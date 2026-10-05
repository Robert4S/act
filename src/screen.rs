//! Truecolour half-block framebuffer exposed to act programs as intrinsics.
//!
//! Each terminal cell shows two vertically stacked pixels using `▀` with separate foreground and
//! background colours, so pixels are roughly square. Two buffers (selected by frame parity) let
//! an out-of-order producer start on frame N+1 while stragglers of frame N are still arriving.

use std::{
    fmt::Write as _,
    io::Write as _,
    sync::Mutex,
    thread,
    time::{Duration, Instant},
};

use crate::runtimelib::{
    gc::{unmask_integer, Gc},
    runtime::RT,
};

const ENTER: &str = "\x1b[?1049h\x1b[?25l\x1b[2J";
const LEAVE: &str = "\x1b[0m\x1b[?25h\x1b[?1049l";
const MAX_FPS: f64 = 60.0;

type Rgb = (f32, f32, f32);

#[derive(Clone, Copy)]
struct Pixel {
    depth: f32,
    lum: f32,
    face: f32,
}

const EMPTY: Pixel = Pixel {
    depth: 0.0,
    lum: 0.0,
    face: 0.0,
};

/// Per-sample attributes set by `screen_brush` and consumed by the next `screen_plot`.
struct Brush {
    size: f32,
    face: f32,
}

struct Screen {
    w: usize,
    h: usize,
    brush: Brush,
    buffers: [Vec<Pixel>; 2],
    image: Vec<Rgb>,
    emission: Vec<Rgb>,
    scratch: Vec<Rgb>,
    out: String,
    started: Instant,
    last_present: Instant,
    fps: f64,
}

static SCREEN: Mutex<Option<Screen>> = Mutex::new(None);

extern "C" {
    fn signal(signum: i32, handler: extern "C" fn(i32)) -> usize;
    fn write(fd: i32, buf: *const u8, count: usize) -> isize;
    fn _exit(status: i32) -> !;
    fn ioctl(fd: i32, request: u64, ...) -> i32;
}

const SIGINT: i32 = 2;
const SIGTERM: i32 = 15;

#[cfg(target_os = "macos")]
const TIOCGWINSZ: u64 = 0x40087468;
#[cfg(not(target_os = "macos"))]
const TIOCGWINSZ: u64 = 0x5413;

#[repr(C)]
#[derive(Default)]
struct WinSize {
    rows: u16,
    cols: u16,
    xpixel: u16,
    ypixel: u16,
}

extern "C" fn restore_and_exit(_sig: i32) {
    unsafe {
        write(1, LEAVE.as_ptr(), LEAVE.len());
        _exit(130);
    }
}

fn terminal_size() -> (usize, usize) {
    let mut ws = WinSize::default();
    let ok = unsafe { ioctl(1, TIOCGWINSZ, &mut ws as *mut WinSize) } == 0;
    if ok && ws.cols > 0 && ws.rows > 0 {
        (ws.cols as usize, ws.rows as usize)
    } else {
        (80, 24)
    }
}

unsafe fn read_float(g: Gc) -> f32 {
    g.ptr::<f64>().read() as f32
}

fn lerp(a: Rgb, b: Rgb, t: f32) -> Rgb {
    (
        a.0 + (b.0 - a.0) * t,
        a.1 + (b.1 - a.1) * t,
        a.2 + (b.2 - a.2) * t,
    )
}

fn ramp(stops: &[Rgb], t: f32) -> Rgb {
    let t = t.clamp(0.0, 1.0) * (stops.len() - 1) as f32;
    let i = (t.floor() as usize).min(stops.len() - 2);
    lerp(stops[i], stops[i + 1], t - i as f32)
}

const SURFACE: [Rgb; 7] = [
    (14.0, 5.0, 38.0),
    (52.0, 9.0, 112.0),
    (120.0, 14.0, 168.0),
    (196.0, 24.0, 150.0),
    (247.0, 52.0, 110.0),
    (255.0, 140.0, 30.0),
    (255.0, 222.0, 140.0),
];
const RIM: Rgb = (40.0, 230.0, 255.0);

fn background(x: usize, y: usize, w: usize, h: usize) -> Rgb {
    let fy = y as f32 / h as f32;
    let dx = x as f32 / w as f32 - 0.5;
    let dy = fy - 0.45;
    let glow = (1.0 - (dx * dx + dy * dy).sqrt() * 1.6).max(0.0);
    let base = lerp((10.0, 6.0, 26.0), (4.0, 2.0, 10.0), fy);
    lerp(base, (48.0, 16.0, 72.0), glow * glow * 0.6)
}

fn shade(p: Pixel, bg: Rgb) -> Rgb {
    let wrap = (p.lum * 0.5 + 0.5).powf(1.7);
    let mut c = ramp(&SURFACE, wrap);
    // `face` is the normal's z: -1 faces the camera, 0 is a silhouette edge.
    let rim = (1.0 + p.face).clamp(0.0, 1.0).powi(3) * (1.0 - wrap * 0.6);
    c = lerp(c, RIM, rim * 0.55);
    let spec = p.lum.max(0.0).powi(18);
    c = lerp(c, (255.0, 250.0, 240.0), spec * 0.8);
    // Depth is 1/z; only the far side of the torus (z beyond 6) fades into the backdrop.
    let fog = ((0.17 - p.depth) * 9.0).clamp(0.0, 0.5);
    lerp(c, bg, fog)
}

const GLOW_RADIUS: usize = 4;
const GLOW_STRENGTH: f32 = 0.22;

/// One direction of a box blur over a `w * h` image.
fn box_pass(src: &[Rgb], dst: &mut [Rgb], w: usize, h: usize, horizontal: bool) {
    let r = GLOW_RADIUS as i64;
    let norm = 1.0 / (2 * r + 1) as f32;
    for y in 0..h as i64 {
        for x in 0..w as i64 {
            let mut acc = (0.0, 0.0, 0.0);
            for d in -r..=r {
                let (sx, sy) = if horizontal { (x + d, y) } else { (x, y + d) };
                if sx >= 0 && sy >= 0 && sx < w as i64 && sy < h as i64 {
                    let c = src[sy as usize * w + sx as usize];
                    acc = (acc.0 + c.0, acc.1 + c.1, acc.2 + c.2);
                }
            }
            dst[y as usize * w + x as usize] = (acc.0 * norm, acc.1 * norm, acc.2 * norm);
        }
    }
}

impl Screen {
    fn new(w: usize, h: usize) -> Self {
        Self {
            w,
            h,
            brush: Brush {
                size: 2.0,
                face: 0.0,
            },
            buffers: [vec![EMPTY; w * h], vec![EMPTY; w * h]],
            image: vec![(0.0, 0.0, 0.0); w * h],
            emission: vec![(0.0, 0.0, 0.0); w * h],
            scratch: vec![(0.0, 0.0, 0.0); w * h],
            out: String::with_capacity(w * h * 24),
            started: Instant::now(),
            last_present: Instant::now(),
            fps: 0.0,
        }
    }

    fn plot(&mut self, parity: usize, x: f32, y: f32, depth: f32, lum: f32) {
        let (w, h) = (self.w as i64, self.h as i64);
        let face = self.brush.face;
        // Half a pixel of overlap so rounding the splat origin never opens a seam.
        let n = (self.brush.size + 0.5).ceil().clamp(1.0, 5.0);
        let (x0, y0) = ((x - n * 0.5).round() as i64, (y - n * 0.5).round() as i64);
        let n = n as i64;
        let buf = &mut self.buffers[parity];
        for py in y0.max(0)..(y0 + n).min(h) {
            for px in x0.max(0)..(x0 + n).min(w) {
                let slot = &mut buf[(py * w + px) as usize];
                if depth > slot.depth {
                    *slot = Pixel { depth, lum, face };
                }
            }
        }
    }

    fn present(&mut self, parity: usize, frame: i64) {
        let elapsed = self.last_present.elapsed().as_secs_f64();
        let budget = 1.0 / MAX_FPS;
        if elapsed < budget {
            thread::sleep(Duration::from_secs_f64(budget - elapsed));
        }
        let dt = self.last_present.elapsed().as_secs_f64().max(1e-6);
        self.last_present = Instant::now();
        self.fps = if self.fps == 0.0 {
            1.0 / dt
        } else {
            self.fps * 0.9 + 0.1 / dt
        };

        let (w, h) = (self.w, self.h);
        let buf = &self.buffers[parity];
        for (i, p) in buf.iter().enumerate() {
            let bg = background(i % w, i / w, w, h);
            if p.depth > 0.0 {
                let c = shade(*p, bg);
                self.image[i] = c;
                self.emission[i] = c;
            } else {
                self.image[i] = bg;
                self.emission[i] = (0.0, 0.0, 0.0);
            }
        }
        box_pass(&self.emission, &mut self.scratch, w, h, true);
        box_pass(&self.scratch, &mut self.emission, w, h, false);
        for (i, p) in buf.iter().enumerate() {
            if p.depth == 0.0 {
                let (c, g) = (self.image[i], self.emission[i]);
                self.image[i] = (
                    (c.0 + g.0 * GLOW_STRENGTH).min(255.0),
                    (c.1 + g.1 * GLOW_STRENGTH).min(255.0),
                    (c.2 + g.2 * GLOW_STRENGTH).min(255.0),
                );
            }
        }

        let out = &mut self.out;
        out.clear();
        out.push_str("\x1b[H");
        let mut last: Option<((u8, u8, u8), (u8, u8, u8))> = None;
        let image = &self.image;
        for row in (0..h).step_by(2) {
            for x in 0..w {
                let colour = |y: usize| {
                    let c = if y < h {
                        image[y * w + x]
                    } else {
                        background(x, y, w, h)
                    };
                    (c.0 as u8, c.1 as u8, c.2 as u8)
                };
                let (top, bottom) = (colour(row), colour(row + 1));
                if last.map(|(t, _)| t) != Some(top) {
                    let _ = write!(out, "\x1b[38;2;{};{};{}m", top.0, top.1, top.2);
                }
                if last.map(|(_, b)| b) != Some(bottom) {
                    let _ = write!(out, "\x1b[48;2;{};{};{}m", bottom.0, bottom.1, bottom.2);
                }
                last = Some((top, bottom));
                out.push('▀');
            }
            out.push_str("\x1b[0m\r\n");
            last = None;
        }
        let secs = self.started.elapsed().as_secs_f64();
        let _ = write!(
            out,
            "\x1b[38;2;181;23;158m ◆ act\x1b[38;2;120;110;150m  six-stage actor pipeline  \
             \x1b[38;2;255;158;0mframe {frame:>6}\x1b[38;2;120;110;150m  ·  \
             \x1b[38;2;255;238;170m{:>5.1} fps\x1b[38;2;120;110;150m  ·  {secs:>6.1}s  ·  ctrl-c to quit\x1b[0m\x1b[K",
            self.fps
        );

        let mut stdout = std::io::stdout().lock();
        let _ = stdout.write_all(out.as_bytes());
        let _ = stdout.flush();

        self.buffers[parity].fill(EMPTY);
    }
}

/// Opens the alternate screen sized to the terminal and writes the pixel dimensions into the
/// two given boxed floats.
#[no_mangle]
pub unsafe extern "C" fn screen_open(_rt: &RT, width_out: Gc, height_out: Gc) {
    let (cols, rows) = terminal_size();
    let w = cols.clamp(20, 160);
    let h = (rows.saturating_sub(2) * 2).clamp(16, 120);
    width_out.ptr::<f64>().write(w as f64);
    height_out.ptr::<f64>().write(h as f64);

    signal(SIGINT, restore_and_exit);
    signal(SIGTERM, restore_and_exit);

    let mut stdout = std::io::stdout().lock();
    let _ = stdout.write_all(ENTER.as_bytes());
    let _ = stdout.flush();
    *SCREEN.lock().unwrap() = Some(Screen::new(w, h));
}

/// Sets the splat size (in pixels) and facing ratio used by subsequent plots.
#[no_mangle]
pub unsafe extern "C" fn screen_brush(_rt: &RT, size: Gc, face: Gc) {
    if let Some(s) = SCREEN.lock().unwrap().as_mut() {
        s.brush = Brush {
            size: read_float(size),
            face: read_float(face),
        };
    }
}

#[no_mangle]
pub unsafe extern "C" fn screen_plot(_rt: &RT, parity: Gc, x: Gc, y: Gc, depth: Gc, lum: Gc) {
    if let Some(s) = SCREEN.lock().unwrap().as_mut() {
        let parity = (unmask_integer(parity) & 1) as usize;
        s.plot(
            parity,
            read_float(x),
            read_float(y),
            read_float(depth),
            read_float(lum),
        );
    }
}

#[no_mangle]
pub unsafe extern "C" fn screen_present(_rt: &RT, parity: Gc, frame: Gc) {
    if let Some(s) = SCREEN.lock().unwrap().as_mut() {
        s.present((unmask_integer(parity) & 1) as usize, unmask_integer(frame));
    }
}

#[no_mangle]
pub unsafe extern "C" fn screen_close(_rt: &RT, _unused: Gc) {
    if SCREEN.lock().unwrap().take().is_some() {
        let mut stdout = std::io::stdout().lock();
        let _ = stdout.write_all(LEAVE.as_bytes());
        let _ = stdout.flush();
    }
}
