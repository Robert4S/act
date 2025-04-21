fn main() {
    let summed = sum(10000.);
    println!("sum: {summed}");
    let sum_recursive = sum_recursive(10000.);
    println!("recursive sum: {sum_recursive}");
}

fn sum(num: f64) -> f64 {
    let mut acc = 0.;
    let mut arg = num;

    while arg > 0. {
        acc += arg;
        arg = arg - 1.;
    }

    acc
}

fn sum_recursive(num: f64) -> f64 {
    if num <= 0. {
        return num;
    }

    return num + sum_recursive(num - 1.);
}
