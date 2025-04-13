function test_prog
	cargo build --release
	cp ./target/release/libactrt.a /home/robert/.local/lib/
	gcc -nostartfiles -o testing test.S /home/robert/.local/lib/libactrt.a
end
