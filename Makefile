.PHONY: all check fix clippy test clean bench build help memtest print-type-sizes

all: fix clippy memtest

fix: check
	cargo fmt && cargo fix --allow-dirty --allow-staged

clippy: check
	find . -name '*.rs' | xargs touch && cargo clippy --all-features --all-targets

check:
	cargo check

test: check
	RUST_BACKTRACE=1 cargo test

memtest:
	RUSTFLAGS="-Z sanitizer=leak" cargo +nightly run  --example memory_test
	RUSTFLAGS="-Z sanitizer=leak" cargo +nightly test

clean:
	cargo clean

bench:
	cargo bench

build:
	cargo build --all-targets

print-type-sizes:
	find . -name '*.rs' | xargs touch && cargo +nightly rustc --release --lib -- -Z print-type-sizes

help:
	@grep '^[^#[:space:]].*:' Makefile
