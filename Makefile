.PHONY: all check fix clippy test clean

all: fix clippy test

fix: check
	cargo fmt && cargo fix --allow-dirty --allow-staged

clippy: check
	find . -name '*.rs' | xargs touch && cargo clippy --all-features --all-targets

check:
	cargo check

test: check
	RUST_BACKTRACE=1 cargo test

clean:
	cargo clean
