.PHONY: all check fix clippy test

all: check test

check: fix clippy

fix:
	cargo fmt && cargo fix --allow-dirty --allow-staged

clippy:
	find . -name '*.rs' | xargs touch && cargo clippy --all-features --all-targets

test:
	RUST_BACKTRACE=1 cargo test
