.PHONY: all fix clippy

all: fix clippy

fix:
	cargo fmt && cargo fix --allow-dirty --allow-staged

clippy:
	find . -name '*.rs' | xargs touch && cargo clippy --all-features --all-targets

