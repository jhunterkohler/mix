SHELL := bash
CARGO := cargo
RUSTUP := rustup

.PHONY: \
	clean \
	install-tools \
	test \
	coverage \
	coverage-html

# Clean project.
clean:
	$(CARGO) clean
	$(CARGO)

# Install project tools.
install-tools:
	$(CARGO) install cargo-llvm-cov
	$(RUSTUP) component add llvm-tools-preview

# Run tests.
test:
	$(CARGO) test --all-features --workspace

# Run tests with coverage, print summary to terminal.
coverage:
	$(CARGO) llvm-cov --all-features --workspace

# Run tests with coverage, open HTML summary.
coverage-html:
	$(CARGO) llvm-cov --all-features --workspace --html
	$(CARGO) llvm-cov report --html --open
