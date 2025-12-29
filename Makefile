# Lambda Calculus in Lean 4
# Use with: nix-shell --run "make <target>"

.PHONY: all build test clean repl check update-deps

# Default target
all: build

# Build the project
build:
	lake build

# Run tests (builds and checks all proofs)
test: build
	@echo "All proofs verified successfully!"

# Type-check without full build
check:
	lake build LambdaCalc

# Clean build artifacts
clean:
	lake clean
	rm -rf .lake

# Start Lean REPL with project loaded
lean-repl:
	lake env lean

# Start Lambda Calculus REPL
repl: build
	.lake/build/bin/lambdacalc_repl

# Update Lake dependencies
update-deps:
	lake update

# Build with verbose output
build-verbose:
	lake build -v

# Show project info
info:
	@echo "Project: Lambda Calculus in Lean 4"
	@echo "Structure:"
	@echo "  LambdaCalc/Basic.lean  - Core implementation"
	@echo "  LambdaCalc/Proofs.lean - Formal proofs"
	@echo "  LambdaCalc/Tests.lean  - Tests and examples"
	@echo "  LambdaCalc/REPL.lean   - Interactive REPL"
	@echo ""
	@echo "Usage:"
	@echo "  nix-shell              - Enter development shell"
	@echo "  nix-shell --run 'make' - Build the project"

# Help target
help:
	@echo "Available targets:"
	@echo "  make build        - Build the project"
	@echo "  make test         - Build and verify all proofs"
	@echo "  make check        - Type-check the project"
	@echo "  make clean        - Remove build artifacts"
	@echo "  make repl         - Start Lambda Calculus REPL"
	@echo "  make lean-repl    - Start Lean REPL"
	@echo "  make update-deps  - Update Lake dependencies"
	@echo "  make info         - Show project information"
	@echo ""
	@echo "Use with nix-shell:"
	@echo "  nix-shell --run 'make build'"
