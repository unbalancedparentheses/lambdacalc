{ pkgs ? import <nixpkgs> {} }:

pkgs.mkShell {
  buildInputs = with pkgs; [
    elan      # Lean version manager (installs lean4 + lake)
    gnumake
  ];

  shellHook = ''
    echo "Lean 4 Lambda Calculus development environment"
    echo ""
    echo "Available commands:"
    echo "  make build   - Build the project"
    echo "  make test    - Run tests"
    echo "  make clean   - Clean build artifacts"
    echo "  make repl    - Start Lean REPL"
    echo ""

    # Ensure elan has the toolchain ready
    if [ -f lean-toolchain ]; then
      elan show
    fi
  '';
}
