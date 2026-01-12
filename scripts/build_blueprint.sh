#!/bin/bash
# Build and serve the Crystallographic Restriction Theorem blueprint locally
# Usage: ./scripts/build_blueprint.sh

set -e

cd "$(dirname "$0")/.."
PROJECT_ROOT=$(pwd)

# Add pipx leanblueprint venv to PATH for plastex
export PATH="$HOME/.local/pipx/venvs/leanblueprint/bin:$PATH"

echo "=== Crystallographic Restriction Theorem Blueprint Builder ==="
echo ""

# Check dependencies
check_dependency() {
    if ! command -v "$1" &> /dev/null; then
        echo "ERROR: $1 is not installed."
        echo "$2"
        exit 1
    fi
}

check_dependency "lake" "Please install Lean 4 and Lake."
check_dependency "leanblueprint" "Install with: pipx install leanblueprint"

# Check for xelatex (required by latexmkrc)
if ! command -v xelatex &> /dev/null; then
    echo "WARNING: xelatex is not installed. PDF generation may fail."
    echo "Install a TeX distribution (e.g., MacTeX or TeX Live)."
fi

echo "=== Step 1: Building Lean project ==="
lake build

echo ""
echo "=== Step 2: Building LeanArchitect blueprint data ==="
lake build :blueprint

echo ""
echo "=== Step 3: Building blueprint (PDF and web) ==="
cd blueprint
# Use pdf and web separately instead of 'all' to skip checkdecls
# (checkdecls requires extra dependency and is redundant when using LeanArchitect)
leanblueprint pdf
leanblueprint web

echo ""
echo "=== Step 4: Launching local server ==="
echo ""
echo "Blueprint is ready!"
echo "  - PDF: blueprint/print/print.pdf"
echo "  - Web: http://localhost:8000"
echo ""
echo "Press Ctrl+C to stop the server."
echo ""

# Open browser after a short delay (in background)
(sleep 2 && open "http://localhost:8000") &

leanblueprint serve