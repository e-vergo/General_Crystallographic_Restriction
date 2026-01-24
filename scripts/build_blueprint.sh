#!/bin/bash
# Build and serve the Crystallographic Restriction Theorem blueprint locally
# Usage: ./scripts/build_blueprint.sh
#
# This script:
# 1. Builds all four local dependency forks (SubVerso, LeanArchitect, Dress, leanblueprint)
# 2. Builds the Lean project with dressed artifacts
# 3. Builds the blueprint (web only - PDF skipped)
# 4. Serves the blueprint locally
#
# All dependencies use local paths, so no git push/pull is needed.

set -e

cd "$(dirname "$0")/.."
PROJECT_ROOT=$(pwd)

# Configuration - paths to local dependency forks
SUBVERSO_PATH="/Users/eric/Github/subverso"
LEAN_ARCHITECT_PATH="/Users/eric/Github/LeanArchitect"
DRESS_PATH="/Users/eric/Github/Dress"
LEANBLUEPRINT_PATH="/Users/eric/Github/leanblueprint"

# Create/activate a local venv for leanblueprint
VENV_PATH="$PROJECT_ROOT/.venv"
if [[ ! -d "$VENV_PATH" ]]; then
    echo "Creating virtual environment..."
    python3 -m venv "$VENV_PATH"
fi
source "$VENV_PATH/bin/activate"

echo "=== Crystallographic Restriction Theorem Blueprint Builder ==="
echo ""

# Clean build artifacts
echo "=== Cleaning build artifacts ==="
rm -rf "$PROJECT_ROOT/blueprint/web"
rm -rf "$PROJECT_ROOT/blueprint/src/web"
rm -rf "$PROJECT_ROOT/.lake/build/blueprint"
rm -rf "$PROJECT_ROOT/.lake/build/dressed"
echo "Cleaned blueprint output directories"

# Ensure leanblueprint is installed from local fork (editable mode)
if [[ ! -d "$LEANBLUEPRINT_PATH" ]]; then
    echo "ERROR: leanblueprint not found at $LEANBLUEPRINT_PATH"
    exit 1
fi
echo "Installing leanblueprint from local fork (editable)..."
pip install -e "$LEANBLUEPRINT_PATH" -q

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
check_dependency "leanblueprint" "Install with: pip install -e $LEANBLUEPRINT_PATH"

echo ""
echo "=== Step 1: Building local dependency forks ==="

# Build order: SubVerso -> LeanArchitect -> Dress (respects dependency chain)

if [[ -d "$SUBVERSO_PATH" ]]; then
    echo "Building SubVerso..."
    (cd "$SUBVERSO_PATH" && lake build)
else
    echo "ERROR: SubVerso not found at $SUBVERSO_PATH"
    exit 1
fi

if [[ -d "$LEAN_ARCHITECT_PATH" ]]; then
    echo "Building LeanArchitect..."
    (cd "$LEAN_ARCHITECT_PATH" && lake build)
else
    echo "ERROR: LeanArchitect not found at $LEAN_ARCHITECT_PATH"
    exit 1
fi

if [[ -d "$DRESS_PATH" ]]; then
    echo "Building Dress..."
    (cd "$DRESS_PATH" && lake build)
else
    echo "ERROR: Dress not found at $DRESS_PATH"
    exit 1
fi

# leanblueprint is Python - already handled via pipx editable install above

echo ""
echo "=== Step 2: Fetching mathlib cache ==="
cd "$PROJECT_ROOT"
# Note: No `lake update` needed - local path dependencies are resolved directly.
# Running `lake update` can corrupt the manifest when mixing local/git deps.
lake exe cache get || echo "Cache fetch completed (some files may have been skipped)"

echo ""
echo "=== Step 3: Building Lean project with dressed artifacts ==="
# Use BLUEPRINT_DRESS=1 environment variable to enable dressed artifact generation.
# Dress's ElabRules.lean checks this env var to generate per-declaration artifacts
# during elaboration. This is more reliable than the marker file approach.
#
# Must clean build artifacts to force re-elaboration (cached oleans skip elab_rules).
# Clean oleans, IR files, and dressed artifacts - Lake uses multiple caching mechanisms.
# Without this, `lake build` uses cached oleans and the elab_rules that generate
# per-declaration artifacts won't run.
rm -rf "$PROJECT_ROOT/.lake/build/lib/Crystallographic"
rm -rf "$PROJECT_ROOT/.lake/build/ir/Crystallographic"
rm -rf "$PROJECT_ROOT/.lake/build/dressed"

BLUEPRINT_DRESS=1 lake build

echo ""
echo "=== Step 4: Building blueprint facet ==="
lake build :blueprint

echo ""
echo "=== Step 5: Building blueprint (web only) ==="
cd blueprint
leanblueprint web

echo ""
echo "=== Blueprint ready ==="
echo "  Web: http://localhost:8000"
echo ""
echo "Press Ctrl+C to stop the server."

(open "http://localhost:8000") &
leanblueprint serve
