#!/bin/bash
# Build and serve the Crystallographic Restriction Theorem blueprint locally
# Usage: ./scripts/build_blueprint.sh
#
# This script:
# 1. Builds and pushes changes to LeanArchitect fork
# 2. Builds and pushes changes to leanblueprint fork
# 3. Updates this project's dependencies and fetches caches
# 4. Builds the Lean project and blueprint
# 5. Serves the blueprint locally

set -e

cd "$(dirname "$0")/.."
PROJECT_ROOT=$(pwd)

# Configuration - paths to forked repos
LEAN_ARCHITECT_PATH="/Users/eric/GitHub/LeanArchitect"
LEANBLUEPRINT_PATH="/Users/eric/GitHub/leanblueprint"

# Add pipx leanblueprint venv to PATH for plastex
# Use explicit path expansion in case $HOME is not set
PIPX_VENV="${HOME:-/Users/eric}/.local/pipx/venvs/leanblueprint/bin"
if [[ -d "$PIPX_VENV" ]]; then
    export PATH="$PIPX_VENV:$PATH"
fi

echo "=== Crystallographic Restriction Theorem Blueprint Builder ==="
echo ""

# Clean all build artifacts to ensure fresh build
echo "=== Cleaning all build artifacts ==="

# Clean blueprint output directories
rm -rf "$PROJECT_ROOT/blueprint/web"
rm -rf "$PROJECT_ROOT/blueprint/print"
echo "Cleaned blueprint/web and blueprint/print"

# Clean LeanArchitect blueprint output
rm -rf "$PROJECT_ROOT/.lake/build/blueprint"
rm -rf "$PROJECT_ROOT/.lake/build/dressed"
echo "Cleaned .lake/build/blueprint and .lake/build/dressed"

# Ensure leanblueprint is installed from local fork (editable mode picks up changes automatically)
if [[ -d "$LEANBLUEPRINT_PATH" ]]; then
    if ! pip show leanblueprint 2>/dev/null | grep -q "Editable project location.*$LEANBLUEPRINT_PATH"; then
        echo "Installing leanblueprint from local fork (editable)..."
        pipx uninstall leanblueprint 2>/dev/null || true
        pipx install -e "$LEANBLUEPRINT_PATH"
    else
        echo "leanblueprint already installed from local fork (editable)"
    fi
fi

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
check_dependency "gh" "Install with: brew install gh"

# Check for xelatex (required by latexmkrc)
if ! command -v xelatex &> /dev/null; then
    echo "WARNING: xelatex is not installed. PDF generation may fail."
    echo "Install a TeX distribution (e.g., MacTeX or TeX Live)."
fi

# Function to commit and push changes in a git repo
push_repo_changes() {
    local repo_path="$1"
    local repo_name="$2"

    echo ""
    echo "=== Checking $repo_name for changes ==="
    cd "$repo_path"

    if [[ -n $(git status --porcelain) ]]; then
        echo "Found uncommitted changes in $repo_name"
        git add -A
        git status --short

        # Auto-commit with timestamp
        local commit_msg="Auto-commit from build_blueprint.sh at $(date '+%Y-%m-%d %H:%M:%S')"
        git commit -m "$commit_msg" || true
    fi

    # Check if we need to push
    local upstream=$(git rev-parse --abbrev-ref --symbolic-full-name @{u} 2>/dev/null || echo "")
    if [[ -n "$upstream" ]]; then
        local local_hash=$(git rev-parse HEAD)
        local remote_hash=$(git rev-parse @{u} 2>/dev/null || echo "")

        if [[ "$local_hash" != "$remote_hash" ]]; then
            echo "Pushing changes to remote..."
            git push
        else
            echo "No new commits to push"
        fi
    else
        echo "No upstream configured, skipping push"
    fi

    cd "$PROJECT_ROOT"
}

# Function to build a Lean project
build_lean_project() {
    local repo_path="$1"
    local repo_name="$2"

    echo ""
    echo "=== Building $repo_name ==="
    cd "$repo_path"
    lake build
    cd "$PROJECT_ROOT"
}

echo ""
echo "=== Step 0: Building and pushing dependency repositories ==="

# Build LeanArchitect first (it's a dependency)
if [[ -d "$LEAN_ARCHITECT_PATH" ]]; then
    build_lean_project "$LEAN_ARCHITECT_PATH" "LeanArchitect"
    push_repo_changes "$LEAN_ARCHITECT_PATH" "LeanArchitect"
else
    echo "WARNING: LeanArchitect path not found at $LEAN_ARCHITECT_PATH"
    echo "Skipping LeanArchitect build/push"
fi

# Push leanblueprint changes (Python, no build needed)
if [[ -d "$LEANBLUEPRINT_PATH" ]]; then
    push_repo_changes "$LEANBLUEPRINT_PATH" "leanblueprint"
else
    echo "WARNING: leanblueprint path not found at $LEANBLUEPRINT_PATH"
    echo "Skipping leanblueprint push"
fi

echo ""
echo "=== Step 1: Updating dependencies and fetching caches ==="
cd "$PROJECT_ROOT"

# Update lake dependencies (explicitly update LeanArchitect to pick up local changes)
echo "Updating lake dependencies..."
lake update LeanArchitect
lake update

# Build Architect library and extract_blueprint executable
# (lake update handles dependency changes, no need to clean)
echo "Building Architect library and extract_blueprint..."
lake build Architect extract_blueprint

# Fetch mathlib cache
echo "Fetching mathlib cache..."
lake exe cache get || echo "Cache fetch completed (some files may have been skipped)"

echo ""
echo "=== Step 2: Building Lean project with dressed artifacts ==="
# BLUEPRINT_DRESS=1 enables automatic export of dressed artifacts to .lake/build/dressed/
# and .tex files to .lake/build/blueprint/module/ for all @[blueprint] declarations
BLUEPRINT_DRESS=1 lake build

echo ""
echo "=== Step 3: Building LeanArchitect blueprint data ==="
# Reads pre-generated dressed JSON from .lake/build/dressed/ (no re-elaboration needed)
# Skips module .tex generation since files already exist from Step 2
lake build :blueprint

# echo ""
# echo "=== Step 4: Pushing main project changes ==="
# push_repo_changes "$PROJECT_ROOT" "General_Crystallographic_Restriction"

echo ""
echo "=== Step 5: Building blueprint (PDF and web) ==="
cd blueprint
# Use pdf and web separately instead of 'all' to skip checkdecls
# (checkdecls requires extra dependency and is redundant when using LeanArchitect)
leanblueprint pdf
leanblueprint web

echo ""
echo "=== Step 6: Launching local server ==="
echo ""
echo "Blueprint is ready!"
echo "  - PDF: blueprint/print/print.pdf"
echo "  - Web: http://localhost:8000"
echo ""
echo "Press Ctrl+C to stop the server."
echo ""

# Open browser after a short delay (in background)
(open "http://localhost:8000") &

leanblueprint serve
