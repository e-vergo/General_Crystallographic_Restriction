#!/bin/bash
# Build and serve the General Crystallographic Restriction blueprint locally
# Usage: ./scripts/build_blueprint.sh
#
# This script uses the pure Lean blueprint pipeline (no Python/plasTeX):
#   1. Builds local dependency forks (SubVerso, LeanArchitect, Dress, Runway)
#   2. Fetches mathlib cache
#   3. Builds Lean project with BLUEPRINT_DRESS=1 (generates per-declaration artifacts)
#   4. Builds :blueprint Lake facet
#   5. Generates dependency graph via Dress extract_blueprint
#   6. Generates static site via Runway (reads dressed artifacts + runway.json)
#   7. Serves site locally at http://localhost:8000
#
# Configuration:
#   - runway.json: Site config (title, URLs, blueprintTexPath for chapter structure)
#   - blueprint/src/blueprint.tex: Chapter organization and prose content
#
# All dependencies use local paths for development. No git push/pull needed.

set -e

cd "$(dirname "$0")/.."
PROJECT_ROOT=$(pwd)

# Configuration - paths to local dependency forks
SUBVERSO_PATH="/Users/eric/GitHub/Side-By-Side-Blueprint/subverso"
LEAN_ARCHITECT_PATH="/Users/eric/GitHub/Side-By-Side-Blueprint/LeanArchitect"
DRESS_PATH="/Users/eric/GitHub/Side-By-Side-Blueprint/Dress"
RUNWAY_PATH="/Users/eric/GitHub/Side-By-Side-Blueprint/Runway"
DRESS_BLUEPRINT_ACTION_PATH="/Users/eric/GitHub/Side-By-Side-Blueprint/dress-blueprint-action"

echo "=== General Crystallographic Restriction Blueprint Builder ==="
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

# Verify local paths exist
for path in "$SUBVERSO_PATH" "$LEAN_ARCHITECT_PATH" "$DRESS_PATH" "$RUNWAY_PATH" "$DRESS_BLUEPRINT_ACTION_PATH"; do
    if [[ ! -d "$path" ]]; then
        echo "ERROR: Dependency not found at $path"
        exit 1
    fi
done

# Kill any existing processes on port 8000
echo "Killing any existing servers on port 8000..."
lsof -ti:8000 | xargs kill -9 2>/dev/null || true

echo ""
echo "=== Step 0: Syncing local repos to GitHub ==="

# Function to commit and push a repo if it has changes
sync_repo() {
    local repo_path="$1"
    local repo_name=$(basename "$repo_path")

    echo "Checking $repo_name..."
    cd "$repo_path"

    # Check for uncommitted changes (staged or unstaged)
    if [[ -n $(git status --porcelain) ]]; then
        echo "  Committing changes in $repo_name..."
        git add -A
        git commit -m "Auto-commit from build_blueprint.sh"
        echo "  Pushing $repo_name to GitHub..."
        git push
    else
        echo "  No changes in $repo_name"
    fi

    cd "$PROJECT_ROOT"
}

# Sync repos in dependency order (upstream first, then this project)
sync_repo "$SUBVERSO_PATH"
sync_repo "$LEAN_ARCHITECT_PATH"
sync_repo "$DRESS_PATH"
sync_repo "$RUNWAY_PATH"
sync_repo "$PROJECT_ROOT"

echo ""
echo "=== Step 0b: Updating lake manifests ==="

# Update LeanArchitect's SubVerso dependency
echo "Updating LeanArchitect dependencies..."
(cd "$LEAN_ARCHITECT_PATH" && lake update SubVerso 2>/dev/null || true)

# Update Dress's LeanArchitect dependency
echo "Updating Dress dependencies..."
(cd "$DRESS_PATH" && lake update LeanArchitect 2>/dev/null || true)

# Update Runway's Dress dependency
echo "Updating Runway dependencies..."
(cd "$RUNWAY_PATH" && lake update Dress 2>/dev/null || true)

# Update GCR's Dress dependency
echo "Updating project dependencies..."
(cd "$PROJECT_ROOT" && lake update Dress 2>/dev/null || true)

# Commit and push any manifest changes
for repo_path in "$LEAN_ARCHITECT_PATH" "$DRESS_PATH" "$RUNWAY_PATH"; do
    repo_name=$(basename "$repo_path")
    cd "$repo_path"
    if [[ -n $(git status --porcelain lake-manifest.json 2>/dev/null) ]]; then
        echo "  Committing manifest update in $repo_name..."
        git add lake-manifest.json
        git commit -m "Update lake-manifest.json from build_blueprint.sh"
        git push
    fi
    cd "$PROJECT_ROOT"
done

# Commit and push GCR manifest if changed
if [[ -n $(git status --porcelain lake-manifest.json 2>/dev/null) ]]; then
    echo "  Committing manifest update in project..."
    git add lake-manifest.json
    git commit -m "Update lake-manifest.json from build_blueprint.sh"
    git push
fi

echo ""
echo "=== Step 1: Building local dependency forks ==="

# Build order: SubVerso -> LeanArchitect -> Dress -> Runway (respects dependency chain)

echo "Building SubVerso..."
(cd "$SUBVERSO_PATH" && lake build)

echo "Building LeanArchitect..."
(cd "$LEAN_ARCHITECT_PATH" && lake build)

echo "Building Dress..."
(cd "$DRESS_PATH" && lake build)

echo "Building Runway..."
(cd "$RUNWAY_PATH" && lake build)

echo ""
echo "=== Step 2: Fetching mathlib cache ==="
cd "$PROJECT_ROOT"
lake exe cache get || echo "Cache fetch completed (some files may have been skipped)"

echo ""
echo "=== Step 3: Building Lean project with dressed artifacts ==="
# Use BLUEPRINT_DRESS=1 environment variable to enable dressed artifact generation.
# Dress's ElabRules.lean checks this env var to generate per-declaration artifacts
# during elaboration.
#
# Clean build artifacts to force re-elaboration (cached oleans skip elab_rules).
rm -rf "$PROJECT_ROOT/.lake/build/lib/Crystallographic"
rm -rf "$PROJECT_ROOT/.lake/build/ir/Crystallographic"
rm -rf "$PROJECT_ROOT/.lake/build/dressed"

BLUEPRINT_DRESS=1 lake build

echo ""
echo "=== Step 4: Building blueprint facet ==="
lake build :blueprint

echo ""
echo "=== Step 5: Generating dependency graph ==="
# Run extract_blueprint graph command from local Dress
# Uses lake env to ensure correct LEAN_PATH for importing project modules
lake env "$DRESS_PATH/.lake/build/bin/extract_blueprint" graph \
    --build "$PROJECT_ROOT/.lake/build" \
    Crystallographic

echo ""
echo "=== Step 6: Generating site with Runway ==="
# Runway reads:
#   - Dress artifacts from .lake/build/dressed/
#   - Configuration from runway.json (includes blueprintTexPath for chapter structure)
# Outputs to .lake/build/runway/
OUTPUT_DIR="$PROJECT_ROOT/.lake/build/runway"
rm -rf "$OUTPUT_DIR"

# Verify runway.json exists
if [[ ! -f "$PROJECT_ROOT/runway.json" ]]; then
    echo "ERROR: runway.json not found. Create it with blueprintTexPath set."
    exit 1
fi

(cd "$RUNWAY_PATH" && lake exe runway \
    --build-dir "$PROJECT_ROOT/.lake/build" \
    --output "$OUTPUT_DIR" \
    build \
    "$PROJECT_ROOT/runway.json")

echo ""
echo "=== Step 7: Generating paper (if configured) ==="
# Check if paperTexPath is configured in runway.json
if grep -q '"paperTexPath"' "$PROJECT_ROOT/runway.json" && ! grep -q '"paperTexPath": null' "$PROJECT_ROOT/runway.json"; then
    (cd "$RUNWAY_PATH" && lake exe runway \
        --build-dir "$PROJECT_ROOT/.lake/build" \
        --output "$OUTPUT_DIR" \
        paper \
        "$PROJECT_ROOT/runway.json")
else
    echo "No paperTexPath configured, skipping paper generation"
fi

echo ""
echo "=== Blueprint ready ==="
echo "  Output: $OUTPUT_DIR"
echo "  Web: http://localhost:8000"
echo ""

# Start server in background
python3 -m http.server -d "$OUTPUT_DIR" 8000 &
SERVER_PID=$!
echo "Server started (PID: $SERVER_PID)"

# Open browser
(sleep 1 && open "http://localhost:8000") &

echo ""
echo "=== BUILD COMPLETE ==="
echo "Server running at http://localhost:8000 (PID: $SERVER_PID)"
echo ""
