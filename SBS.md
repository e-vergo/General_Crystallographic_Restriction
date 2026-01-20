# Side-by-Side Lean Code Display Architecture

This document describes the architecture for displaying Lean source code side-by-side with LaTeX theorem statements in the blueprint HTML output.

## Overview

The feature involves three repositories:

1. **LeanArchitect** (`/Users/eric/GitHub/LeanArchitect`) - Lightweight Lean 4 library that provides the `@[blueprint]` attribute and stores declaration metadata
2. **Dress** (`/Users/eric/GitHub/Dress`) - Lean 4 tool that generates syntax-highlighted artifacts during compilation
3. **leanblueprint** (`/Users/eric/GitHub/leanblueprint`) - Python package that consumes Dress artifacts to produce interactive HTML/PDF

## Architecture

```
┌─────────────────────────────────────────────────────────────────────┐
│                     LEAN PROJECT                                    │
│  import Dress                                                       │
│  @[blueprint "thm:foo"] theorem foo : P → Q := ...                 │
└─────────────────────────────────────────────────────────────────────┘
                              │
                              │ lake build (with .lake/build/.dress marker)
                              ▼
┌─────────────────────────────────────────────────────────────────────┐
│                         DRESS                                       │
│                                                                     │
│  Hook.lean intercepts elaboration of @[blueprint] declarations:     │
│  ├── SubVerso captures semantic highlighting from info trees        │
│  ├── Verso renders HTML with hover tooltips                         │
│  └── Output.lean generates LaTeX with base64-embedded HTML          │
│                                                                     │
│  Artifacts written to:                                              │
│  ├── .lake/build/dressed/{Module/Path}.json (highlighting data)     │
│  └── .lake/build/blueprint/module/{Module/Path}.tex (LaTeX + HTML) │
└─────────────────────────────────────────────────────────────────────┘
                              │
                              │ lake build :blueprint
                              ▼
┌─────────────────────────────────────────────────────────────────────┐
│                 LIBRARY INDEX GENERATION                            │
│                                                                     │
│  extract_blueprint index: Collates module .tex files                │
│  Output: .lake/build/blueprint/library/{Library}.tex                │
└─────────────────────────────────────────────────────────────────────┘
                              │
                              │ leanblueprint pdf / leanblueprint web
                              ▼
┌─────────────────────────────────────────────────────────────────────┐
│                      LEANBLUEPRINT                                  │
│                                                                     │
│  plasTeX parses .tex → extracts base64 HTML from macros:            │
│  ├── \leansourcehtml{base64}      → lean_source_html                │
│  ├── \leansignaturesourcehtml{base64} → lean_signature_html         │
│  ├── \leanproofsourcehtml{base64} → lean_proof_html                 │
│  └── \leanhoverdata{base64}       → lean_hover_data                 │
│                                                                     │
│  Thms.jinja2s renders side-by-side grid layout                      │
│  Errors if Dress artifacts are missing (no fallback rendering)      │
└─────────────────────────────────────────────────────────────────────┘
                              │
                              ▼
┌─────────────────────────────────────────────────────────────────────┐
│                      HTML OUTPUT                                    │
│                                                                     │
│  .sbs-container (CSS grid):                                         │
│  ├── .sbs-latex-column (75ch fixed) - LaTeX theorem                 │
│  └── .sbs-lean-column (flexible) - Lean code with highlighting      │
│       ├── .lean-signature - Highlighted signature                   │
│       └── .lean-proof-body - Collapsible proof (synced with LaTeX)  │
└─────────────────────────────────────────────────────────────────────┘
```

## Key Files

### LeanArchitect

LeanArchitect is a lightweight metadata store with no artifact generation.

| File | Purpose |
|------|---------|
| `Architect/Basic.lean` | `Node`, `NodePart` structures, environment extensions |
| `Architect/Attribute.lean` | `@[blueprint]` attribute syntax and elaboration |
| `Architect/CollectUsed.lean` | Dependency inference from constant values |
| `Architect/Command.lean` | `blueprint_comment` command |
| `Architect/Tactic.lean` | `sorry_using`, `blueprint_using` tactics |

**Dependencies:** Only `batteries` (no SubVerso/Verso)

### Dress

Dress generates all artifacts during Lean elaboration.

| File | Purpose |
|------|---------|
| `Dress/Hook.lean` | Elaboration-time capture via `elab_rules`, marker file detection |
| `Dress/HookState.lean` | IO refs for recursion prevention |
| `Dress/Highlighting.lean` | SubVerso highlighting wrapper |
| `Dress/HtmlRender.lean` | Verso HTML rendering with hover tooltips |
| `Dress/Output.lean` | LaTeX generation with base64-embedded HTML |
| `Dress/Core.lean` | `NodeWithPos` structure, signature/proof splitting |
| `Dress/Load.lean` | Environment loading utilities |
| `Main.lean` | `extract_blueprint` CLI for index generation |
| `lakefile.lean` | Lake facets (`dressed`, `blueprint`), `script dress` |

**Dependencies:** LeanArchitect, SubVerso, Verso, Cli

### leanblueprint

leanblueprint consumes Dress artifacts (no fallback rendering).

| File | Purpose |
|------|---------|
| `Packages/blueprint.py` | plasTeX commands, requires Dress artifacts |
| `Packages/renderer_templates/Thms.jinja2s` | Side-by-side grid layout template |
| `static/blueprint.css` | Layout and syntax highlighting styles |

**Dependencies:** plasTeX, plastexdepgraph

## Elaboration-Time Capture

Dress uses Hook.lean to capture highlighting **during** Lean elaboration, not as a post-processing step.

### Marker File Detection

When `.lake/build/.dress` exists, Hook.lean enables artifact generation:

```lean
-- From Hook.lean
let markerFile : System.FilePath := ".lake" / "build" / ".dress"
let markerExists ← markerFile.pathExists
let dressEnabled := dressEnv == some "1" || blueprint.dress.get (← getOptions) || markerExists
```

### Capture Flow

1. `elab_rules` fire after `@[blueprint]` declaration elaboration
2. Info trees (containing type info for hovers) are captured while still available
3. SubVerso's `highlightIncludingUnparsed` extracts semantic highlighting
4. Verso renders HTML with `data-hover-id` attributes for tooltips
5. Output.lean writes artifacts with base64-encoded HTML

### Code Splitting

`splitAtDefinitionAssign` in `Core.lean` handles splitting code at `:=`:

- Strips `@[blueprint]` prefix
- Finds definition keyword (`def`, `theorem`, `lemma`, etc.)
- Tracks bracket depth to find `:=` at depth 0
- Returns `(signature, proofBody)` for theorems with proofs

## LaTeX Macros

Dress embeds pre-rendered HTML in LaTeX using these macros:

| Macro | Content |
|-------|---------|
| `\leansourcehtml{base64}` | Full highlighted code |
| `\leansignaturesourcehtml{base64}` | Signature up to `:=` |
| `\leanproofsourcehtml{base64}` | Proof body after `:=` |
| `\leanhoverdata{base64}` | Hover tooltip JSON |
| `\leanposition{file\|startLine\|startCol\|endLine\|endCol}` | Source location |

leanblueprint decodes these directly - no SubVerso JSON rendering needed.

## CSS Classes

### Semantic Highlighting (from SubVerso/Verso)

| Class | Element | Color |
|-------|---------|-------|
| `lean-keyword` | `def`, `theorem`, `by`, `fun` | Blue (#0000ff) |
| `lean-const` | Constants and functions | Gold (#AF8700) |
| `lean-var` | Local variables | Cyan-blue (#0070C1) |
| `lean-string` | String literals | Red (#a31515) |
| `lean-docstring` | Doc comments | Green italic (#008000) |
| `lean-sort` | `Type`, `Prop`, `Sort` | Teal (#267f99) |
| `lean-sorry` | `sorry` | Red with pink background |

### Lexical Highlighting (from Dress)

| Class | Element | Color |
|-------|---------|-------|
| `lean-number` | Numeric literals | Green (#098658) |
| `lean-operator` | Mathematical symbols | Black (#000000) |
| `lean-comment` | `-- comments` | Green italic (#008000) |

### Rainbow Brackets (6 colors cycling by depth)

| Class | Color |
|-------|-------|
| `lean-bracket-1` | Magenta (#d000ff) |
| `lean-bracket-2` | Purple (#5126ff) |
| `lean-bracket-3` | Cyan (#0184BC) |
| `lean-bracket-4` | Blue (#4078F2) |
| `lean-bracket-5` | Green (#50A14F) |
| `lean-bracket-6` | Red (#E45649) |

## Build Process

```bash
# 1. Create marker file to enable Dress artifact generation
mkdir -p .lake/build
echo "1" > .lake/build/.dress

# 2. Build project - Hook.lean generates artifacts during elaboration
lake build

# 3. Remove marker file
rm .lake/build/.dress

# 4. Generate library index
lake build :blueprint

# 5. Build blueprint website and PDF
cd blueprint
leanblueprint pdf
leanblueprint web
```

The `scripts/build_blueprint.sh` automates this entire process.

## Configuration

### lakefile.toml

```toml
[[require]]
name = "Dress"
git = "https://github.com/e-vergo/Dress"
rev = "main"
```

Dress re-exports LeanArchitect, so only one `require` is needed.

### Lean Files

```lean
import Dress  -- Re-exports Architect

@[blueprint "thm:my-theorem"]
theorem myTheorem : 2 + 2 = 4 := rfl
```

## Error Handling

leanblueprint requires Dress artifacts. If artifacts are missing, it errors:

```
RuntimeError: Missing Dress artifacts for <node>: found \leansource but not \leansourcehtml.
Run Dress to generate pre-rendered HTML artifacts.
```

This ensures consistent, high-quality output. There is no fallback to:
- Rendering SubVerso JSON at leanblueprint time
- Reading source files directly
- Plain text without highlighting

## Debugging

### Check if Dress artifacts were generated

```bash
ls -la .lake/build/dressed/
ls -la .lake/build/blueprint/module/
```

### Check for pre-rendered HTML in .tex files

```bash
grep -r "leansourcehtml" .lake/build/blueprint/module/
```

### Verify HTML classes in output

```bash
grep -o 'class="[^"]*lean[^"]*"' blueprint/web/sect0004.html | sort -u
```

Should show `lean-keyword`, `lean-const`, `lean-bracket-*`, etc.

### Force full rebuild

```bash
rm -rf .lake/build/dressed .lake/build/blueprint
echo "1" > .lake/build/.dress
lake build
rm .lake/build/.dress
lake build :blueprint
cd blueprint && leanblueprint web
```
