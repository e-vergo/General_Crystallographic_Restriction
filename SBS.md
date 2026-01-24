# Side-by-Side Lean Code Display Architecture

This document describes the architecture for displaying Lean source code side-by-side with LaTeX theorem statements in blueprint HTML output.

## Overview

The feature involves six repositories (local forks for faster development):

1. **LeanArchitect** (`/Users/eric/Github/LeanArchitect`) - Lightweight Lean 4 library providing the `@[blueprint]` attribute and metadata storage
2. **Dress** (`/Users/eric/Github/Dress`) - Lean 4 tool generating syntax-highlighted artifacts during compilation
3. **leanblueprint** (`/Users/eric/Github/leanblueprint`) - Python/plasTeX package consuming Dress artifacts to produce interactive HTML/PDF
4. **SubVerso** (`/Users/eric/Github/subverso`) - Syntax highlighting library for Lean 4 that extracts semantic info from elaboration
5. **dress-blueprint-action** (`/Users/eric/Github/dress-blueprint-action`) - GitHub Action automating the full build pipeline
6. **General_Crystallographic_Restriction** (`/Users/eric/Github/General_Crystallographic_Restriction`) - Example consumer project demonstrating ecosystem usage

## Architecture

```
┌─────────────────────────────────────────────────────────────────────────┐
│                         LEAN PROJECT                                    │
│  import Dress                                                           │
│  @[blueprint "thm:foo"] theorem foo : P → Q := ...                     │
└─────────────────────────────────────────────────────────────────────────┘
                              │
                              │ BLUEPRINT_DRESS=1 lake build
                              ▼
┌─────────────────────────────────────────────────────────────────────────┐
│                           DRESS                                         │
│                                                                         │
│  Phase 1: Elaboration-time (per @[blueprint] declaration)               │
│  ├── SubVerso captures semantic highlighting from info trees            │
│  ├── Verso renders HTML with hover tooltips (data-hover-id)             │
│  └── Writes per-declaration artifacts immediately:                      │
│      .lake/build/dressed/{Module/Path}/{label}/                         │
│          decl.tex, decl.html, decl.json                                 │
│                                                                         │
│  Phase 2: Lake facet (per module, after compilation)                    │
│  ├── Scans declaration subdirs, aggregates into module.json             │
│  └── Generates module.tex with \input{} paths                           │
└─────────────────────────────────────────────────────────────────────────┘
                              │
                              │ lake build :blueprint
                              ▼
┌─────────────────────────────────────────────────────────────────────────┐
│                        LEANBLUEPRINT                                    │
│                                                                         │
│  plasTeX parses .tex → extracts base64 HTML from macros:                │
│  ├── \leansourcehtml{base64}      → lean_source_html                    │
│  ├── \leansignaturesourcehtml{base64} → lean_signature_html             │
│  ├── \leanproofsourcehtml{base64} → lean_proof_html                     │
│  └── \leanhoverdata{base64}       → lean_hover_data                     │
│                                                                         │
│  Thms.jinja2s renders side-by-side grid layout                          │
│  Errors if Dress artifacts are missing (no fallback rendering)          │
└─────────────────────────────────────────────────────────────────────────┘
                              │
                              ▼
┌─────────────────────────────────────────────────────────────────────────┐
│                        HTML OUTPUT                                      │
│                                                                         │
│  .sbs-container (CSS grid):                                             │
│  ├── .sbs-latex-column (75ch fixed) - LaTeX theorem                     │
│  └── .sbs-lean-column (flexible) - Lean code with highlighting          │
│       ├── .lean-signature - Highlighted signature                       │
│       └── .lean-proof-body - Collapsible proof (synced with LaTeX)      │
│                                                                         │
│  Interactive features (verso-code.js):                                  │
│  ├── Tippy.js hover tooltips with type signatures                       │
│  ├── Token binding highlights (hover variable → all occurrences)        │
│  └── Tactic state expansion on click                                    │
└─────────────────────────────────────────────────────────────────────────┘
```

## Output Directory Structure

```text
.lake/build/dressed/
├── {Module/Path}/                    # Per-module directory
│   ├── {sanitized-label}/            # Per-declaration subdirectory
│   │   ├── decl.tex                  # LaTeX with \lean{}, \leanok, base64 data
│   │   ├── decl.html                 # Syntax-highlighted HTML with hover data
│   │   └── decl.json                 # {"name": "...", "label": "...", "highlighting": {...}}
│   ├── module.json                   # Aggregated: {"DeclName": {"html", "htmlBase64", "jsonBase64"}}
│   └── module.tex                    # \input{} directives for each declaration
│
├── nodes/                            # Flat directory for \inputleannode lookup
│   └── {sanitized-label}/
│       └── decl.tex                  # Copy of declaration .tex (enables label-based lookup)
│
└── library/
    └── {LibraryName}.tex             # Library index with macro definitions and module paths
```

The `nodes/` flat directory enables `\inputleannode{label}` to find declarations by label without knowing the module path.

## Key Files

### LeanArchitect

Lightweight metadata store with no artifact generation. Only depends on `batteries`.

| File | Purpose |
|------|---------|
| `Architect/Basic.lean` | `Node`, `NodePart`, `NodeWithPos` structures; `blueprintExt` and `latexLabelToLeanNamesExt` environment extensions |
| `Architect/Attribute.lean` | `@[blueprint]` attribute syntax and elaboration; `Config` structure |
| `Architect/CollectUsed.lean` | Automatic dependency inference from constant usage |
| `Architect/Command.lean` | `blueprint_comment` command for module-level documentation |
| `Architect/Tactic.lean` | `sorry_using`, `blueprint_using` tactics; proof docstring capture |
| `Architect/Content.lean` | `BlueprintContent` extraction from modules |
| `Architect/Output.lean` | LaTeX/JSON conversion and file I/O |
| `Architect/Load.lean` | `envOfImports` for programmatic environment loading |

**Data Structures:**
- `Node` - Declaration metadata (name, latexLabel, statement, proof, notReady, discussion, title)
- `NodePart` - Statement/proof section (text, uses, excludes, usesLabels, excludesLabels, latexEnv)
- `NodeWithPos` - Extends Node with location info (hasLean, location, file)

**Environment Extensions:**
- `blueprintExt : NameMapExtension Node` - All registered blueprint nodes
- `latexLabelToLeanNamesExt` - Reverse index: LaTeX label → Lean names (supports multiple declarations per label)
- `proofDocStringExt` - Proof docstrings captured from `/-/` comments
- `moduleBlueprintDocExt` - Module-level blueprint comments

### Dress

Two-phase architecture: per-declaration artifacts during elaboration, module-level aggregation via Lake facets.

| File | Purpose |
|------|---------|
| `Dress/Capture/ElabRules.lean` | `elab_rules` for theorem/def/abbrev/structure/class/inductive/instance |
| `Dress/Capture/InfoTree.lean` | `dressedDeclExt` environment extension; info tree capture |
| `Dress/Capture/State.lean` | IO.Ref state management (prevents recursion in elaboration hooks) |
| `Dress/Capture/Config.lean` | Blueprint config parsing from attribute syntax |
| `Dress/Serialize/Json.lean` | JSON serialization of SubVerso highlighting data |
| `Dress/Serialize/Html.lean` | HTML serialization; converts `NameMap Highlighted` to JSON maps |
| `Dress/Serialize/Artifacts.lean` | Full "dressed" artifact format: `{html, htmlBase64, jsonBase64}` |
| `Dress/Generate/Declaration.lean` | Per-declaration artifact writer (tex, html, json) |
| `Dress/Generate/Latex.lean` | LaTeX generation with base64-embedded HTML |
| `Dress/Generate/Module.lean` | Module-level utilities for Lake facets |
| `Dress/Paths.lean` | Centralized path management for artifact output |
| `Dress/HtmlRender.lean` | Verso HTML rendering wrapper for `Highlighted` objects |
| `Dress/Core.lean` | `NodeWithPos` structure, `splitAtDefinitionAssign` |
| `Dress/Base64.lean` | RFC 4648 Base64 encoding for embedding data in LaTeX |
| `Dress/Highlighting.lean` | Utilities for capturing SubVerso highlighting |
| `Dress/Hook.lean` | Main entry point, re-exports submodules |
| `lakefile.lean` | Lake facets (`dressed`, `blueprint`), `lake run dress` script |

**Dependencies:** LeanArchitect, SubVerso (fork), Verso, Cli

### leanblueprint

plasTeX plugin consuming Dress artifacts (no fallback rendering).

| File | Purpose |
|------|---------|
| `leanblueprint/Packages/blueprint.py` | plasTeX commands; base64 decoding; artifact validation |
| `leanblueprint/Packages/renderer_templates/Thms.jinja2s` | Side-by-side grid layout template |
| `leanblueprint/subverso_render.py` | SubVerso JSON → HTML renderer (fallback, rarely used) |
| `leanblueprint/client.py` | CLI tool (`leanblueprint new/pdf/web/serve/checkdecls`) |
| `leanblueprint/static/blueprint.css` | Layout styles, syntax highlighting, Tippy.js theming |
| `leanblueprint/static/blueprint.js` | Proof toggle sync script (LaTeX ↔ Lean proof visibility) |
| `leanblueprint/static/verso-code.js` | Interactive hover system (Tippy.js, token binding, tactic states) |
| `leanblueprint/static/vendor/` | Popper.js and Tippy.js libraries |
| `leanblueprint/templates/` | plasTeX config, LaTeX wrappers (web.tex, print.tex) |

**Dependencies:** plasTeX (≥3.1), plastexshowmore, plastexdepgraph, click, Jinja2, GitPython

### SubVerso

Semantic syntax highlighting library for Lean 4 that extracts and exports highlighted representations of Lean modules as JSON. Maintained by Lean FRO as a support library for Verso documentation.

| File | Purpose |
|------|---------|
| `src/SubVerso/Highlighting/Highlighted.lean` | Core data structures: `Token.Kind`, `Highlighted` inductive, `Goal`, `Message` |
| `src/SubVerso/Highlighting/Code.lean` | Main highlighting logic: `InfoTable`, token priority, expression tagging |
| `src/SubVerso/Highlighting/Export.lean` | Size optimization through deduplication |
| `src/SubVerso/Highlighting/Anchors.lean` | Example extraction with `-- ANCHOR:` markers |
| `src/SubVerso/Module.lean` | `ModuleItem` and `Module` structures for file-level metadata |
| `ExtractModule.lean` | CLI tool `subverso-extract-mod` for batch highlighting |

**Key Components:**

1. **Highlighted Data Structure:** Inductive type representing tokens, text, spans, tactics (with proof goals), and diagnostics
2. **Token.Kind:** Semantic categories (keyword, const, var, str, option, sort, moduleName)
3. **InfoTable:** Preprocessed info tree for efficient tactic state lookup
4. **Export:** Deduplication tables for compact JSON output

**Integration with Dress:**

```text
Dress Project
    └── extractModuleHighlighting(moduleName)
        ├── Calls: lake exe subverso-extract-mod <moduleName>
        ├── Parses JSON output (deduplicated tables + items)
        └── Returns: Array ModuleItem with Highlighted data
```

**Using `tactic-hover-support` branch** for enhanced tactic state capture.

### dress-blueprint-action

GitHub Action automating the complete build pipeline for Lean blueprint projects.

| File | Purpose |
|------|---------|
| `action.yml` | Action definition with 11 inputs, 2 outputs, composite steps |
| `examples/basic-workflow.yml` | Minimal workflow example |
| `examples/full-workflow.yml` | Full options with caching |

**Inputs:**

| Input | Default | Purpose |
|-------|---------|---------|
| `build-dressed` | `true` | Enable Dress artifact generation |
| `blueprint-facet` | `true` | Run `lake build :blueprint` |
| `build-pdf` | `true` | Generate PDF version |
| `build-web` | `true` | Generate HTML version |
| `check-decls` | `true` | Verify declarations match `lean_decls` |
| `lake-package-directory` | `.` | Location of lakefile.toml |
| `blueprint-directory` | `blueprint` | Blueprint source directory |
| `deploy-pages` | `true` | Upload artifact for GitHub Pages |
| `output-directory` | `_site` | Final assembled site output |
| `use-mathlib-cache` | `true` | Fetch pre-built Mathlib cache |
| `clean-dressed` | `false` | Remove dressed artifacts before build |
| `leanblueprint-version` | `git+https://github.com/e-vergo/leanblueprint.git` | pip package spec |

**Outputs:**
- `blueprint-pdf-path` - Path to generated PDF
- `blueprint-web-path` - Path to generated web directory

**Build Steps:**
1. Validate configuration (lakefile, blueprint directory)
2. Fetch Mathlib cache (optional)
3. Clean dressed artifacts (optional)
4. Build with Dress artifacts (`.lake/build/.dress` marker)
5. Build blueprint facet (`lake build :blueprint`)
6. Build blueprint documentation (texlive container)
7. Check declarations (optional)
8. Assemble site
9. Upload Pages artifact

## Two-Phase Capture

Dress captures highlighting **during** Lean elaboration and writes artifacts immediately.

### Phase 1: Elaboration-time (per declaration)

Artifact generation is enabled via:
- `.lake/build/.dress` marker file
- `BLUEPRINT_DRESS=1` environment variable
- `blueprint.dress` Lean option

```lean
-- From Capture/ElabRules.lean
let markerFile : System.FilePath := ".lake" / "build" / ".dress"
let markerExists ← markerFile.pathExists
let dressEnabled := dressEnv == some "1" || blueprint.dress.get (← getOptions) || markerExists
```

For each `@[blueprint]` declaration:
1. `elab_rules` fire after declaration elaboration
2. Info trees (containing type info for hovers) captured while available
3. SubVerso's `highlightIncludingUnparsed` extracts semantic highlighting
4. Verso renders HTML with `data-hover-id` attributes for tooltips
5. `Generate.writeDeclarationArtifacts` writes `decl.tex`, `decl.html`, `decl.json`

### Phase 2: Lake facet (per module)

After compilation, Lake facets aggregate per-declaration artifacts:

1. **`dressed` facet:**
   - Scans `.lake/build/dressed/{Module/Path}/` for declaration subdirectories
   - Reads each `decl.json` file
   - Aggregates into `module.json`:
     ```json
     {
       "MyProject.myTheorem": {
         "html": "...",
         "htmlBase64": "...",
         "jsonBase64": "..."
       }
     }
     ```

2. **`blueprint` facet:**
   - Depends on `dressed` facet
   - Generates `module.tex` with LaTeX preamble and `\input{}` paths

3. **Library/package facets:**
   - `library_facet blueprint`: Builds all module facets, generates library index
   - `package_facet blueprint`: Builds all library facets

### Code Splitting

`splitAtDefinitionAssign` in `Core.lean` handles splitting code at `:=`:

- Strips `@[blueprint]` prefix
- Finds definition keyword (`def`, `theorem`, `lemma`, etc.)
- Tracks bracket depth to find `:=` at depth 0
- Returns `(signature, proofBody)` for theorems with proofs

## LaTeX Macros

Dress embeds pre-rendered HTML in LaTeX:

| Macro | Content |
|-------|---------|
| `\leansourcehtml{base64}` | Full highlighted code |
| `\leansignaturesourcehtml{base64}` | Signature up to `:=` |
| `\leanproofsourcehtml{base64}` | Proof body after `:=` |
| `\leanhoverdata{base64}` | Hover tooltip JSON map |
| `\leanposition{file\|startLine\|startCol\|endLine\|endCol}` | Source location |
| `\leanproofposition{...}` | Proof-specific position |

**Blueprint-level macros:**
| Macro | Content |
|-------|---------|
| `\inputleanmodule{Module.Name}` | Include all declarations from a module |
| `\inputleannode{label}` | Include a specific declaration by label |
| `\lean{name1, name2}` | Link to Lean declarations |
| `\leanok` | Mark as formalized (no sorries) |
| `\notready` | Mark as work-in-progress |
| `\mathlibok` | Mark as in Mathlib |
| `\uses{label1, label2}` | Declare dependencies |
| `\discussion{issue_number}` | Link to GitHub issue |

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

### Lexical Highlighting (from leanblueprint/subverso_render.py)

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

### Interactive Features

| Class/Attribute | Purpose |
|-----------------|---------|
| `data-lean-hovers` | JSON map of hover ID → tooltip HTML |
| `data-hover-id` | Links token to hover data entry |
| `data-binding` | Unique binding ID for variable highlighting |
| `.binding-hl` | Yellow background for highlighted bindings |
| `.tactic` | Clickable tactic with expandable goal state |

## Build Process

### Local Build

```bash
# 1. Clean previous artifacts and enable Dress generation
rm -rf .lake/build/dressed .lake/build/lib/{YourProject} .lake/build/ir/{YourProject}
BLUEPRINT_DRESS=1 lake build

# 2. Generate library index and module aggregation
lake build :blueprint

# 3. Build blueprint website (PDF skipped by default - requires latexmk)
cd blueprint
leanblueprint web

# 4. Serve locally
leanblueprint serve
```

### Using build_blueprint.sh

The project includes a convenience script at `scripts/build_blueprint.sh` that:

1. Builds all local dependency forks (SubVerso, LeanArchitect, Dress)
2. Installs leanblueprint from local fork
3. Cleans and rebuilds with `BLUEPRINT_DRESS=1`
4. Runs `lake build :blueprint`
5. Runs `leanblueprint web` (PDF skipped)
6. Serves the result locally

### GitHub Actions

```yaml
- name: Build blueprint with Dress
  uses: e-vergo/dress-blueprint-action@main
  with:
    build-dressed: true
    build-pdf: true
    build-web: true
    use-mathlib-cache: true

- name: Deploy to GitHub Pages
  uses: actions/deploy-pages@v4
```

The action automates the entire pipeline from Lean compilation through HTML deployment.

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

@[blueprint "thm:my-theorem"
  (statement := /-- The statement in LaTeX. -/)
  (proof := /-- Proof explanation. -/)]
theorem myTheorem : 2 + 2 = 4 := rfl

-- With explicit dependencies
@[blueprint "lem:helper"
  (statement := /-- Helper lemma. \uses{thm:base} -/)
  (uses := [other_lemma])]
lemma helper : ... := by ...

-- Work-in-progress
@[blueprint "thm:wip" (notReady := true) (discussion := 42)]
theorem wip : ... := sorry
```

### Blueprint Directory

```
blueprint/
├── lean_decls              # List of @[blueprint] declaration names
├── src/
│   ├── blueprint.tex       # Master document with \inputleanmodule{}
│   ├── web.tex             # Web wrapper with plugin options
│   ├── print.tex           # Print wrapper
│   ├── plastex.cfg         # plasTeX configuration
│   └── latexmkrc           # LaTeX build config
├── web/                    # Generated HTML output
└── print/                  # Generated PDF output
```

### web.tex Example

```latex
\documentclass{report}
\usepackage[showmore, dep_graph, coverage, project=../../,
            thms=definition+lemma+proposition+theorem+corollary]{blueprint}
\home{https://example.github.io/project/}
\github{https://github.com/example/project}
\dochome{https://example.github.io/project/docs/}
\input{blueprint.tex}
\end{document}
```

## Interactive Features

### Hover Tooltips (verso-code.js)

- **Library:** Tippy.js with Popper.js positioning
- **Triggers:** `.lean-const`, `.lean-var`, `.lean-keyword`, `.lean-sort`, `.tactic`
- **Data source:** `data-lean-hovers` JSON parsed on page load
- **Themes:** `lean` (light gray), `warning`/`error`/`info` (colored), `tactic` (white, larger)
- **Delay:** 100ms before showing
- **Max dimensions:** 600px width, 300px height with scroll

### Token Binding Highlight

On mouseover of a variable, all occurrences with the same `data-binding` attribute receive the `.binding-hl` class (yellow background).

### Tactic State Display

Clickable `.tactic` tokens expand to show goal state with:
- Hypothesis list (names and types)
- Conclusion (goal type)
- Case names

### Proof Toggle Sync

Two mechanisms keep LaTeX and Lean proof visibility in sync:

1. **Click handler:** Template-injected JavaScript listens to proof heading clicks
2. **MutationObserver:** `verso-code.js` watches for expand icon changes and syncs Lean proof body visibility

## Error Handling

leanblueprint requires Dress artifacts. If artifacts are missing:

```
RuntimeError: Missing Dress artifacts for <node>: found \leansource but not \leansourcehtml.
Run Dress to generate pre-rendered HTML artifacts.
```

There is no fallback to:
- Rendering SubVerso JSON at leanblueprint time
- Reading source files directly
- Plain text without highlighting

This ensures consistent, high-quality output.

## Debugging

### Check Dress artifacts

```bash
# List module directories
ls -la .lake/build/dressed/

# List declarations in a module
ls .lake/build/dressed/Crystallographic/FiniteOrder/Basic/

# Check a specific declaration's artifacts
ls .lake/build/dressed/Crystallographic/FiniteOrder/Basic/def-blockDiag2/

# Verify pre-rendered HTML in .tex files
grep -r "leansourcehtml" .lake/build/dressed/
```

### Verify HTML output

```bash
# Check CSS classes in generated HTML
grep -o 'class="[^"]*lean[^"]*"' blueprint/web/sect0004.html | sort -u

# Should show: lean-keyword, lean-const, lean-bracket-*, etc.
```

### Force full rebuild

```bash
# Remove all dressed artifacts
rm -rf .lake/build/dressed

# Remove compiled Lean (forces re-elaboration)
rm -rf .lake/build/lib/{YourProject}
rm -rf .lake/build/ir/{YourProject}

# Rebuild with artifact generation
BLUEPRINT_DRESS=1 lake build
lake build :blueprint
cd blueprint && leanblueprint web
```

### Enable tracing

```lean
set_option trace.blueprint true
set_option trace.blueprint.debug true
```

## Dependency Chain

```
Consumer Project (e.g., General_Crystallographic_Restriction)
└── Dress (e-vergo/Dress)
    ├── LeanArchitect (e-vergo/LeanArchitect)
    │   └── batteries
    ├── SubVerso (e-vergo/subverso, fork)
    │   └── (Lean core)
    ├── Verso (leanprover/verso)
    └── Cli
```

At build time:
```
Lean Project + Dress → .lake/build/dressed/ artifacts
                            ↓
                      leanblueprint (Python)
                            ↓
                      blueprint/web/ + blueprint/print/
                            ↓
                      dress-blueprint-action (GitHub)
                            ↓
                      GitHub Pages deployment
```
