# Lean Formal Verification Project

## Proof Standards

- No `sorry` statements in final deliverables
- No axioms, assertions, or trivial statements in place of complete proofs
- Meet or exceed Mathlib quality standards
- All proofs must be completed - deferral provides no benefit

## MCP Tool Usage (lean-lsp)

Primary tools - use frequently:
- `lean_goal` - Check proof state (omit column for before/after view)
- `lean_diagnostic_messages` - Compiler errors/warnings
- `lean_hover_info` - Type signatures and docs
- `lean_completions` - IDE autocomplete for incomplete code

Search tools (rate limited):
- `lean_local_search` - Fast local declaration search, use BEFORE trying lemma names
- `lean_leansearch` - Natural language to Mathlib (3/30s)
- `lean_loogle` - Type pattern to Mathlib (3/30s)
- `lean_leanfinder` - Semantic/conceptual search (10/30s)
- `lean_state_search` - Goal to closing lemmas (3/30s)
- `lean_hammer_premise` - Premises for simp/aesop (3/30s)

## Workflow

**Before writing proofs:**
- Read ALL transitively imported local files
- Use `lean_local_search` to find project-specific lemmas

**During proof development:**
- Work directly in actual project files - never create scratch files
- Check `lean_diagnostic_messages` frequently
- Read full error messages - they contain type information and unification failures

**When stuck:**
- Prefer existing Mathlib lemmas over custom proofs
- Use search tools to find relevant lemmas
- Use `lean_multi_attempt` to test multiple tactics without editing

**Proof preservation:**
- NEVER replace partial proofs with `sorry`
- Keep working intermediate steps
- Comment out non-working tactics rather than deleting

## Agent Delegation

Use Task tool with agents for:
- Complex multi-step proofs requiring deep context
- Reading all imports before working on a file
- Exploratory lemma/tactic search across codebases
- When context is near token limits

Launch agents in parallel for independent proof obligations.

## Powerful Tactics

**`grind`** - SMT-style automation using congruence closure, E-matching, and theory solvers:
- Subsumes `omega` for linear integer arithmetic
- Includes ring solver for polynomial equations
- `grind?` reports minimal `grind only [...]` call needed
- Options: `grind (splits := n)`, `grind -lia`, `grind +splitImp`
- Not for combinatorially explosive problems (use `bv_decide` instead)

**Suggestion tactics** - search for applicable lemmas/tactics:
- `exact?` / `apply?` - find lemmas matching the goal
- `simp?` - shows which simp lemmas work (use to build `simp only [...]`)
- `rw?` - suggests rewrite lemmas
- `try?` - general tactic search with fallback

## Lean-Specific Notes

- Never run `lake clean`
- Never use `lean_run_code` (token inefficient)
- Before building a project, ensure there is a build cache to avoid excessive build times


## Remember

- The code you will be writing will be reviewed by world class computer scientists and mathematicians, the will catch any deviations from complete, airtight, formalized mathematical proof
- Dont hallucinate
- The only way to produce suprise and delight in the user is to write world class code, formalizing known results. we are not doing research, we are autoformalizing. 
- Everything the user will ask you to do is doable based on what they have seen you do in previous sessions. By defualt, assume you can do something assigned to you.



# Side-by-Side Lean Code Display Architecture

This document describes the architecture for displaying Lean source code side-by-side with LaTeX theorem statements in the blueprint HTML output.

## Overview

The feature involves four repositories (all local forks for faster development):

1. **LeanArchitect** (`/Users/eric/GitHub/LeanArchitect`) - Lightweight Lean 4 library that provides the `@[blueprint]` attribute and stores declaration metadata
2. **Dress** (`/Users/eric/GitHub/Dress`) - Lean 4 tool that generates syntax-highlighted artifacts during compilation
3. **leanblueprint** (`/Users/eric/GitHub/leanblueprint`) - Python package that consumes Dress artifacts to produce interactive HTML/PDF
4. **SubVerso** (`/Users/eric/GitHub/subverso`) - Fork of leanprover/subverso with fix for synthetic source info handling

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
│  Phase 1: Elaboration-time (per @[blueprint] declaration)           │
│  ├── SubVerso captures semantic highlighting from info trees        │
│  ├── Verso renders HTML with hover tooltips                         │
│  └── Writes per-declaration artifacts immediately:                  │
│      .lake/build/dressed/{Module/Path}/{label}/                     │
│          decl.tex, decl.html, decl.json                             │
│                                                                     │
│  Phase 2: Lake facet (per module, after compilation)                │
│  ├── Scans declaration subdirs, aggregates into module.json         │
│  └── Generates module.tex with \input{} paths                       │
└─────────────────────────────────────────────────────────────────────┘
                              │
                              │ lake build :blueprint
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

## Output Directory Structure

```
.lake/build/dressed/{Module/Path}/
├── thm-main/
│   ├── decl.tex       # LaTeX with \lean{}, \leanok, base64 data
│   ├── decl.html      # Syntax-highlighted HTML with hover data
│   └── decl.json      # {"name": "...", "label": "...", "highlighting": {...}}
├── lem-helper/
│   └── ...
├── module.json        # Aggregated: {"DeclName": {"html", "htmlBase64", "jsonBase64"}}
└── module.tex         # \newleannode entries + \input{} directives
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

Dress uses a two-phase architecture: per-declaration artifacts during elaboration, module-level aggregation via Lake facets.

| File | Purpose |
|------|---------|
| `Dress/Capture/ElabRules.lean` | `elab_rules` for `@[blueprint]` declarations |
| `Dress/Capture/InfoTree.lean` | Environment extension, info tree capture |
| `Dress/Capture/Config.lean` | Blueprint config parsing |
| `Dress/Generate/Declaration.lean` | Per-declaration artifact writer (tex, html, json) |
| `Dress/Generate/Latex.lean` | LaTeX generation with base64-embedded HTML |
| `Dress/Paths.lean` | Path utilities for artifact locations |
| `Dress/HtmlRender.lean` | Verso HTML rendering with hover tooltips |
| `Dress/Core.lean` | `NodeWithPos` structure, signature/proof splitting |
| `Dress/Hook.lean` | Main entry point, re-exports submodules |
| `lakefile.lean` | Lake facets (`dressed`, `blueprint`) for aggregation |

**Dependencies:** LeanArchitect (local), SubVerso (local fork), Verso (local), Cli

### leanblueprint

leanblueprint consumes Dress artifacts (no fallback rendering).

| File | Purpose |
|------|---------|
| `Packages/blueprint.py` | plasTeX commands, requires Dress artifacts |
| `Packages/renderer_templates/Thms.jinja2s` | Side-by-side grid layout template |
| `static/blueprint.css` | Layout and syntax highlighting styles |

**Dependencies:** plasTeX, plastexdepgraph

### SubVerso (Fork)

SubVerso provides semantic syntax highlighting by extracting info trees during Lean elaboration. Our fork adds support for synthetic source info.

| File | Modification |
|------|--------------|
| `src/SubVerso/Highlighting/Code.lean` | `emitToken` now handles `.synthetic` source info |

**Upstream:** [leanprover/subverso](https://github.com/leanprover/subverso)

**Fix:** The upstream `emitToken` function throws an error for syntax with `.synthetic` source info (e.g., from macros or term-mode proofs). Our fork handles synthetic info gracefully by using its begin/end positions directly:

```lean
-- Before (upstream): throws error for synthetic info
| .synthetic b e =>
  throwError "Syntax {blame} not original, can't highlight: ..."

-- After (fork): handles synthetic info
| .synthetic b e _ =>
  openUntil <| text.toPosition b
  modify fun st => {st with output := Output.addToken st.output token}
  closeUntil e
  setLastPos (some e)
```

This allows highlighting to succeed for all declarations, not just those with original source info.

## Two-Phase Capture

Dress captures highlighting **during** Lean elaboration and writes artifacts immediately.

### Phase 1: Elaboration-time (per declaration)

When `.lake/build/.dress` exists, artifact generation is enabled:

```lean
-- From Capture/ElabRules.lean
let markerFile : System.FilePath := ".lake" / "build" / ".dress"
let markerExists ← markerFile.pathExists
let dressEnabled := dressEnv == some "1" || blueprint.dress.get (← getOptions) || markerExists
```

For each `@[blueprint]` declaration:
1. `elab_rules` fire after declaration elaboration
2. Info trees (containing type info for hovers) are captured while still available
3. SubVerso's `highlightIncludingUnparsed` extracts semantic highlighting
4. Verso renders HTML with `data-hover-id` attributes for tooltips
5. `Generate.writeDeclarationArtifacts` writes `decl.tex`, `decl.html`, `decl.json`

### Phase 2: Lake facet (per module)

After compilation, Lake facets aggregate per-declaration artifacts:
1. `dressed` facet scans `{label}/decl.json` files in module directory
2. Parses each to extract name, label, and highlighting data
3. Generates `module.json` in Dress format for leanblueprint
4. `blueprint` facet generates `module.tex` with `\input{}` paths

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
# List module directories
ls -la .lake/build/dressed/

# List declarations in a module
ls .lake/build/dressed/Crystallographic/FiniteOrder/Basic/

# Check a specific declaration's artifacts
ls .lake/build/dressed/Crystallographic/FiniteOrder/Basic/def-blockDiag2/
```

### Check for pre-rendered HTML in .tex files

```bash
grep -r "leansourcehtml" .lake/build/dressed/
```

### Verify HTML classes in output

```bash
grep -o 'class="[^"]*lean[^"]*"' blueprint/web/sect0004.html | sort -u
```

Should show `lean-keyword`, `lean-const`, `lean-bracket-*`, etc.

### Force full rebuild

```bash
rm -rf .lake/build/dressed
mkdir -p .lake/build && echo "1" > .lake/build/.dress
lake build
rm .lake/build/.dress
lake build :blueprint
cd blueprint && leanblueprint web
```
