# Side-by-Side Lean Code Display for Blueprint

This document describes the architecture for displaying Lean source code side-by-side with LaTeX theorem statements in the leanblueprint HTML output, including SubVerso semantic syntax highlighting. This document is meant to capture the repo at a moment in time and provide a one-stop-shop for LLMs to get up to speed on the project. It is not meant to capture development history.

## Overview

The feature involves three repositories:
1. **LeanArchitect** (`/Users/eric/GitHub/LeanArchitect`) - Lean 4 library that extracts blueprint data from `@[blueprint]` attributes
2. **leanblueprint** (`/Users/eric/GitHub/leanblueprint`) - Python package that renders LaTeX to HTML using plasTeX
3. **General_Crystallographic_Restriction** (`/Users/eric/GitHub/General_Crystallographic_Restriction`) - The project using both

## Architecture

### Data Flow

```
Lean Source Code (@[blueprint] attributes)
    |
LeanArchitect extracts declarations with --highlight flag
    |
Highlighting.lean re-elaborates source with withInfoTreeContext
    |
SubVerso's highlightIncludingUnparsed produces Highlighted JSON
    |
Basic.lean: splitAtDefinitionAssign() splits at := for theorems with proofs
    |
Output.lean emits:
  - \leansignaturesource{base64_json}  (signature up to :=)
  - \leanproofsource{base64_json}      (proof body after :=)
  - \leanposition{...} and \leanproofposition{...}
    |
plasTeX parses .tex -> Node objects with userdata
    |
blueprint.py processes nodes:
  - If leansignature_base64 present: render_highlighted_base64() -> lean_signature_html
  - If leanproof_base64 present: render_highlighted_base64() -> lean_proof_html
  - Fallback: read source file, clean_lean_source() -> plain text HTML
    |
Thms.jinja2s template renders sbs-container grid layout
    |
HTML with .sbs-latex-column and .sbs-lean-column side by side
```

### Code Splitting Logic

The `splitAtDefinitionAssign` function in `Basic.lean` handles splitting highlighted code:

1. **Strip @[blueprint] prefix**: The function always removes any prefix before the definition keyword (def/theorem/lemma/abbrev/instance/example), stripping attributes like `@[blueprint ...]`.

2. **Find the definition keyword**: Scans tokens for `def`, `theorem`, `lemma`, `abbrev`, `instance`, or `example`.

3. **Find `:=` at bracket depth 0**: After the definition keyword, tracks bracket depth `()[]{}` and finds the `:=` token when depth is 0.

4. **Split behavior**:
   - If `node.proof.isSome` (theorem with proof): Splits at `:=`, returning `(signature, body)` where signature includes `:=`.
   - If `node.proof.isNone` (definition without proof section): Returns full code from def keyword with no body split.

### SubVerso Highlighting

SubVerso produces semantic highlighting by re-elaborating source code:

1. `computeHighlighting` extracts the declaration source from the file using position ranges.
2. `highlightSource` re-elaborates the source with `withInfoTreeContext` to capture proper info trees.
3. `highlightIncludingUnparsed` produces a `Highlighted` JSON structure with token kinds.

The `Highlighted` type contains:
- `token`: Semantic tokens with `kind` (keyword, const, var, string, etc.) and `content`
- `text`: Plain text
- `seq`: Sequences of highlighted nodes
- `span`: Spans with attached messages (errors/warnings/info)
- `tactics`: Tactic blocks with goal information

### Proof Toggle Synchronization

When the LaTeX proof toggle (expand-proof icon) is clicked, JavaScript syncs the Lean proof body visibility:

```javascript
// From Thms.jinja2s - inline script per theorem
proofHeading.addEventListener('click', function() {
  setTimeout(function() {
    var icon = container.querySelector('.expand-proof');
    var isExpanded = icon && icon.textContent.trim() === '▼';
    leanProofBody.style.display = isExpanded ? 'inline' : 'none';
  }, 50);
});
```

The `setTimeout` delay allows plastex.js to toggle the icon before we read its state.

## Key Files

### LeanArchitect

#### Architect/Basic.lean
Core data structures and highlighting logic:
- `NodeWithPos`: Extended node with `highlightedSignature` and `highlightedProofBody` fields
- `splitAtDefinitionAssign`: Bracket-aware splitting at `:=` token
- `computeHighlighting`: Extracts source and runs SubVerso highlighting
- `Node.toNodeWithPos`: Converts node with optional highlighting computation

#### Architect/Output.lean
LaTeX emission:
- `NodeWithPos.toLatex`: Emits `\leansignaturesource{}` and `\leanproofsource{}` as base64-encoded SubVerso JSON
- Commands emitted INSIDE the LaTeX environment so plasTeX attaches userdata to correct node

#### Architect/Highlighting.lean
SubVerso integration following the Verso pattern:
- `highlightSource`: Re-elaborates source with `withInfoTreeContext`
- `runCommand`: Wraps command elaboration to capture contextualized info trees

### leanblueprint

#### leanblueprint/subverso_render.py
Converts SubVerso `Highlighted` JSON to HTML:
- `render_highlighted_base64()`: Decodes base64, parses JSON, renders to HTML
- `_render_node()`: Recursively renders tokens, text, sequences, spans, tactics
- `_token_class()`: Maps token kinds to CSS classes (lean-keyword, lean-const, lean-var, etc.)
- `_token_data_attrs()`: Extracts data attributes for hover info

#### leanblueprint/Packages/blueprint.py
plasTeX command classes and post-parse processing:
- `leansignaturesource`: Stores base64-encoded signature JSON in `leansignature_base64` userdata
- `leanproofsource`: Stores base64-encoded proof JSON in `leanproof_base64` userdata
- `leanposition`: Stores file path and line/column range
- `make_lean_data()`: Post-parse callback that:
  - Renders SubVerso JSON to HTML via `render_highlighted_base64()`
  - Falls back to reading source file with `clean_lean_source()` for plain text
  - Builds GitHub permalinks from position data

#### leanblueprint/Packages/renderer_templates/Thms.jinja2s
Jinja2 template for theorem environments:
```jinja2
<div class="{{ obj.thmName }}_thmwrapper sbs-container" id="{{ obj.id }}">
  <div class="sbs-latex-column">
    {# LaTeX theorem content and proof #}
  </div>
  {% if obj.userdata.lean_signature_html %}
  <div class="sbs-lean-column">
    <pre class="lean-code">
      <code class="lean-signature">{{ obj.userdata.lean_signature_html | safe }}</code>
      {% if obj.userdata.lean_proof_html %}
      <code class="lean-proof-body">{{ obj.userdata.lean_proof_html | safe }}</code>
      {% endif %}
    </pre>
  </div>
  {% endif %}
</div>
```

Inline JavaScript handles proof toggle sync for each theorem with a proof.

#### leanblueprint/static/blueprint.css
CSS styling:
- `.sbs-container`: Grid layout with two columns
- `.lean-proof-body`: Initially `display: none`, shown via JS when proof expanded
- SubVerso syntax highlighting classes: `.lean-keyword`, `.lean-const`, `.lean-var`, etc.

## Build Process

The `scripts/build_blueprint.sh` executes:
1. Build LeanArchitect (`lake build`)
2. Build project and blueprint data (`lake build :blueprint` - uses `--highlight` flag)
3. Run leanblueprint (`leanblueprint pdf && leanblueprint web`)

## Configuration

### Development (Local Forks)
```toml
# lakefile.toml
[[require]]
name = "LeanArchitect"
path = "/Users/eric/GitHub/LeanArchitect"
```

```bash
pipx install -e /Users/eric/GitHub/leanblueprint
```

### Production (GitHub)
```toml
[[require]]
name = "LeanArchitect"
git = "https://github.com/e-vergo/LeanArchitect"
rev = "main"
```

```bash
pipx install leanblueprint
```

## Debugging

### Check if SubVerso highlighting is working
```bash
grep -r "leansignaturesource" .lake/build/blueprint/module/
```
If empty, SubVerso highlighting is failing silently.

### Check HTML output classes
```bash
grep -o 'class="[^"]*lean[^"]*"' blueprint/web/sect0004.html | sort -u
```
- `lean-plain` = fallback path (no SubVerso highlighting)
- `lean-keyword`, `lean-const`, etc. = SubVerso highlighting working

### Force full rebuild
```bash
rm -rf .lake/build/blueprint
lake build :blueprint
cd blueprint && leanblueprint web
```

## Known Issues / TODOs

1. **Proof toggle timing**: The 50ms setTimeout in the JavaScript is a workaround for plastex.js async icon toggling. A MutationObserver approach is also included in `sbs-script` for more robust handling.

2. **Fallback path**: When SubVerso highlighting fails (e.g., due to parsing issues), the fallback reads the source file and uses `clean_lean_source()` to strip docstrings and `@[...]` attributes. This produces plain text without semantic highlighting.

3. **GitHub permalink branch**: Currently hardcoded to `main` branch. Could be made configurable.

4. **Universe levels and tactics**: SubVerso captures hover information and goal states for tactics, but these are not yet fully exposed in the HTML rendering (they're stored as `data-*` attributes and hidden goal displays).
