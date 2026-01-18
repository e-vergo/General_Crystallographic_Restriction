# Side-by-Side Lean Code Display for Blueprint

This document describes the architecture for displaying Lean source code side-by-side with LaTeX theorem statements in the leanblueprint HTML output, including SubVerso semantic syntax highlighting and VSCode-quality lexical highlighting. This document is meant to capture the repo at a moment in time and provide a one-stop-shop for LLMs to get up to speed on the project. It is not meant to capture development history.

## Overview

The feature involves three repositories:
1. **LeanArchitect** (`/Users/eric/GitHub/LeanArchitect`) - Lean 4 library that extracts blueprint data from `@[blueprint]` attributes
2. **leanblueprint** (`/Users/eric/GitHub/leanblueprint`) - Python package that renders LaTeX to HTML using plasTeX
3. **General_Crystallographic_Restriction** (`/Users/eric/GitHub/General_Crystallographic_Restriction`) - The project using both

## Architecture

### Data Flow

```
Lean Source Code (@[blueprint] attributes)
    │
LeanArchitect extracts declarations with --highlight flag
    │
Highlighting.lean re-elaborates source with withInfoTreeContext
    │
SubVerso's highlightIncludingUnparsed produces Highlighted JSON
    │
Basic.lean: splitAtDefinitionAssign() splits at := for theorems with proofs
    │
Output.lean emits:
  - \leansignaturesource{base64_json}  (signature up to :=)
  - \leanproofsource{base64_json}      (proof body after :=)
  - \leanposition{...} and \leanproofposition{...}
    │
plasTeX parses .tex -> Node objects with userdata
    │
blueprint.py processes nodes:
  - If leansignature_base64 present: render_highlighted_base64() -> lean_signature_html
  - If leanproof_base64 present: render_highlighted_base64() -> lean_proof_html
  - Fallback: read source file, clean_lean_source() -> plain text HTML
    │
subverso_render.py rendering pipeline:
  1. _render_node() recursively processes SubVerso JSON
  2. _render_token() maps semantic tokens to CSS classes
  3. _highlight_plain_text() adds lexical highlighting (numbers, operators, comments, brackets)
  4. _renumber_brackets_by_depth() post-processes for global bracket depth tracking
    │
Thms.jinja2s template renders sbs-container grid layout
    │
HTML with .sbs-latex-column (75ch fixed) and .sbs-lean-column (flexible) side by side
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

### Lexical Highlighting (Post-SubVerso)

SubVerso captures semantic tokens but misses lexical tokens. The Python renderer adds:

1. **Comments**: `-- line comments` and `/- block comments -/`
2. **Numbers**: Integers, floats, hex (`123`, `3.14`, `0xFF`)
3. **Operators**: Mathematical symbols (`→←↔∀∃∈∉⊆⊇⊂⊃∧∨¬≤≥≠∼≃≡×∘∑∏∫∂√∞∅⁻¹·λ⊕⊗⊥⊤⊢⊣`)
4. **Rainbow brackets**: Depth-based coloring for `()[]{}⟨⟩⟦⟧`

The lexical highlighting pipeline:
```python
def _highlight_plain_text(text: str) -> str:
    # 1. Highlight brackets with depth tracking (per-token)
    result = _highlight_brackets_with_depth(text)
    # 2. Apply regex patterns for comments, numbers, operators
    #    (only to text outside HTML tags to avoid corrupting spans)
    result = _apply_patterns_outside_tags(result, LEXICAL_PATTERNS)
    return result
```

### Rainbow Bracket Depth Post-Processing

Since SubVerso splits code into separate tokens, bracket depth resets for each token. A post-processing pass fixes this:

```python
def _renumber_brackets_by_depth(html: str) -> str:
    """
    Post-process HTML to renumber bracket spans based on actual nesting depth.
    Scans entire HTML, tracks global depth, and renumbers lean-bracket-N classes.
    """
```

This ensures nested brackets like `(foo (bar (baz)))` get different colors even when the brackets are in separate SubVerso tokens.

### Proof Toggle Synchronization

When the LaTeX proof toggle (expand-proof icon) is clicked, JavaScript syncs the Lean proof body visibility using CSS class toggling for smooth animation:

```javascript
// From Thms.jinja2s - inline script per theorem
proofHeading.addEventListener('click', function() {
  setTimeout(function() {
    var icon = container.querySelector('.expand-proof');
    var isExpanded = icon && icon.textContent.trim() === '▼';
    if (isExpanded) {
      leanProofBody.classList.add('expanded');
    } else {
      leanProofBody.classList.remove('expanded');
    }
  }, 50);
});
```

The proof body uses `max-height` and `opacity` transitions for smooth expand/collapse animation rather than `display: none/block`.

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
Converts SubVerso `Highlighted` JSON to HTML with full syntax highlighting:

**Constants:**
- `LEXICAL_PATTERNS`: Regex patterns for comments, numbers, operators
- `OPENING_BRACKETS` / `CLOSING_BRACKETS`: Characters for rainbow bracket matching (`([{⟨⟦` / `)]}⟩⟧`)

**Core Functions:**
- `render_highlighted_base64()`: Entry point - decodes base64, parses JSON, renders to HTML, post-processes brackets
- `render_highlighted()`: Renders JSON and applies bracket depth post-processing
- `_render_node()`: Recursively renders tokens, text, sequences, spans, tactics
- `_render_token()`: Maps semantic token kinds to CSS classes, applies lexical highlighting to unknown tokens
- `_token_class()`: Maps SubVerso token kinds to CSS classes

**Lexical Highlighting Functions:**
- `_highlight_plain_text()`: Applies bracket highlighting then regex patterns
- `_highlight_brackets_with_depth()`: Per-token bracket coloring with depth tracking
- `_apply_patterns_outside_tags()`: Safely applies regex only to text outside HTML tags
- `_renumber_brackets_by_depth()`: Global post-processing to fix bracket depth across token boundaries

**Token Kind Mapping:**
| SubVerso Kind | CSS Class | Color (Light Theme) |
|---------------|-----------|---------------------|
| keyword | lean-keyword | Blue (#0000ff) |
| const | lean-const | Gold (#AF8700) |
| var | lean-var | Cyan-blue (#0070C1) |
| str | lean-string | Red (#a31515) |
| docComment | lean-docstring | Green italic (#008000) |
| sort | lean-sort | Teal (#267f99) |
| levelVar/Op/Const | lean-level | Green (#098658) |
| unknown | lean-text | (lexical highlighting applied) |

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
CSS styling for layout and syntax highlighting:

**Layout:**
```css
/* Wide content area for side-by-side display */
div.content-wrapper {
  max-width: 1800px;
}

/* Side-by-side grid: fixed LaTeX width, flexible Lean */
.sbs-container {
  display: grid;
  grid-template-columns: 75ch 1fr;  /* Standard blueprint width for LaTeX */
  gap: 3rem;
  margin-left: 3rem;  /* Match gap from sidebar */
  margin-bottom: 3rem;
}
```

**Proof Toggle Animation:**
```css
.lean-proof-body {
  display: block;
  max-height: 0;
  opacity: 0;
  overflow: hidden;
  transition: max-height 0.3s ease-out, opacity 0.2s ease-out;
}

.lean-proof-body.expanded {
  max-height: 5000px;
  opacity: 1;
  transition: max-height 0.4s ease-in, opacity 0.3s ease-in;
}
```

**Semantic Highlighting (SubVerso):**
- `.lean-keyword`: Blue (#0000ff) - `def`, `theorem`, `if`, `then`, `by`, `fun`
- `.lean-const`: Gold (#AF8700) - constants and functions
- `.lean-var`: Cyan-blue (#0070C1) - local variables
- `.lean-string`: Red (#a31515) - string literals
- `.lean-docstring`: Green italic (#008000) - doc comments
- `.lean-sort`: Teal (#267f99) - `Type`, `Prop`, `Sort`
- `.lean-sorry`: Red with pink background - `sorry`

**Lexical Highlighting (Regex):**
- `.lean-number`: Green (#098658) - numeric literals
- `.lean-operator`: Black (#000000) - mathematical symbols
- `.lean-comment`: Green italic (#008000) - `-- comments`

**Rainbow Brackets (6 colors cycling by depth):**
- `.lean-bracket-1`: Magenta (#d000ff)
- `.lean-bracket-2`: Purple (#5126ff)
- `.lean-bracket-3`: Cyan (#0184BC)
- `.lean-bracket-4`: Blue (#4078F2)
- `.lean-bracket-5`: Green (#50A14F)
- `.lean-bracket-6`: Red (#E45649)

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
- `lean-bracket-1`, `lean-bracket-2`, etc. = Rainbow brackets working

### Check bracket depth is working
```bash
grep -o 'lean-bracket-[1-6]' blueprint/web/sect0004.html | sort | uniq -c
```
Should show multiple bracket levels if nesting exists.

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

4. **Tactic goal display**: SubVerso captures goal states for tactics, stored as `data-*` attributes and hidden goal displays. Interactive goal exploration is not yet implemented in the UI.

5. **Dark theme support**: Current colors are optimized for light themes. A dark theme variant would require media query or class-based color switching.
