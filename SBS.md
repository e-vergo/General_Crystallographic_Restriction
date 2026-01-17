# Side-by-Side Lean Code Display for Blueprint

This document describes the architecture for displaying Lean source code side-by-side with LaTeX theorem statements in the leanblueprint HTML output, including SubVerso semantic syntax highlighting.

## Overview

The feature involves three repositories:
1. **LeanArchitect** (`/Users/eric/GitHub/LeanArchitect`) - Lean 4 library that extracts blueprint data from `@[blueprint]` attributes
2. **leanblueprint** (`/Users/eric/GitHub/leanblueprint`) - Python package that renders LaTeX to HTML using plasTeX
3. **General_Crystallographic_Restriction** (`/Users/eric/GitHub/General_Crystallographic_Restriction`) - The project using both

## Architecture

### Data Flow

```
Lean Source Code (@[blueprint] attributes)
    ↓
LeanArchitect extracts declarations with --highlight flag
    ↓
Highlighting.lean re-elaborates source with withInfoTreeContext
    ↓
SubVerso's highlightIncludingUnparsed produces Highlighted JSON
    ↓
Output.lean emits \leansource{base64_json} and \leanposition{...} INSIDE environments
    ↓
plasTeX parses .tex → Node objects with userdata (leansource_base64, leanposition)
    ↓
blueprint.py processes nodes:
  - If leansource_base64 present: render_highlighted_base64() → lean_source_html
  - Fallback: read source file → lean_signature_html, lean_proof_html (plain text)
    ↓
Thms.jinja2s template renders sbs-container grid layout
    ↓
HTML with .sbs-latex-column and .sbs-lean-column side by side
```

### Critical Implementation Details

#### 1. plasTeX Parent Node Assignment

**plasTeX's `self.parentNode` during command parsing depends on where the command appears in the LaTeX source.**

```latex
% WRONG - parentNode is the SECTION, not the definition:
\begin{definition}
...content...
\end{definition}
\leanposition{...}

% CORRECT - parentNode is the definition:
\begin{definition}
\leanposition{...}
...content...
\end{definition}
```

This is why `Output.lean` emits `\leanposition{}` and `\leansource{}` as part of `addLatex` (which goes inside the environment).

#### 2. SubVerso Highlighting via Re-elaboration

SubVerso requires properly contextualized info trees. A previous approach of capturing info trees during a linter phase caused panics ("unexpected contextless node") because info trees lacked proper `.context` wrappers.

The solution follows the Verso (Lean 4 reference manual) pattern:
1. Parse the declaration source text
2. Re-elaborate each command wrapped in `withInfoTreeContext`
3. Capture the resulting info trees
4. Pass to `highlightIncludingUnparsed` in a proper TermElabM context

```lean
-- From Highlighting.lean
def runCommand (act : CommandElabM Unit) (stx : Syntax) (ctx : Command.Context)
    (state : Command.State) : IO Command.State := do
  let act' := withInfoTreeContext
    (mkInfoTree := pure ∘ InfoTree.node (.ofCommandInfo {elaborator := `Architect.highlight, stx}))
    act
  match ← EIO.toIO' <| (act' ctx).run state with
  | .ok ((), state') => return state'
  | .error e => throw <| IO.userError s!"Command elaboration failed: {← e.toMessageData.toString}"
```

#### 3. Proof Toggle Synchronization

The LaTeX proof is rendered inside `.sbs-latex-column` via `{{ obj }}`. JavaScript syncs the Lean proof body visibility with the LaTeX proof toggle:

```javascript
// From Thms.jinja2s sbs-script
document.querySelectorAll('.expand-proof').forEach(function(toggle) {
  toggle.addEventListener('click', function() {
    var wrapper = toggle.closest('.sbs-container');
    if (wrapper) {
      var proofBody = wrapper.querySelector('.lean-proof-body');
      if (proofBody) {
        // Check icon state AFTER plastex.js toggles it
        setTimeout(function() {
          var icon = toggle.textContent || toggle.innerText;
          // ▼ = expanded → show Lean proof; ▶ = collapsed → hide
          proofBody.style.display = (icon.trim() === '▼') ? 'inline' : 'none';
        }, 50);
      }
    }
  });
});
```

## File Structure

### LeanArchitect

#### lakefile.lean
```lean
require subverso from git
  "https://github.com/leanprover/subverso"

/-- A facet to extract the blueprint for a module. -/
module_facet blueprint (mod : Module) : Unit := do
  buildModuleBlueprint mod "tex" #["--highlight"]  -- Enables SubVerso highlighting
```

#### Main.lean
```lean
def singleCmd := `[Cli|
  single VIA runSingleCmd;
  FLAGS:
    j, json; "Output JSON instead of LaTeX."
    h, highlight; "Compute SubVerso syntax highlighting for Lean code."
    b, build : String; "Build directory."
    o, options : String; "LeanOptions in JSON to pass to running the module."
  ARGS:
    module : String; "The module to extract the blueprint for."
]
```

#### Architect/Highlighting.lean
Core SubVerso integration following the Verso pattern:
- `highlightSource`: Re-elaborates source with `withInfoTreeContext`, returns `Highlighted`
- `runHighlighting`: Runs `highlightIncludingUnparsed` in TermElabM context
- `runCommand`: Wraps command elaboration to capture contextualized info trees

#### Architect/Basic.lean
```lean
structure NodeWithPos extends Node where
  hasLean : Bool
  location : Option DeclarationLocation
  proofLocation : Option DeclarationRange := none
  file : Option System.FilePath
  highlightedCode : Option SubVerso.Highlighting.Highlighted := none

def computeHighlighting (file : System.FilePath) (range : DeclarationRange)
    (env : Environment) (opts : Options := {}) : IO (Option SubVerso.Highlighting.Highlighted)

def Node.toNodeWithPos (node : Node) (computeHighlight : Bool := false) : CoreM NodeWithPos
```

#### Architect/Output.lean
```lean
def NodeWithPos.toLatex (node : NodeWithPos) : m Latex := do
  -- ... build addLatex ...

  -- Emit INSIDE the environment so plasTeX attaches to correct node
  if let (some file, some location) := (node.file, node.location) then
    let positionStr := s!"{file}|{location.range.pos.line}|..."
    addLatex := addLatex ++ "\\leanposition{" ++ positionStr ++ "}\n"
  if let some hl := node.highlightedCode then
    let jsonStr := (toJson hl).compress
    let base64Json := stringToBase64 jsonStr
    addLatex := addLatex ++ "\\leansource{" ++ base64Json ++ "}\n"
```

### leanblueprint

#### leanblueprint/subverso_render.py
Converts SubVerso `Highlighted` JSON to HTML with CSS classes:
```python
def render_highlighted(highlighted_json: str) -> str:
    """Convert SubVerso Highlighted JSON to HTML."""

def _token_class(kind: Any) -> str:
    """Map SubVerso Token.Kind to CSS class."""
    # Returns: lean-keyword, lean-const, lean-var, lean-string, etc.
```

#### leanblueprint/Packages/blueprint.py
plasTeX command classes:
```python
class leansource(Command):
    r"""\leansource{base64_encoded_json}"""
    args = 'source:str'
    def digest(self, tokens):
        Command.digest(self, tokens)
        self.parentNode.setUserData('leansource_base64', self.attributes['source'])

class leanposition(Command):
    r"""\leanposition{file|startLine|startCol|endLine|endCol}"""
    # Sets leanposition userdata dict
```

Processing in `make_lean_data()`:
```python
# If SubVerso highlighting available:
if node.userdata.get('leansource_base64'):
    node.userdata['lean_source_html'] = render_highlighted_base64(
        node.userdata['leansource_base64']
    )

# Fallback: read source file directly
if not node.userdata.get('lean_signature_html'):
    # Read file, split signature/proof, HTML escape
    node.userdata['lean_signature_html'] = f'<span class="lean-plain">{escaped}</span>'
```

#### leanblueprint/Packages/renderer_templates/Thms.jinja2s
```jinja2
<div class="{{ obj.thmName }}_thmwrapper sbs-container" id="{{ obj.id }}">
  <div class="sbs-latex-column">
    <div class="{{ obj.thmName }}_thmheading">...</div>
    <div class="{{ obj.thmName }}_thmcontent">{{ obj }}</div>
  </div>
  {% if obj.userdata.lean_signature_html %}
  <div class="sbs-lean-column">
    <pre class="lean-code"><code class="lean-signature">{{ obj.userdata.lean_signature_html | safe }}</code>{% if obj.userdata.lean_proof_html %}<code class="lean-proof-body">{{ obj.userdata.lean_proof_html | safe }}</code>{% endif %}</pre>
    {% if obj.userdata.lean_github_permalink %}
    <a href="{{ obj.userdata.lean_github_permalink }}" class="lean-github-hover" target="_blank">GitHub</a>
    {% endif %}
  </div>
  {% endif %}
</div>
```

#### leanblueprint/static/blueprint.css
```css
.sbs-container {
  display: grid;
  grid-template-columns: 1fr 1fr;
  gap: 2rem;
  align-items: start;
}

.lean-proof-body {
  display: none;  /* Shown via JS when proof toggle expanded */
}

/* SubVerso syntax highlighting */
.lean-keyword { color: #8959a8; font-weight: bold; }
.lean-const { color: #4271ae; }
.lean-var { color: #c82829; }
.lean-string { color: #718c00; }
/* ... etc */
```

## Build Process

The `scripts/build_blueprint.sh` executes:
1. Build LeanArchitect (`lake build`)
2. Build project and blueprint data (`lake build :blueprint` - uses `--highlight` flag)
3. Run leanblueprint (`leanblueprint pdf && leanblueprint web`)

## Current Challenge

**Symptom**: Lean code displays as plain text without syntax highlighting. The HTML shows `class="lean-plain"` instead of SubVerso classes like `lean-keyword`, `lean-const`.

**Root Cause**: The `computeHighlighting` function in `Basic.lean` extracts just the declaration source from the file, but SubVerso's re-elaboration needs the source to be parseable as standalone Lean code. A bare declaration without imports/namespace context fails to parse, so `computeHighlighting` catches the exception and returns `none`, causing no `\leansource{}` to be emitted.

**The Chain**:
1. `--highlight` flag is passed ✓
2. `Node.toNodeWithPos` is called with `computeHighlight := true` ✓
3. `computeHighlighting` extracts source text from file ✓
4. `highlightSource` attempts to re-elaborate the extracted text
5. Re-elaboration fails because the extracted text (e.g., `theorem foo : ...`) lacks imports
6. Exception caught, returns `none`
7. `node.highlightedCode` is `none`, so `\leansource{}` is not emitted
8. Python fallback reads source file as plain text with `class="lean-plain"`

**Potential Solutions**:

1. **Pass full file content**: Instead of extracting just the declaration range, pass the entire file to SubVerso. This preserves all imports and context.

2. **Construct minimal valid source**: Prepend the necessary imports to the extracted declaration:
   ```lean
   def mkMinimalSource (imports : Array Name) (declText : String) : String :=
     let importLines := imports.map (fun n => s!"import {n}") |>.toList |> "\n".intercalate
     s!"{importLines}\n\n{declText}"
   ```

3. **Use different SubVerso API**: SubVerso may have APIs that work with existing info trees rather than requiring re-elaboration.

4. **Cache during compilation**: Capture highlighted output during initial elaboration when the full context is available (the original linter approach), but ensure proper info tree context wrapping.

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

### Check if \leansource appears in .tex output
```bash
grep -r "leansource" .lake/build/blueprint/module/
```
If empty, SubVerso highlighting is failing silently.

### Check HTML output classes
```bash
grep -o 'class="[^"]*lean[^"]*"' blueprint/web/sect0004.html | sort -u
```
- `lean-plain` = fallback path (no highlighting)
- `lean-keyword`, `lean-const`, etc. = SubVerso highlighting working

### Check leanblueprint installation
```bash
pipx list | grep leanblueprint
pip show leanblueprint | grep Location
```

### Force full rebuild
```bash
rm -rf .lake/build/blueprint
lake build :blueprint
cd blueprint && leanblueprint web
```

### Test SubVerso highlighting manually
Add debug output to `computeHighlighting` in `Basic.lean`:
```lean
def computeHighlighting ... := do
  try
    let contents ← IO.FS.readFile file
    -- ... extract source ...
    IO.eprintln s!"Attempting to highlight: {source.take 100}..."
    let (hl, msgs) ← highlightSource source env opts file.toString
    IO.eprintln s!"Highlighting succeeded"
    return some hl
  catch e =>
    IO.eprintln s!"Highlighting failed: {e}"
    return none
```
