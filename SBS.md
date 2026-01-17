# Side-by-Side Lean Code Display for Blueprint

This document describes the implementation of side-by-side Lean code display in the leanblueprint system. This feature shows the actual Lean source code alongside each theorem/definition in the blueprint HTML output, with clickable GitHub permalinks.

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
LeanArchitect extracts declarations → .tex artifacts with \leanposition{...}
    ↓
leanblueprint/plasTeX parses .tex → Node objects with userdata
    ↓
make_lean_data() reads source files → lean_source_html in userdata
    ↓
Thms.jinja2s template renders → HTML with .lean-source-panel divs
```

### Key Insight: plasTeX Parent Node Assignment

The most critical debugging insight: **plasTeX's `self.parentNode` during command parsing depends on where the command appears in the LaTeX source.**

If `\leanposition{}` appears AFTER `\end{definition}`:
```latex
\begin{definition}
...content...
\end{definition}
\leanposition{...}  ← parentNode is the SECTION, not the definition!
```

If `\leanposition{}` appears INSIDE the environment:
```latex
\begin{definition}
...content...
\leanposition{...}  ← parentNode is the definition (correct!)
\end{definition}
```

This is why the fix in Output.lean moves `\leanposition{}` to be emitted as part of `addLatex` (which goes inside the environment) rather than as `extraLatex` (which went after).

## Implementation Details

### LeanArchitect Changes

#### lakefile.lean
Added SubVerso dependency (for future semantic highlighting):
```lean
require subverso from git
  "https://github.com/leanprover/subverso"
```

#### Architect/Basic.lean
Added infrastructure for highlighted code storage:
```lean
structure NodeWithPos extends Node where
  hasLean : Bool
  location : Option DeclarationLocation
  file : Option System.FilePath
  highlightedCode : Option SubVerso.Highlighting.Highlighted := none

initialize highlightedCodeExt : NameMapExtension SubVerso.Highlighting.Highlighted ←
  registerNameMapExtension SubVerso.Highlighting.Highlighted

def addHighlightedCode (name : Name) (hl : SubVerso.Highlighting.Highlighted) : CoreM Unit :=
  modifyEnv fun env => highlightedCodeExt.insert env name hl

def getHighlightedCode? (env : Environment) (name : Name) : Option SubVerso.Highlighting.Highlighted :=
  highlightedCodeExt.find? env name
```

#### Architect/Highlighting.lean
Created linter for capturing SubVerso highlighted code. **Currently disabled** due to SubVerso panic:
```lean
private def processDeclaration (_declStx : Syntax) : CommandElabM Unit := do
  -- SubVerso highlighting disabled - causes panics with "unexpected context-free info tree node"
  -- when processing info trees during the linter phase.
  -- TODO: Investigate running SubVerso in a post-processing phase instead.
  return
```

#### Architect/Output.lean
The key fix - emit `\leanposition{}` INSIDE the environment:
```lean
def NodeWithPos.toLatex (node : NodeWithPos) : m Latex := do
  -- ... earlier code building addLatex ...

  -- Emit \leanposition and \leansource INSIDE the environment so plasTeX attaches them to the correct node
  if let (some file, some location) := (node.file, node.location) then
    let positionStr := s!"{file}|{location.range.pos.line}|{location.range.pos.column}|{location.range.endPos.line}|{location.range.endPos.column}"
    addLatex := addLatex ++ "\\leanposition{" ++ positionStr ++ "}\n"
  if let some hl := node.highlightedCode then
    let jsonStr := (toJson hl).compress
    let base64Json := stringToBase64 jsonStr
    addLatex := addLatex ++ "\\leansource{" ++ base64Json ++ "}\n"

  -- addLatex is passed to toLatex as additionalContent, which goes INSIDE the \begin{...}...\end{...}
  let statementLatex ← node.statement.toLatex ... addLatex
```

### leanblueprint Changes

#### leanblueprint/subverso_render.py (new file)
Converts SubVerso JSON to HTML. Handles the Highlighted type variants:
- `token`: Semantic tokens with syntax category
- `text`: Plain text
- `seq`: Sequence of highlighted items
- `span`: Span with info
- `tactics`: Tactic sequences
- `point`: Point markers
- `unparsed`: Unparsed content

Key functions:
```python
def render_highlighted(hl: dict) -> str:
    """Convert SubVerso Highlighted JSON to HTML string."""

def render_highlighted_base64(base64_data: str) -> str:
    """Decode base64, parse JSON, render to HTML."""

def get_css() -> str:
    """Return CSS for SubVerso syntax highlighting."""
```

#### leanblueprint/Packages/blueprint.py

**Command classes** (lines ~122-146):
```python
class leansource(Command):
    r"""\leansource{base64_encoded_json}"""
    args = 'source:str'
    def digest(self, tokens):
        Command.digest(self, tokens)
        self.parentNode.setUserData('leansource_base64', self.attributes['source'])

class leanposition(Command):
    r"""\leanposition{file|startLine|startCol|endLine|endCol}"""
    args = 'position:str'
    def digest(self, tokens):
        Command.digest(self, tokens)
        parts = self.attributes['position'].split('|')
        if len(parts) == 5:
            self.parentNode.setUserData('leanposition', {
                'file': parts[0],
                'startLine': int(parts[1]),
                'startCol': int(parts[2]),
                'endLine': int(parts[3]),
                'endCol': int(parts[4])
            })
```

**Template** (lines ~197-209):
```python
LEAN_SOURCE_TPL = Template("""
{% if obj.userdata.lean_source_html %}
<div class="lean-source-panel">
    <div class="lean-source-header">
        <span class="lean-source-title">Lean Source</span>
        {% if obj.userdata.lean_github_permalink %}
        <a href="{{ obj.userdata.lean_github_permalink }}" class="lean-github-link" target="_blank" rel="noopener">View on GitHub</a>
        {% endif %}
    </div>
    <pre class="lean-code"><code>{{ obj.userdata.lean_source_html | safe }}</code></pre>
</div>
{% endif %}
""")
```

**make_lean_data() processing** (lines ~238-310):
- Converts absolute file paths to relative paths for GitHub URLs
- Reads source files directly as fallback when SubVerso highlighting unavailable
- Builds GitHub permalinks with line ranges

**Template registration** (line ~418):
```python
document.userdata.setdefault('thm_body_extras_tpl', []).extend([LEAN_SOURCE_TPL])
```

#### leanblueprint/Packages/renderer_templates/Thms.jinja2s (new file)
Custom plasTeX template that adds `thm_body_extras_tpl` rendering:
```jinja2
  <div class="{{ obj.thmName }}_thmcontent">
  {{ obj }}
  </div>
  {% if doc.userdata.get('thm_body_extras_tpl') %}
  <div class="thm_body_extras">
  {% for tpl in doc.userdata['thm_body_extras_tpl'] %}
  {% include tpl %}
  {% endfor %}
  </div>
  {% endif %}
```

This overrides the default plasTeX `Thms.jinja2s` to add the body extras section.

#### leanblueprint/static/blueprint.css
Added CSS for the Lean source panel (collapsible, syntax highlighting classes, etc.)

## Current State

### Working
- GitHub permalinks (e.g., `https://github.com/e-vergo/General_Crystallographic_Restriction/blob/main/Crystallographic/Psi/Basic.lean#L49-L63`)
- Source code display (plain text, HTML-escaped)
- Side-by-side layout in blueprint HTML

### Not Working / Disabled
- **SubVerso semantic highlighting**: Causes panic "unexpected context-free info tree node" when processing info trees during the linter phase
  - The infrastructure is in place (`\leansource{}` command, `subverso_render.py`)
  - Needs investigation into running SubVerso in a post-processing phase instead of during linting

## Configuration

### Using Local Forks (Development)

**lakefile.toml** in General_Crystallographic_Restriction:
```toml
[[require]]
name = "LeanArchitect"
path = "/Users/eric/GitHub/LeanArchitect"
```

**leanblueprint** installed via pipx:
```bash
pipx install -e /Users/eric/GitHub/leanblueprint
```

### Using GitHub (Production)

**lakefile.toml**:
```toml
[[require]]
name = "LeanArchitect"
git = "https://github.com/e-vergo/LeanArchitect"
rev = "main"
```

**leanblueprint** from PyPI:
```bash
pipx install leanblueprint
```

## Build Script

The `scripts/build_blueprint.sh` handles the full workflow:
1. Builds LeanArchitect and pushes changes
2. Pushes leanblueprint changes and ensures local fork is installed
3. Updates lake dependencies and fetches mathlib cache
4. Builds Lean project and blueprint data
5. Pushes main project changes
6. Builds blueprint PDF and web
7. Launches local server

## Debugging Tips

### Check if \leanposition appears in .tex files
```bash
grep -r "leanposition" .lake/build/blueprint/module/
```

### Check if lean-source-panel appears in HTML
```bash
grep -l "lean-source-panel" blueprint/web/*.html
```

### Verify leanblueprint is using local fork
```bash
pipx list | grep leanblueprint
# Should show path to /Users/eric/GitHub/leanblueprint
```

### Check plasTeX command parsing
Add debug prints in `blueprint.py`:
```python
def digest(self, tokens):
    Command.digest(self, tokens)
    import sys
    print(f"DEBUG: leanposition parsed, parentNode={self.parentNode}", file=sys.stderr)
```

### Common Issues

1. **leanposition not in HTML**: Check if it's INSIDE the environment in .tex files
2. **Wrong GitHub URLs**: Check path conversion in make_lean_data()
3. **Template not rendering**: Check if Thms.jinja2s is being loaded from leanblueprint package
4. **Old code being used**: Run `pipx uninstall leanblueprint && pipx install -e /path/to/fork`

## Files Modified

### LeanArchitect
- `lakefile.lean` - SubVerso dependency
- `Architect/Basic.lean` - NodeWithPos.highlightedCode field, extension
- `Architect/Highlighting.lean` - Linter (disabled)
- `Architect/Output.lean` - \leanposition inside environment

### leanblueprint
- `leanblueprint/subverso_render.py` - New file
- `leanblueprint/Packages/blueprint.py` - Commands, template, processing
- `leanblueprint/Packages/renderer_templates/Thms.jinja2s` - New file
- `leanblueprint/Packages/renderer_templates/blueprint.jinja2s` - Command registration
- `leanblueprint/static/blueprint.css` - Styling

### General_Crystallographic_Restriction
- `lakefile.toml` - Local LeanArchitect path
- `scripts/build_blueprint.sh` - Full build workflow

## Future Work

1. **Re-enable SubVerso highlighting**: Investigate running in post-processing phase
2. **Configurable GitHub branch**: Currently hardcoded to 'main'
3. **Collapsible source panels**: CSS/JS for toggle
4. **Syntax highlighting for plain text fallback**: Use a Lean syntax highlighter library
