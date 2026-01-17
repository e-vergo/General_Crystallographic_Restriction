Summary
The side-by-side Lean code display feature is now working. Here's what was implemented:

LeanArchitect Changes (/Users/eric/GitHub/LeanArchitect/)
lakefile.lean: Added SubVerso dependency
Basic.lean: Added highlightedCode field to NodeWithPos and extension for storing highlighted code
Highlighting.lean: Created linter for capturing highlighted code (currently disabled due to SubVerso panic issues)
Output.lean: Moved \leanposition{} command INSIDE theorem/definition environments so plasTeX attaches it to the correct node
leanblueprint Changes (/Users/eric/GitHub/leanblueprint/)
subverso_render.py: Created new module for converting SubVerso JSON to HTML
Packages/blueprint.py:
Added leansource and leanposition Command classes
Added LEAN_SOURCE_TPL Jinja2 template
Added logic to convert absolute paths to relative paths for GitHub permalinks
Added fallback to read source files directly when SubVerso highlighting isn't available
Packages/renderer_templates/Thms.jinja2s: Created custom template that renders thm_body_extras_tpl after theorem content
static/blueprint.css: Added CSS for .lean-source-panel styling
Current State
Working: GitHub permalinks, source code display (plain text without highlighting)
Disabled: SubVerso semantic highlighting (causes panic "unexpected context-free info tree node")
The blueprint now shows Lean source code alongside each theorem/definition with a "View on GitHub" link
Configuration
The test project's lakefile.toml is configured to use the local LeanArchitect fork:


[[require]]
name = "LeanArchitect"
path = "/Users/eric/GitHub/LeanArchitect"
To switch back to GitHub for production, change it back to:


[[require]]
name = "LeanArchitect"
git = "https://github.com/e-vergo/LeanArchitect"
rev = "main"