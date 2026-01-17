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
