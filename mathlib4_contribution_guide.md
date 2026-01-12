# Comprehensive Guide to High-Quality Mathlib4 Contributions

This document synthesizes official Mathlib documentation and community practices to provide a complete reference for contribution standards.

---

## Part I: Explicit Standards

### 1. Naming Conventions

#### 1.1 Capitalization Rules

| Category | Convention | Example |
|----------|------------|---------|
| Terms of `Prop`s (proofs, theorem names) | `snake_case` | `succ_ne_zero`, `mul_comm` |
| `Prop`s and `Type`s (structures, classes) | `UpperCamelCase` | `OneHom`, `IsTopologicalRing` |
| Functions | Same as return type | Function `A → B → C` named like term of `C` |
| Other terms of `Type`s | `lowerCamelCase` | `toFun`, `hPow` |
| UpperCamelCase inside snake_case | `lowerCamelCase` | `MonoidHom.toOneHom_injective` |
| Acronyms (LE, NE) | Grouped upper/lower | `LE.trans`, `neZero_iff` |

#### 1.2 Symbol Dictionary

**Logic:**
- `∨` → `or`
- `∧` → `and`  
- `→` → `of` / `imp` (conclusion first, hypotheses often omitted)
- `↔` → `iff`
- `¬` → `not`
- `∃` → `exists`
- `∀` → `all` / `forall`
- `=` → `eq` (often omitted)
- `≠` → `ne`

**Sets:**
- `∈` → `mem`
- `∪` → `union`
- `∩` → `inter`
- `⋃` → `iUnion` / `biUnion`
- `\` → `sdiff`
- `ᶜ` → `compl`

**Algebra:**
- `0` → `zero`
- `+` → `add`
- `-` → `neg` (unary) / `sub` (binary)
- `1` → `one`
- `*` → `mul`
- `^` → `pow`
- `/` → `div`
- `•` → `smul`
- `⁻¹` → `inv`

**Lattices:**
- `<` → `lt` / `gt`
- `≤` → `le` / `ge`
- `⊔` → `sup`
- `⊓` → `inf`
- `⊥` → `bot`
- `⊤` → `top`

#### 1.3 Special Naming Patterns

**le/ge and lt/gt usage:**
- Use `ge`/`gt` when arguments to `≤`/`<` appear swapped
- Use `ge`/`gt` to match argument order of another relation
- Use `ge`/`gt` when second argument is "more variable"

**Structural lemmas:**
- Extensionality: `.ext` (with `@[ext]` attribute), `.ext_iff` for biconditional
- Injectivity: `f_injective` for `Function.Injective f`, `f_inj` for bidirectional `f x = f y ↔ x = y`
- Induction: `T.induction_on` (value first) vs `T.induction` (constructions first)
- Recursion: `T.recOn` (value first) vs `T.rec` (constructions first)

**Hypotheses naming:**
- Use `of` to separate hypotheses from conclusion
- List hypotheses in order they appear (NOT reverse order)
- Example: `A → B → C` becomes `C_of_A_of_B`

**Abbreviations:**
- `pos` for `zero_lt`
- `neg` for `lt_zero`
- `nonpos` for `le_zero`
- `nonneg` for `zero_le`

---

### 2. Formatting Requirements

#### 2.1 Line Length
- Maximum 100 characters per line
- VS Code shows a visual marker at this limit

#### 2.2 Indentation Rules

**Theorem statements:**
```lean
-- Multi-line statement: indent subsequent lines by 4 spaces
theorem le_induction {P : Nat → Prop} {m}
    (h0 : P m) (h1 : ∀ n, m ≤ n → P n → P (n + 1)) :
    ∀ n, m ≤ n → P n := by
  -- Proof indented by 2 spaces (NOT 6 = 4 + 2)
  apply Nat.le.rec
  · exact h0
  · exact h1 _
```

**Key formatting rules:**
- Spaces on both sides of `:`, `:=`, and infix operators
- Put operators before line breaks, not at start of next line
- `by` at end of line preceding tactic block, never on its own line
- Focus dots `·` not indented; focused content indented
- No orphaned parentheses

#### 2.3 Whitespace and Delimiters

- Prefer `<|` over `$` (disallowed in Mathlib)
- Space after binders: `∀ α : Type, ∀ x : α, ...`
- Space after left arrow in rewrites: `rw [← add_comm a b]`
- Prefer `↦` over `=>` for anonymous functions (but `fun` keyword, not `λ`)
- No empty lines inside declarations (linter enforces this)

#### 2.4 Tactic Mode Formatting

```lean
-- Good: focusing dots with indented content
theorem example : ... := by
  cases x
  · simp [h]  -- Focus dot not indented
    ring      -- Content indented
  · rfl

-- Multiple tactics on one line: use semicolons sparingly
-- Good for single mathematical idea:
cases bla; clear h
induction n; simp
rw [foo]; simp_rw [bar]
```

---

### 3. Documentation Standards

#### 3.1 File Header Structure

```lean
/-
Copyright (c) 2024 Author Name. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Author Name
-/
import Mathlib.Data.Nat.Basic
import Mathlib.Algebra.Group.Defs

/-!
# Title of the File

Summary of contents.

## Main definitions

- `definition_name`: Description.

## Main results

- `theorem_name`: The **Important Theorem** states that...

## Notation

- `|_|` : The barrification operator.

## Implementation notes

Description of design decisions.

## References

See [Author2024] for details.

## Tags

keyword1, keyword2
-/
```

#### 3.2 Docstrings

- Required for all definitions (`docBlame` linter enforces)
- Encouraged for important theorems
- Use `/-- ... -/` delimiters
- No indentation on subsequent lines
- Use backticks for Lean declarations
- Fully qualified names become links in docs
- Named theorems should be **bold faced**

```lean
/-- If `q ≠ 0`, the `p`-adic norm of a rational `q` is `p ^ (-padicValRat p q)`.
If `q = 0`, the `p`-adic norm of `q` is `0`. -/
def padicNorm (p : ℕ) (q : ℚ) : ℚ := ...
```

#### 3.3 Sectioning Comments

Use `/-! ... -/` for section headers (appears in generated docs):
```lean
/-! ### Declarations about `BinderInfo` -/
```

---

### 4. Import Organization

- Imports immediately after copyright header, no blank line
- One import per line
- Use `#find_home` to verify declaration placement
- Avoid importing more than necessary (especially Analysis into Algebra)
- Consider splitting files if new imports create undesirable dependencies

---

### 5. Deprecation and Backward Compatibility

```lean
-- Renamed declaration: use deprecated alias
theorem new_name : ... := ...
@[deprecated (since := "YYYY-MM-DD")] alias old_name := new_name

-- No direct replacement: add explanation
@[deprecated "Use ... with ... instead" (since := "YYYY-MM-DD")]
theorem old_theorem ...

-- With to_additive: two deprecations needed
@[deprecated (since := "YYYY-MM-DD")] alias AddGroup_foo := AddGroup_bar
@[to_additive existing, deprecated (since := "YYYY-MM-DD")] alias Group_foo := Group_bar
```

- Named instances do not require deprecations
- Deprecated declarations can be deleted after 6 months

---

## Part II: Implicit Quality Factors

### 6. Proof Style Preferences

#### 6.1 Term Mode vs Tactic Mode

**When to use term mode:**
- Short, direct proofs
- When the proof term is naturally readable
- Simple applications of existing lemmas
- Pattern matching proofs

```lean
-- Good term mode
theorem succ_pos : ∀ n : Nat, 0 < succ n := zero_lt_succ

def square (x : Nat) : Nat := x * x
```

**When to use tactic mode:**
- Complex multi-step proofs
- Proofs requiring case analysis, induction
- When intermediate goals clarify the proof
- When tactics like `simp`, `ring`, `linarith` are appropriate

```lean
-- Good tactic mode
theorem continuous_example : Continuous (uncurry f) := by
  apply continuous_iff_continuousAt.2
  rintro ⟨a, x⟩
  change map _ _ ≤ _
  rw [nhds_prod_eq, nhds_discrete, Filter.map_pure_prod]
  exact (hf a).continuousAt
```

#### 6.2 Calculational Proofs

```lean
-- Preferred style for interchangeable lines
theorem reverse_reverse : ∀ (l : List α), reverse (reverse l) = l
  | []     => rfl
  | a :: l => calc
        reverse (reverse (a :: l))
    _ = reverse (reverse l ++ [a]) := by rw [reverse_cons]
    _ = reverse [a] ++ reverse (reverse l) := reverse_append _ _
    _ = reverse [a] ++ l := by rw [reverse_reverse l]
    _ = a :: l := rfl
```

#### 6.3 Simp Lemmas: Squeezing Policy

**Do NOT squeeze terminal simp calls** unless:
- Performance is particularly poor
- The proof breaks otherwise

Reasons:
1. Squeezed simp drowns important lemmas in basic ones
2. Squeezed simp breaks when lemmas are renamed
3. Terminal simp is followed only by flexible tactics (`ring`, `field_simp`, `aesop`)

---

### 7. Proof Readability and Maintainability

#### 7.1 Interspersed Comments

For complex proofs, add comments explaining the strategy:

```lean
theorem instSecondCountableTopology : SecondCountableTopology GHSpace := by
  refine secondCountable_of_countable_discretization fun δ δpos => ?_
  let ε := 2 / 5 * δ
  -- for each `p`, `s p` is a finite `ε`-dense subset of `p.Rep`
  choose s hs using this
  -- cardinality of the nice finite subset `s p`
  let N := fun p : GHSpace => Nat.card (s p)
  ...
```

#### 7.2 Avoid Long Standalone Proofs

- Split into supporting lemmas
- Each lemma should have a clear purpose
- Consider if a different structure simplifies the argument

#### 7.3 Use Better Tactics

**Before:**
```lean
have ha' := mul_le_mul_of_nonneg_left ha (inv_pos.2 hab).le
rwa [MulZeroClass.mul_zero, ← div_eq_inv_mul] at ha'
```

**After:**
```lean
positivity
```

**Good tactic choices:**
- `gcongr` for congruence with inequalities
- `positivity` for positivity goals
- `ring`, `field_simp`, `linarith` for algebraic manipulation
- `simp` with key lemmas, not over-specified

---

### 8. Lemma Granularity

#### 8.1 When to Split

- When a step has independent value
- When the same argument appears multiple times
- When the proof exceeds ~30-50 lines
- When a step would benefit from a clear name

#### 8.2 When to Inline

- Truly trivial steps
- Steps unlikely to be reused
- When splitting would obscure the main argument

#### 8.3 Auxiliary Lemma Naming

Use `aux` suffix and document restricted scope:
```lean
/-- Auxiliary lemma for `main_theorem`. Not intended for use outside this file. -/
theorem main_theorem_aux : ... := ...
```

---

### 9. API Design Philosophy

#### 9.1 Good API Characteristics

- **Completeness**: Provide rewrite lemmas for common patterns
- **Discoverability**: Follow naming conventions strictly
- **Composability**: Work well with existing abstractions
- **Appropriate attributes**: `@[simp]`, `@[ext]`, `@[gcongr]` where warranted

#### 9.2 Simp Normal Forms

Mathlib fixes canonical forms for equivalent expressions:
- `s.Nonempty` preferred over `s ≠ ∅`
- `(a : Option α)` preferred over `some a`
- `0 < n` preferred for "nonzero natural"

For `⊥ < x` vs `x ≠ ⊥`:
- Use `hne : x ≠ ⊥` in **assumptions** (easier to provide)
- Use `hlt : ⊥ < x` in **conclusions** (more powerful result)

#### 9.3 Transparency and Definitions

- Default is `semireducible` (via `def`)
- Use `abbrev` for `reducible` definitions
- Avoid `irreducible` unless profiling demonstrates need
- For sealed APIs, use structure wrappers:
```lean
structure myDef where
  underlying : underlyingTerm
```

- `erw` or `rfl` after `simp`/`rw` indicates missing API

#### 9.4 Instance Design

- Check for diamonds (non-defeq or non-propeq)
- Use `where` syntax for instances
- Provide `inferInstanceAs` bridges when needed:
```lean
instance : Foo myDef := inferInstanceAs (Foo underlyingTermOfMyDef)
```

---

### 10. Evaluating "Mathematical Taste"

#### 10.1 Generality vs Specialization

**Prefer generality when:**
- More general version uses existing Mathlib concepts
- No significant proof complexity increase
- Future use cases are foreseeable

**Prefer specialization when:**
- General version requires new abstractions
- Specialized version is significantly simpler
- The general case isn't mathematically natural

#### 10.2 Definition Quality

- Avoid unnecessary dependent types
- Prefer subtypes over custom inductive types when possible
- Example: `Vector` as subtype of `List` with length constraint

#### 10.3 Fit with Library Design

**Morphism design:**
- Use bundled morphisms with `FunLike` API
- Follow established patterns for morphism classes

**Subobject design:**
- Use bundled subobjects with `SetLike` API
- Follow existing subobject hierarchies

---

### 11. Common Rejection Reasons

#### 11.1 Style Violations
- Incorrect naming conventions
- Line length > 100 characters
- Missing docstrings
- Improper indentation

#### 11.2 Location Issues
- Declaration in wrong file
- Import hierarchy problems
- Result already exists (possibly more general)

#### 11.3 Quality Issues
- Proof too long/complex without splitting
- Missing API lemmas for new definitions
- Poor tactic choices (using `erw` when `rw` should work)
- Non-terminal `simp` without `only`

#### 11.4 Design Issues
- Introducing unnecessary diamonds
- Not following bundled morphism/subobject patterns
- Insufficient generality without justification
- Missing `@[simp]`/`@[ext]` attributes

#### 11.5 Performance Issues
- Using `Type _` instead of `Type*`
- Expensive tactics without justification
- Not benchmarking PRs that touch instances/simp lemmas

---

### 12. Review Process Expectations

#### 12.1 PR Requirements
- Informative title and description
- Small, self-contained changes preferred
- Run `lake build` locally before submitting
- Check linters pass

#### 12.2 Reviewer Considerations
1. **Style**: Formatting, naming, PR description
2. **Documentation**: Docstrings, cross-references, proof sketches
3. **Location**: File placement, import appropriateness
4. **Improvements**: Better tactics, structure, readability
5. **Library integration**: API quality, future needs, design fit

---

## Quick Reference: Pre-Submission Checklist

- [ ] Naming follows conventions (capitalization + symbol dictionary)
- [ ] Lines ≤ 100 characters
- [ ] Proper indentation (4 for continuation, 2 for proof body)
- [ ] All definitions have docstrings
- [ ] Module docstring with required sections
- [ ] No unnecessary imports
- [ ] `#find_home` confirms placement
- [ ] Appropriate attributes (`@[simp]`, `@[ext]`, etc.)
- [ ] No `Type _` (use `Type*`)
- [ ] Terminal simp not squeezed
- [ ] Complex proofs have explanatory comments
- [ ] New definitions have basic API lemmas
- [ ] Benchmarked if touching instances/simp lemmas

---

## References

- [Style Guide](https://leanprover-community.github.io/contribute/style.html)
- [Naming Conventions](https://leanprover-community.github.io/contribute/naming.html)
- [Documentation Style](https://leanprover-community.github.io/contribute/doc.html)
- [PR Review Guide](https://leanprover-community.github.io/contribute/pr-review.html)
- [Simp Guide](https://leanprover-community.github.io/extras/simp.html)
