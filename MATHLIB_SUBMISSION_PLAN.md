# Mathlib Submission Plan

Analysis of lemmas/theorems from the Crystallographic Restriction project that are candidates for Mathlib submission.

## Selection Criteria

- General-purpose (not specific to crystallographic restriction)
- No dependencies on project-specific definitions
- Fit naturally in existing Mathlib modules

---

## Submission Process

### Before Starting
1. Discuss the contribution on Zulip (`#mathlib4` channel)
2. Confirm the material is within Mathlib's scope
3. Identify potential reviewers
4. Create GitHub account and link to Zulip profile

### During Submission
1. Fork mathlib4 repository
2. Create branch from master
3. Make small, focused PRs (one lemma or closely related set)
4. Run `lake exe mk_all` if creating new files
5. Submit PR with proper title format (see PR conventions below)

### After Submission
1. Monitor CI status
2. Respond to review comments promptly
3. Remove `awaiting-author` label after addressing feedback
4. Use `lake exe cache get` after CI passes

---

## Tier 1: Directly Mathlib-ready (no project dependencies)

### `Mathlib.Data.Nat.Totient`

| Lemma | Location | Description |
|-------|----------|-------------|
| `totient_ge_two_of_gt_two` | `Main/Lemmas.lean:154` | phi(n) >= 2 for n > 2 |
| `Nat.totient_finset_prod_of_coprime` | `Main/Lemmas.lean:216` | phi(prod f(a)) = prod phi(f(a)) for pairwise coprime |
| `totient_primePow_ge_two` | `Psi/Bounds.lean:40` | phi(p^k) >= 2 unless (p,k) = (2,1) |

**Naming notes:**
- Verify if `two_le_totient_of_two_lt` pattern is preferred over `totient_ge_two_of_gt_two`
- Check existing totient lemma naming patterns in Mathlib

### `Mathlib.Algebra.Order.BigOperators.Group.Finset`

| Lemma | Location | Description |
|-------|----------|-------------|
| `Finset.sum_le_prod_of_all_ge_two` | `Main/Lemmas.lean:54` | sum f(x) <= prod f(x) when all f(x) >= 2 |

**Naming notes:**
- Long name - verify "of_all" pattern is acceptable
- Consider if more general statement exists

### `Mathlib.Data.Nat.Factorization.Basic`

| Lemma | Location | Description |
|-------|----------|-------------|
| `factorization_support_disjoint` | `Psi/Basic.lean:183` | Coprime numbers have disjoint factorization supports |
| `factorization_split_lt` | `Psi/Bounds.lean:73` | Factor composite m = p^e * m' with bounds |

### `Mathlib.Algebra.GCDMonoid.Finset` or `Mathlib.Data.Nat.GCD.BigOperators`

| Lemma | Location | Description |
|-------|----------|-------------|
| `Finset.lcm_factorization_le_sup` | `Main/Lemmas.lean:84` | (S.lcm f).factorization q <= S.sup (factorization q) |
| `Finset.prod_coprime_dvd` | `Main/Lemmas.lean:177` | Pairwise coprime divisors: prod f(a) dvd d |

### `Mathlib.Algebra.Order.Ring.Nat`

| Lemma | Location | Description |
|-------|----------|-------------|
| `sum_le_prod_of_ge_two` | `Psi/Bounds.lean:55` | a + b <= a * b for a, b >= 2 |

---

## Tier 2: Permutation matrix infrastructure

### `Mathlib.LinearAlgebra.Matrix.Permutation`

| Lemma | Location | Description |
|-------|----------|-------------|
| `Equiv.Perm.permMatrix_one` | `Backward.lean:54` | (1).permMatrix = 1 |
| `Equiv.Perm.permMatrix_mul` | `Backward.lean:61` | (sigma * tau).permMatrix = tau.permMatrix * sigma.permMatrix |
| `Equiv.Perm.permMatrix_pow` | `Backward.lean:68` | (sigma^k).permMatrix = (sigma.permMatrix)^k |
| `Equiv.Perm.permMatrix_eq_one_iff` | `Backward.lean:80` | sigma.permMatrix = 1 <-> sigma = 1 |
| `Equiv.Perm.orderOf_permMatrix` | `Backward.lean:107` | orderOf (sigma.permMatrix) = orderOf sigma |

**Pre-submission check:** Search Mathlib for existing `permMatrix` API - these may already exist or have variants.

### `Mathlib.GroupTheory.Perm.Fin`

| Lemma | Location | Description |
|-------|----------|-------------|
| `Equiv.Perm.orderOf_finRotate` | `Backward.lean:132` | orderOf (finRotate n) = n for n >= 2 |

---

## Tier 3: Companion matrix infrastructure (significant contribution)

### New file: `Mathlib.LinearAlgebra.Matrix.Companion`

| Definition/Theorem | Location | Description |
|-------|----------|-------------|
| `companion` | `Companion/Basic.lean:69` | Companion matrix of a monic polynomial |
| `companion_charpoly` | `Companion/Basic.lean:496` | charpoly(companion p) = p |
| `companion_aeval_eq_zero` | `Companion/Basic.lean:568` | p(companion p) = 0 (Cayley-Hamilton) |
| `companion_pow_eq_one_of_dvd` | `Companion/Basic.lean:583` | If p dvd X^m - 1, then companion(p)^m = 1 |

**Considerations:**
- Creating a new file requires module docstring with full structure
- Consider splitting into multiple PRs:
  - PR 1: Definition + basic lemmas
  - PR 2: `companion_charpoly` and Cayley-Hamilton
  - PR 3: Root of unity implications
- Decide on transparency: `reducible`, `semireducible`, or `irreducible`
- Design complete API with convenience lemmas

---

## Tier 4: Block diagonal matrix order

### `Mathlib.Data.Matrix.Block` or `Mathlib.GroupTheory.OrderOfElement`

| Lemma | Location | Description |
|-------|----------|-------------|
| `orderOf_blockDiag2` | `FiniteOrder/Order.lean:43` | orderOf (blockDiag A B) = lcm(orderOf A, orderOf B) |
| `ringChar_matrix_int` | `FiniteOrder/Basic.lean:64` | ringChar (Matrix (Fin N) (Fin N) Z) = 0 for N >= 1 |

---

## Recommended Submission Order

### Phase 1: Small self-contained lemmas (1-2 lemmas per PR)
- `totient_ge_two_of_gt_two`
- `factorization_support_disjoint`
- `Finset.sum_le_prod_of_all_ge_two`
- `sum_le_prod_of_ge_two`

### Phase 2: Totient multiplicativity
- `Nat.totient_finset_prod_of_coprime`
- `Finset.prod_coprime_dvd`

### Phase 3: Permutation matrix lemmas
- First: Search Mathlib using `exact?`, Loogle, LeanSearch
- If not present: `orderOf_permMatrix`, `orderOf_finRotate`

### Phase 4: Companion matrix infrastructure
- Split into 2-3 focused PRs as described in Tier 3

---

## Pre-submission Checklist

For each lemma before submission:

### Search & Verification
- [ ] Search Mathlib for existing versions (`exact?`, `apply?`, Loogle, LeanSearch)
- [ ] Use `#find_home` to verify correct file location
- [ ] Verify no problematic new imports are introduced

### Naming & Style
- [ ] Verify naming follows Mathlib conventions (capitalization, symbol names)
- [ ] Use American English spelling
- [ ] Line length under 100 characters
- [ ] Proper spacing around operators (`: `, `:= `, etc.)
- [ ] Variables follow conventions (`alpha`, `beta` for types, `h` for hypotheses, etc.)
- [ ] Hypotheses left of colon where appropriate

### Documentation
- [ ] Add docstring explaining mathematical meaning
- [ ] Include cross-references to related declarations
- [ ] Add proof sketch comments for complex proofs
- [ ] If formalizing from literature, add `docs/references.bib` entry
- [ ] For new files: add module docstring (title, summary, notation, references, tags)
- [ ] For new files: add copyright header with author information

### Code Quality
- [ ] Remove `@[blueprint]` attributes
- [ ] Update namespace to match target Mathlib location
- [ ] Ensure imports are minimal
- [ ] Consider appropriate attributes (`@[simp]`, `@[ext]`, `@[gcongr]`)
- [ ] Run `#lint` at end of file
- [ ] For new definitions: decide on transparency level

### PR Preparation
- [ ] Prepare PR title: `feat(<scope>): <description>`
- [ ] Draft PR description with motivation
- [ ] Use `Closes #xxx` for related issues if applicable
- [ ] Format dependencies: `- [ ] depends on: #XXXX`

---

## PR Title Format

Use the format: `<type>(<scope>): <subject>`

Examples for this project:
- `feat(Data/Nat/Totient): add totient_ge_two_of_gt_two`
- `feat(Algebra/Order/BigOperators): add sum_le_prod for terms >= 2`
- `feat(LinearAlgebra/Matrix): add companion matrix definition`

Types: `feat`, `fix`, `refactor`, `perf`, `doc`, `chore`

---

## Style Requirements Summary

From Mathlib style guide:

- **Line length**: 100 characters max
- **Indentation**: 2 spaces
- **Spacing**: space after `:`, before and after `:=`
- **Variables**: `u`, `v` for universes; `alpha`, `beta` for types; `h` prefix for hypotheses
- **Language**: American English
- **Instances**: prefer `where` syntax
- **Arguments**: hypotheses left of colon when possible

---

## Documentation Requirements

### Module Docstrings (for new files)

```lean
/-!
# Title

Summary of contents.

## Main declarations

* `foo`: description
* `bar`: description

## Notation

* `notation`: meaning

## References

* [Author, *Title*][citation_key]

## Tags

tag1, tag2
-/
```

### Copyright Header (for new files)

```lean
/-
Copyright (c) 2024 Author Name. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Author Name
-/
```

### Declaration Docstrings

- Explain mathematical meaning, not just type signature
- Use backticks for code references
- Use LaTeX for mathematical notation where helpful
- Include cross-references: `see also `RelatedLemma``

---

## Open Questions

- [ ] Confirm `permMatrix` lemmas don't already exist in Mathlib
- [ ] Verify preferred naming pattern for totient bounds
- [ ] Determine if companion matrix is significant enough for dedicated file vs. extending existing
- [ ] Identify Mathlib reviewers familiar with these areas
