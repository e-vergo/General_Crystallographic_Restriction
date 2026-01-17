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

### `Mathlib.LinearAlgebra.Matrix.Charpoly.Minpoly` (NEW from refactoring)

| Lemma | Location | Description |
|-------|----------|-------------|
| `Matrix.pow_eq_one_of_minpoly_dvd_X_pow_sub_one` | `Forward.lean:48-72` | If minpoly A divides X^k - 1, then A^k = 1 |
| `Matrix.minpoly_dvd_X_pow_sub_one_of_pow_eq_one` | `Forward.lean:74-81` | If A^m = 1, then minpoly A divides X^m - 1 |

**Notes:**
- These are general matrix lemmas extracted during proof refactoring
- Already in `Matrix` namespace, ready for Mathlib
- Fundamental connection between minpoly and finite order

### `Mathlib.RingTheory.Polynomial.Cyclotomic.Basic` (NEW from refactoring)

| Lemma | Location | Description |
|-------|----------|-------------|
| `cyclotomic_dvd_X_pow_sub_one_imp_dvd` | `Cyclotomic.lean:107-149` | If cyclotomic m divides X^k - 1, then m divides k |

**Notes:**
- Check if this already exists in Mathlib (likely candidate for `exact?`)
- Useful characterization of when cyclotomic polynomials divide X^k - 1

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
| `finset_nonempty_of_lcm_ge_two` | `Psi/Bounds.lean:400-405` | S.lcm id ≥ 2 → S.Nonempty (NEW from Phase 2) |

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

### Phase 2: Matrix/minpoly lemmas (NEW - high value)
- `Matrix.pow_eq_one_of_minpoly_dvd_X_pow_sub_one`
- `Matrix.minpoly_dvd_X_pow_sub_one_of_pow_eq_one`
- These form a natural pair connecting minpoly to finite order

### Phase 3: Totient multiplicativity
- `Nat.totient_finset_prod_of_coprime`
- `Finset.prod_coprime_dvd`

### Phase 4: Cyclotomic lemma
- First check if `cyclotomic_dvd_X_pow_sub_one_imp_dvd` exists
- If not: submit as part of cyclotomic API

### Phase 5: Permutation matrix lemmas
- First: Search Mathlib using `exact?`, Loogle, LeanSearch
- If not present: `orderOf_permMatrix`, `orderOf_finRotate`

### Phase 6: Companion matrix infrastructure
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
- [ ] Check if `cyclotomic_dvd_X_pow_sub_one_imp_dvd` exists in Mathlib

---

## Refactoring Completed (January 2026)

Long proofs were broken into helper lemmas to improve readability and enable reuse:

### Forward.lean: `psi_le_of_mem_integerMatrixOrders`
- **Before**: ~170 lines
- **After**: ~42 lines
- **Extracted**:
  - `Matrix.pow_eq_one_of_minpoly_dvd_X_pow_sub_one` (Mathlib candidate)
  - `Matrix.minpoly_dvd_X_pow_sub_one_of_pow_eq_one` (Mathlib candidate)
  - `minpoly_eq_prod_cyclotomic_of_dvd_X_pow_sub_one`
  - `cyclotomic_divisors_lcm_eq_of_orderOf`

### Cyclotomic.lean: `companion_cyclotomic_orderOf`
- **Before**: ~150 lines
- **After**: ~33 lines
- **Extracted**:
  - `minpoly_companion_cyclotomic_eq`
  - `cyclotomic_dvd_X_pow_sub_one_imp_dvd` (Mathlib candidate)

### Bounds.lean: `sum_totient_ge_psi_of_lcm_eq`
- **Before**: ~140 lines
- **After**: Simplified structure
- **Extracted**:
  - `nontrivialPrimes` (abbreviation)
  - `psi_eq_sum_nontrivial_totients`
  - `sum_nontrivial_totients_le_sum_totients`

### Basic.lean: `companion_charpoly_minor00_det`
- **Before**: ~132 lines
- **After**: ~44 lines
- **Extracted**:
  - `companion_minor00_entry_eq`

### Backward.lean: `mem_integerMatrixOrders_of_psi_le`
- **Before**: ~105 lines
- **After**: ~31 lines
- **Extracted**:
  - `mem_integerMatrixOrders_small`
  - `mem_integerMatrixOrders_five`
  - `mem_integerMatrixOrders_of_psi_le_large`

### Backward.lean: `mem_integerMatrixOrders_psi`
- **Before**: ~82 lines
- **After**: ~66 lines (modularized)
- **Extracted**:
  - `mem_integerMatrixOrders_psi_2_times_odd`
  - `mem_integerMatrixOrders_psi_odd_times_2`
  - `mem_integerMatrixOrders_psi_composite`

---

## Refactoring Completed Phase 2 (January 2026)

Additional refactoring to reduce remaining long proofs:

### Companion/Basic.lean: `companion_charpoly_minor10_det`
- **Before**: 127 lines
- **After**: 32 lines (75% reduction)
- **Extracted**:
  - `companion_minor10_row0_entry` - Row 0 structure in minor
  - `companion_subminor_entry` - Subminor entry pattern
  - `companion_subminor_det` - Subminor determinant calculation

### Companion/Basic.lean: `companion_minor00_entry_eq`
- **Before**: 107 lines
- **After**: 26 lines (76% reduction)
- **Extracted**:
  - `Minor00IndexConds` (structure) - Bundles 12 index condition equivalences
  - `mkMinor00IndexConds` - Constructor proving all conditions

### Psi/Bounds.lean: `sum_totient_ge_psi_of_lcm_eq`
- **Before**: 82 lines
- **After**: 40 lines (51% reduction)
- **Extracted**:
  - `totient_sum_ge_psi_of_mem` - Base case when m ∈ S
  - `finset_nonempty_of_lcm_ge_two` (Mathlib candidate) - S nonempty from lcm ≥ 2
  - `exists_gt_one_of_lcm_ge_two` - ∃d ∈ S with d > 1

### Backward.lean: `mem_integerMatrixOrders_psi` (further refined)
- **Before**: 68 lines
- **After**: 40 lines (41% reduction)
- **Extracted**:
  - `odd_ne_two_ge_three_of_coprime_two` - Derives Odd, ≠2, ≥3 from coprimality
  - `primePow_odd_ge_three_of_coprime_two` - Prime power properties from coprimality

### Forward.lean: `minpoly_eq_prod_cyclotomic_of_dvd_X_pow_sub_one`
- **Before**: 62 lines
- **After**: 34 lines (45% reduction)
- **Extracted**:
  - `coprime_of_irreducible_not_dvd` - General coprimality from irreducibility
  - `cyclotomic_coprime_minpoly_of_not_mem` - Cyclotomic/minpoly coprimality
- **Used Mathlib**: `Finset.prod_filter_mul_prod_filter_not`

### Companion/Basic.lean: `companion_charpoly`
- **Before**: 61 lines
- **After**: 22 lines (64% reduction)
- **Extracted**:
  - `companion_laplace_two_terms` - Laplace expansion to 2 terms
- **Used Mathlib**: `Polynomial.X_mul_divX_add`

### Phase 2 Summary

| Proof | Original | Refactored | Reduction |
|-------|----------|------------|-----------|
| `companion_charpoly_minor10_det` | 127 | 32 | 75% |
| `companion_minor00_entry_eq` | 107 | 26 | 76% |
| `sum_totient_ge_psi_of_lcm_eq` | 82 | 40 | 51% |
| `mem_integerMatrixOrders_psi` | 68 | 40 | 41% |
| `minpoly_eq_prod_cyclotomic` | 62 | 34 | 45% |
| `companion_charpoly` | 61 | 22 | 64% |

**New Mathlib candidates identified:**
- `finset_nonempty_of_lcm_ge_two` - General Finset.lcm property

**Existing Mathlib lemmas utilized:**
- `Finset.prod_filter_mul_prod_filter_not` - Product decomposition over filter
- `Polynomial.X_mul_divX_add` - Polynomial identity p = X * divX + C(coeff 0)

---

## Compliance Review Results (2026-01-16)

Comprehensive review of all project files against Mathlib submission standards.

### File-by-File Status

| File | Score | Critical | Required | Suggested |
|------|-------|----------|----------|-----------|
| `Companion/Basic.lean` | 74/100 | 2 | 8 | 10 |
| `Companion/Cyclotomic.lean` | 72/100 | 2 | 5 | 5 |
| `FiniteOrder/Basic.lean` | 65/100 | 3 | 5 | 9 |
| `FiniteOrder/Order.lean` | 75/100 | 2 | 3 | 5 |
| `Psi/Basic.lean` | 70/100 | 2 | 7 | 7 |
| `Psi/Bounds.lean` | 78/100 | 2 | 6 | 9 |
| `CrystallographicRestriction/Forward.lean` | 75/100 | 1 | 5 | 7 |
| `CrystallographicRestriction/Backward.lean` | 78/100 | 1 | 7 | 6 |
| `Main/MainTheorem.lean` | 80/100 | 2 | 3 | 5 |
| `Main/Lemmas.lean` | 70/100 | 2 | 6 | 7 |

**Average Score: 73.7/100**

### Blocking Issues (Must Fix Before Submission)

All files share two universal blocking issues that must be resolved first:

#### 1. Non-Mathlib Import: `Architect`
**Affected:** ALL 10 files
**Issue:** Every file imports `Architect`, a project-specific blueprint documentation tool not recognized by Mathlib.
**Fix:** Remove `import Architect` from all files.

#### 2. Custom Blueprint Attributes
**Affected:** ALL 10 files
**Issue:** All theorems and definitions use `@[blueprint ...]` attributes for documentation generation. These are not Mathlib-compatible.
**Fix:** Remove all `@[blueprint ...]` attributes. Convert meaningful documentation content into standard `/-- ... -/` docstrings.

#### 3. Potential Mathlib Duplicates
**Affected:** Multiple files
| Lemma | Location | Mathlib Equivalent |
|-------|----------|-------------------|
| `coprime_of_irreducible_not_dvd` | `Forward.lean:113-117` | `Irreducible.coprime_iff_not_dvd` |
| `factorization_support_disjoint` | `Psi/Basic.lean:177-194` | `Nat.Coprime.disjoint_primeFactors` + `Nat.support_factorization` |
| `sum_le_prod_of_ge_two` | `Psi/Bounds.lean:50-51` | `Nat.add_le_mul` |
| `reindexMonoidEquiv` | `FiniteOrder/Basic.lean:146-153` | Verify against `Matrix.reindex*` variants |

### Required Fixes Summary

#### Naming Convention Violations

| Current Name | Suggested Name | File |
|--------------|----------------|------|
| `cyclotomic_dvd_X_pow_sub_one_imp_dvd` | `dvd_of_cyclotomic_dvd_X_pow_sub_one` | `Cyclotomic.lean` |
| `minpoly_companion_cyclotomic_eq` | `companion_cyclotomic_minpoly` | `Cyclotomic.lean` |
| `totient_ge_two_of_gt_two` | `Nat.two_le_totient_of_two_lt` | `Main/Lemmas.lean` |
| `totient_primePow_ge_two` | `two_le_totient_primePow` | `Psi/Bounds.lean` |
| `psi_pos_of_odd_ge_three` | `psi_pos_of_three_le_of_odd` | `Psi/Bounds.lean` |
| `finset_nonempty_of_lcm_ge_two` | `Finset.nonempty_of_two_le_lcm` | `Psi/Bounds.lean` |
| `primePow_mem_of_lcm_eq` | `Finset.prime_pow_mem_of_lcm_eq` | `Main/Lemmas.lean` |

#### Namespace Issues
- **`Main/Lemmas.lean`**: Lemmas prefixed with `Finset.` or `Nat.` are incorrectly placed inside `Crystallographic` namespace
- **`Companion/Basic.lean`**: Namespace should be `Polynomial.Companion` or `Matrix.Companion`, not `Crystallographic`
- **Multiple files**: Redundant `Crystallographic.` qualification within the namespace

#### Documentation Deficiencies
- **Missing docstrings:** ~15 declarations across files lack proper `/-- ... -/` docstrings
- **Docstring formatting:** Several use improper indentation or missing backticks around Lean terms
- **Module documentation:** Some files have redundant or inconsistent section headers

#### Private Lemmas
**Affected:** `Companion/Basic.lean` (12 private lemmas)
**Issue:** Mathlib generally discourages `private` lemmas. Consider exposing with proper names or inlining.

#### Type Generalization Needed
| Definition | Current Type | Should Generalize To |
|------------|--------------|---------------------|
| `reindexMonoidEquiv` | `Matrix m m ℤ` | `Matrix m m R` for any `Monoid R` |
| `embedMatrixSum` | `Matrix (Fin M) (Fin M) ℤ` | Any `Zero R, One R` |
| `blockDiag2` | `Matrix (Fin M) (Fin M) ℤ` | Any `Zero R, One R` |

#### Missing `@[simp]` Attributes
- `psiPrimePow_zero` (`Psi/Basic.lean`)
- `embedMatrixSum_mul` (`FiniteOrder/Basic.lean`)
- `blockDiag2_mul` (`FiniteOrder/Basic.lean`)
- `companion_aeval_eq_zero` (`Companion/Basic.lean`)

### Tier Readiness Assessment

#### Tier 1: Directly Mathlib-ready
**Status: MODERATE WORK NEEDED**
- All lemmas require removal of `Architect` import and `@[blueprint]` attributes
- ~4 lemmas are duplicates of existing Mathlib API
- Naming convention fixes needed for ~5 lemmas
- After fixes: Ready for submission in 1-2 lemma PRs

| Lemma | Readiness | Blocker |
|-------|-----------|---------|
| `Matrix.pow_eq_one_of_minpoly_dvd_X_pow_sub_one` | HIGH | Blueprint removal only |
| `Matrix.minpoly_dvd_X_pow_sub_one_of_pow_eq_one` | HIGH | Blueprint removal only |
| `totient_ge_two_of_gt_two` | MEDIUM | Naming, docstring |
| `Nat.totient_finset_prod_of_coprime` | MEDIUM | Namespace, docstring |
| `factorization_support_disjoint` | LOW | May be duplicate |
| `sum_le_prod_of_ge_two` | LOW | Is `Nat.add_le_mul` |

#### Tier 2: Permutation matrix infrastructure
**Status: HIGH - MINIMAL WORK**
- File: `Backward.lean` lines 56-147
- Score: 78/100
- Main blockers: `Architect` import, blueprint attributes
- Pre-submission: Verify these don't exist in Mathlib's `permMatrix` API
- After fixes: Ready for single PR

#### Tier 3: Companion matrix infrastructure
**Status: MODERATE WORK NEEDED**
- File: `Companion/Basic.lean` (607 lines)
- Score: 74/100
- Significant contribution requiring namespace restructuring
- 12 private lemmas need decisions (expose or inline)
- Recommended: Split into 2-3 PRs
- After fixes: Substantial but high-value contribution

#### Tier 4: Block diagonal matrix order
**Status: MODERATE WORK NEEDED**
- Files: `FiniteOrder/Basic.lean`, `FiniteOrder/Order.lean`
- Scores: 65/100, 75/100
- Type generalization needed for several definitions
- After fixes: Ready for submission

### Priority Action Items

1. **CRITICAL (Week 1):**
   - Remove `import Architect` from all 10 files
   - Remove all `@[blueprint ...]` attributes
   - Delete duplicate lemmas (`coprime_of_irreducible_not_dvd`, `sum_le_prod_of_ge_two`)

2. **REQUIRED (Week 2):**
   - Fix naming conventions (7 lemmas)
   - Move declarations to correct namespaces
   - Add missing docstrings (~15 declarations)
   - Generalize type parameters where noted

3. **RECOMMENDED (Week 3+):**
   - Decide fate of 12 private lemmas in `Companion/Basic.lean`
   - Add missing `@[simp]` attributes
   - Consider proof compressions and style improvements

### Estimated Timeline to Submission-Ready

| Tier | Current Score | Work Estimate | Target Score |
|------|---------------|---------------|--------------|
| Tier 1 | 70-78 | 2-3 hours | 90+ |
| Tier 2 | 78 | 1-2 hours | 90+ |
| Tier 3 | 74 | 4-6 hours | 85+ |
| Tier 4 | 65-75 | 3-4 hours | 85+ |

**Total estimated effort:** 10-15 hours of cleanup work before first PR submission
