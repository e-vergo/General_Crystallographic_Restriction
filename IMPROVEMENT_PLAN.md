# Crystallographic Restriction - Improvement Plan

**Date:** 2026-01-16
**Scope:** Code quality improvements and Mathlib readiness (excluding LeanArchitect infrastructure)

> **Note:** This repo uses LeanArchitect for blueprint generation. The `import Architect` and `@[blueprint ...]` annotations are intentional and will be stripped only at final Mathlib PR submission time.

---

## 1. Mathlib Duplicate Verification & Replacement

Four lemmas were identified as potential duplicates of existing Mathlib API. These should be verified and replaced.

### 1.1 `coprime_of_irreducible_not_dvd` (Forward.lean:113-117)
**Current:**
```lean
lemma coprime_of_irreducible_not_dvd {p q : ℚ[X]} (hirr : Irreducible p)
    (hndvd : ¬p ∣ q) : IsCoprime p q :=
  (EuclideanDomain.dvd_or_coprime p q hirr).resolve_left hndvd
```
**Mathlib equivalent:** `Irreducible.coprime_iff_not_dvd`
**Action:** Verify API exists, replace with `hirr.coprime_iff_not_dvd.mpr hndvd`

### 1.2 `factorization_support_disjoint` (Psi/Basic.lean:177-194)
**Current:** Custom proof that coprime numbers have disjoint factorization supports
**Mathlib equivalent:** `Nat.Coprime.disjoint_primeFactors` + `Nat.support_factorization`
**Action:** Verify and replace with:
```lean
simp only [Nat.support_factorization]
exact h.disjoint_primeFactors
```

### 1.3 `sum_le_prod_of_ge_two` (Psi/Bounds.lean:50-51)
**Current:**
```lean
theorem sum_le_prod_of_ge_two {a b : ℕ} (ha : 2 ≤ a) (hb : 2 ≤ b) : a + b ≤ a * b :=
  Nat.add_le_mul ha hb
```
**Mathlib equivalent:** Direct use of `Nat.add_le_mul`
**Action:** Remove wrapper, use `Nat.add_le_mul` directly at call sites

### 1.4 `reindexMonoidEquiv` (FiniteOrder/Basic.lean:146-153)
**Current:** Custom `MulEquiv` for reindexing matrices
**Mathlib:** Check if `Matrix.reindexAlgEquiv` or similar exists with multiplicative structure
**Action:** Search Mathlib for existing API, generalize if no exact match exists

---

## 2. Naming Convention Fixes

### 2.1 Pattern: `_imp_` → `_of_`
Mathlib uses `conclusion_of_hypothesis` pattern, not `hypothesis_imp_conclusion`.

| File | Current | Proposed |
|------|---------|----------|
| Companion/Cyclotomic.lean:86 | `cyclotomic_dvd_X_pow_sub_one_imp_dvd` | `dvd_of_cyclotomic_dvd_X_pow_sub_one` |

### 2.2 Pattern: `_ge_two` → `two_le_`
Mathlib uses prefix for the bound, not suffix.

| File | Current | Proposed |
|------|---------|----------|
| Main/Lemmas.lean:154 | `totient_ge_two_of_gt_two` | `two_le_totient_of_two_lt` |
| Psi/Bounds.lean:40 | `totient_primePow_ge_two` | `two_le_totient_primePow` |
| Psi/Bounds.lean:386 | `finset_nonempty_of_lcm_ge_two` | `Finset.nonempty_of_two_le_lcm` |
| Psi/Bounds.lean:391 | `exists_gt_one_of_lcm_ge_two` | `Finset.exists_one_lt_of_two_le_lcm` |

### 2.3 Other Naming Issues

| File | Current | Proposed | Reason |
|------|---------|----------|--------|
| Companion/Cyclotomic.lean:54 | `minpoly_companion_cyclotomic_eq` | `companion_cyclotomic_minpoly` | Group with other `companion_cyclotomic_*` lemmas |
| Main/Lemmas.lean:117 | `primePow_mem_of_lcm_eq` | `Finset.prime_pow_mem_of_lcm_eq` | Namespace + snake_case |

---

## 3. Type Generalization

Three definitions are over-specialized to `ℤ` but could work for arbitrary types.

### 3.1 `reindexMonoidEquiv` (FiniteOrder/Basic.lean:146-153)
**Current:** `Matrix m m ℤ ≃* Matrix n n ℤ`
**Generalize to:** `Matrix m m R ≃* Matrix n n R` for `[Monoid R]`

### 3.2 `embedMatrixSum` (FiniteOrder/Basic.lean)
**Current:** Specialized to `ℤ`
**Generalize to:** Any `[Zero R] [One R]`

### 3.3 `blockDiag2` (FiniteOrder/Basic.lean)
**Current:** Specialized to `ℤ`
**Generalize to:** Any `[Zero R]`

---

## 4. Execution Checklist

### Phase 1: Duplicate Verification (Priority: High)
- [ ] Search Mathlib for `Irreducible.coprime_iff_not_dvd` - verify exact signature
- [ ] Search Mathlib for `Nat.Coprime.disjoint_primeFactors` - verify exists
- [ ] Confirm `Nat.add_le_mul` has same signature as `sum_le_prod_of_ge_two`
- [ ] Search Mathlib for `Matrix.reindex*` multiplicative equivalences

### Phase 2: Duplicate Replacement
- [ ] Replace `coprime_of_irreducible_not_dvd` usage in Forward.lean
- [ ] Replace `factorization_support_disjoint` in Psi/Basic.lean
- [ ] Inline `Nat.add_le_mul` at call sites, remove wrapper
- [ ] Handle `reindexMonoidEquiv` based on search results

### Phase 3: Naming Fixes
- [ ] Rename `cyclotomic_dvd_X_pow_sub_one_imp_dvd` → `dvd_of_cyclotomic_dvd_X_pow_sub_one`
- [ ] Rename `totient_ge_two_of_gt_two` → `two_le_totient_of_two_lt`
- [ ] Rename `totient_primePow_ge_two` → `two_le_totient_primePow`
- [ ] Rename `finset_nonempty_of_lcm_ge_two` → `Finset.nonempty_of_two_le_lcm`
- [ ] Rename `exists_gt_one_of_lcm_ge_two` → `Finset.exists_one_lt_of_two_le_lcm`
- [ ] Rename `minpoly_companion_cyclotomic_eq` → `companion_cyclotomic_minpoly`
- [ ] Rename `primePow_mem_of_lcm_eq` → `Finset.prime_pow_mem_of_lcm_eq`
- [ ] Update all call sites for each rename

### Phase 4: Type Generalization
- [ ] Generalize `reindexMonoidEquiv` to `[Monoid R]`
- [ ] Generalize `embedMatrixSum` to `[Zero R] [One R]`
- [ ] Generalize `blockDiag2` to `[Zero R]`
- [ ] Update dependent code and verify compilation

### Phase 5: Verification
- [ ] Run `lake build` - ensure no errors
- [ ] Run Lean LSP diagnostics on all files
- [ ] Spot-check that renamed lemmas are found correctly

---

## 5. Proof Enhancements

Opportunities for proof simplification, API extraction, and code quality improvements identified during compliance review.

### 5.1 API Extraction

Inline definitions that should become standalone for reusability.

| File | Current Code | Proposed | Priority |
|------|--------------|----------|----------|
| FiniteOrder/Order.lean:48-52 | Inline `MonoidHom` for `blockDiag2` in `orderOf_blockDiag2` | Extract `blockDiag2.prodMonoidHom` to Basic.lean | Medium |

**Details:**
```lean
-- Current (inline in orderOf_blockDiag2):
let φ : Matrix (Fin M) (Fin M) ℤ × Matrix (Fin K) (Fin K) ℤ →*
    Matrix (Fin M ⊕ Fin K) (Fin M ⊕ Fin K) ℤ :=
  { toFun := fun p => blockDiag2 p.1 p.2
    map_one' := blockDiag2_one
    map_mul' := fun p q => blockDiag2_mul _ _ _ _ }

-- Proposed (in Basic.lean):
def blockDiag2.prodMonoidHom (M K : ℕ) :
    Matrix (Fin M) (Fin M) ℤ × Matrix (Fin K) (Fin K) ℤ →*
    Matrix (Fin M ⊕ Fin K) (Fin M ⊕ Fin K) ℤ where
  toFun := fun p => blockDiag2 p.1 p.2
  map_one' := blockDiag2_one
  map_mul' := fun p q => blockDiag2_mul _ _ _ _
```

### 5.2 Proof Simplifications

Verbose proofs that can use more concise Mathlib patterns.

| File | Location | Current | Proposed | Priority |
|------|----------|---------|----------|----------|
| FiniteOrder/Basic.lean:57-61 | `one_mem_integerMatrixOrders` | `use 1; constructor; exact orderOf_one; norm_num` | `⟨1, orderOf_one, by norm_num⟩` | Low |
| FiniteOrder/Basic.lean:133-140 | `integerMatrixOrders_subset_sum` | Multi-line with `obtain`, `use`, `constructor` | `fun _ ⟨A, hA_ord, hA_pos⟩ => ⟨embedMatrixSum A, by rw [...], hA_pos⟩` | Low |
| FiniteOrder/Order.lean:68-83 | `lcm_mem_integerMatrixOrders` | Multi-line with bullets | Use `refine` with anonymous constructors | Low |
| Backward.lean:74-81 | `permMatrix_pow` base case | `simp only [pow_zero]; exact permMatrix_one` | `simp [permMatrix_one]` | Low |
| Psi/Basic.lean:121-122 | Two consecutive `simp only` calls | `simp only [psiPrimePow, hk.ne']; simp only [ite_false]` | Combine into single `simp only` | Low |

### 5.3 Redundant Code Removal

Trivial wrappers and unnecessary `have` statements.

| File | Location | Issue | Action | Priority |
|------|----------|-------|--------|----------|
| FiniteOrder/Order.lean:57 | `have hφ : φ (A, B) = blockDiag2 A B := rfl` | Definitionally true, used once | Inline or remove | Low |
| Backward.lean:162-174 | `order_one_achievable`, `order_two_achievable` | Trivial wrappers around `*_mem_integerMatrixOrders` | Consider removing, use originals directly | Low |
| Main/Lemmas.lean:155-156 | Multiple anonymous `have this` statements | Shadows identifiers | Name hypotheses: `hpos`, `hne` | Low |

### 5.4 Tactic Modernization

Old patterns that have cleaner alternatives.

| File | Location | Current | Proposed | Priority |
|------|----------|---------|----------|----------|
| Psi/Basic.lean:129+ | `simp only [show (3 : ℕ) ≠ 2 by decide, ...]` | Inline `show ... by decide` | Use `native_decide` or `norm_num` directly | Medium |
| Backward.lean:428 | `rcases hNm with h \| hN_pos <;> [omega; skip]` | Unusual compound tactic | Use `cases ... with \| inl => omega \| inr => ...` | Low |
| Psi/Bounds.lean:388 | `simp_all` | Generally discouraged in Mathlib | Replace with explicit `simp` calls | Medium |

### 5.5 Private Lemma Decisions

Private lemmas that should be exposed, inlined, or documented.

| File | Lemmas | Recommendation | Priority |
|------|--------|----------------|----------|
| Companion/Basic.lean | 12 private lemmas (lines 79-517) | Either expose with proper names/docs OR inline if truly single-use | Medium |
| Backward.lean:198-271 | Private helpers for odd/coprime cases | Add brief docstrings even for private lemmas | Low |
| Psi/Bounds.lean:262 | `nontrivialPrimes` (abbrev) | Either mark `private` or develop proper API | Low |

### 5.6 Missing Attributes

Lemmas that should have `@[simp]` for automation.

| File | Lemma | Current | Recommended | Priority |
|------|-------|---------|-------------|----------|
| Companion/Basic.lean:572 | `companion_aeval_eq_zero` | No attribute | Add `@[simp]` | Medium |
| Psi/Basic.lean:66 | `psiPrimePow_zero` | No attribute | Add `@[simp]` | Medium |
| FiniteOrder/Basic.lean:96-100 | `embedMatrixSum_mul` | No attribute | Consider `@[simp]` | Low |
| FiniteOrder/Basic.lean:203-207 | `blockDiag2_mul` | No attribute | Consider `@[simp]` | Low |

### 5.7 Long Proof Splitting

Proofs over ~30 lines that could be factored into helper lemmas.

| File | Lemma | Lines | Suggestion | Priority |
|------|-------|-------|------------|----------|
| Companion/Cyclotomic.lean:136-169 | `companion_cyclotomic_orderOf` | 33 lines | Extract `m ∣ k ∧ k < m → False` step | Low |
| Forward.lean:130-163 | `minpoly_eq_prod_cyclotomic_of_dvd_X_pow_sub_one` | 33 lines | Factor into `cyclotomic_divisors_filter`, `minpoly_dvd_prod_cyclotomic` | Low |
| Psi/Bounds.lean:167-222 | `psi_le_totient` | 55 lines | Extract "composite without 2^1 factor" case | Medium |
| Main/Lemmas.lean:117-143 | `primePow_mem_of_lcm_eq` | 26 lines | Consider extracting helper lemmas | Low |

### 5.8 General-Purpose Lemmas for Upstream

Lemmas general enough to contribute to Mathlib independently.

| File | Lemma | Target Location | Priority |
|------|-------|-----------------|----------|
| Backward.lean:56-147 | `permMatrix_one`, `permMatrix_mul`, `permMatrix_pow`, `permMatrix_eq_one_iff`, `orderOf_permMatrix` | `Mathlib.LinearAlgebra.Matrix.Permutation` | High |
| Psi/Bounds.lean:40 | `totient_primePow_ge_two` (renamed) | `Mathlib.Data.Nat.Totient` | Medium |
| Psi/Bounds.lean:386,391 | `finset_nonempty_of_lcm_ge_two`, `exists_gt_one_of_lcm_ge_two` | `Mathlib.Algebra.GCDMonoid.Finset` | Medium |
| Main/Lemmas.lean:54 | `Finset.sum_le_prod_of_all_ge_two` | `Mathlib.Algebra.BigOperators.Order` | Medium |
| Main/Lemmas.lean:208 | `Nat.totient_finset_prod_of_coprime` | `Mathlib.Data.Nat.Totient` | Medium |
| Forward.lean:44-83 | `Matrix.pow_eq_one_of_minpoly_dvd_X_pow_sub_one`, `Matrix.minpoly_dvd_X_pow_sub_one_of_pow_eq_one` | `Mathlib.LinearAlgebra.Matrix.Charpoly.Minpoly` | High |

### 5.9 Namespace Issues

Declarations in wrong namespace needing correction.

| File | Location | Issue | Fix | Priority |
|------|----------|-------|-----|----------|
| Main/Lemmas.lean:54,84,169,208 | `Finset.*`, `Nat.*` in `Crystallographic` namespace | Creates `Crystallographic.Finset.*` | Close namespace, reopen correct namespace | Medium |
| Psi/Bounds.lean | Redundant `Crystallographic.` prefix within namespace | `Crystallographic.psi m` inside `Crystallographic` namespace | Remove redundant qualifications | Low |
| Backward.lean | Same redundant prefix issue | `Crystallographic.psi (p ^ k)` | Remove prefix | Low |

---

## 6. Files Affected

| File | Duplicates | Naming | Generalization | Proof Enhancements |
|------|------------|--------|----------------|-------------------|
| Companion/Basic.lean | - | - | - | Private lemmas, missing `@[simp]` |
| Companion/Cyclotomic.lean | - | 2 | - | Long proof splitting |
| FiniteOrder/Basic.lean | 1 | - | 3 | Proof simplifications, missing `@[simp]` |
| FiniteOrder/Order.lean | - | - | - | API extraction, redundant code |
| Psi/Basic.lean | 1 | - | - | Tactic modernization, missing `@[simp]` |
| Psi/Bounds.lean | 1 | 2 | - | Long proofs, tactic issues, namespace |
| Forward.lean | 1 | - | - | Upstream candidates |
| Backward.lean | - | - | - | Proof simplification, upstream candidates |
| Main/Lemmas.lean | - | 2 | - | Namespace issues, redundant code |
| Main/MainTheorem.lean | - | - | - | (clean, no enhancements needed) |
