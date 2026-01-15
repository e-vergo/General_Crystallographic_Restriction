# Mathlib Submission Plan

Analysis of lemmas/theorems from the Crystallographic Restriction project that are candidates for Mathlib submission.

## Selection Criteria

- General-purpose (not specific to crystallographic restriction)
- No dependencies on project-specific definitions
- Fit naturally in existing Mathlib modules

---

## Tier 1: Directly Mathlib-ready (no project dependencies)

### `Mathlib.Data.Nat.Totient`

| Lemma | Location | Description |
|-------|----------|-------------|
| `totient_ge_two_of_gt_two` | `Main/Lemmas.lean:154` | φ(n) ≥ 2 for n > 2 |
| `Nat.totient_finset_prod_of_coprime` | `Main/Lemmas.lean:216` | φ(∏ f(a)) = ∏ φ(f(a)) for pairwise coprime |
| `totient_primePow_ge_two` | `Psi/Bounds.lean:40` | φ(p^k) ≥ 2 unless (p,k) = (2,1) |

### `Mathlib.Algebra.Order.BigOperators.Group.Finset`

| Lemma | Location | Description |
|-------|----------|-------------|
| `Finset.sum_le_prod_of_all_ge_two` | `Main/Lemmas.lean:54` | ∑ f(x) ≤ ∏ f(x) when all f(x) ≥ 2 |

### `Mathlib.Data.Nat.Factorization.Basic`

| Lemma | Location | Description |
|-------|----------|-------------|
| `factorization_support_disjoint` | `Psi/Basic.lean:183` | Coprime numbers have disjoint factorization supports |
| `factorization_split_lt` | `Psi/Bounds.lean:73` | Factor composite m = p^e * m' with bounds |

### `Mathlib.Algebra.GCDMonoid.Finset` or `Mathlib.Data.Nat.GCD.BigOperators`

| Lemma | Location | Description |
|-------|----------|-------------|
| `Finset.lcm_factorization_le_sup` | `Main/Lemmas.lean:84` | (S.lcm f).factorization q ≤ S.sup (factorization q) |
| `Finset.prod_coprime_dvd` | `Main/Lemmas.lean:177` | Pairwise coprime divisors: ∏ f(a) ∣ d |

### `Mathlib.Algebra.Order.Ring.Nat`

| Lemma | Location | Description |
|-------|----------|-------------|
| `sum_le_prod_of_ge_two` | `Psi/Bounds.lean:55` | a + b ≤ a * b for a, b ≥ 2 |

---

## Tier 2: Permutation matrix infrastructure

### `Mathlib.LinearAlgebra.Matrix.Permutation`

| Lemma | Location | Description |
|-------|----------|-------------|
| `Equiv.Perm.permMatrix_one` | `Backward.lean:54` | (1).permMatrix = 1 |
| `Equiv.Perm.permMatrix_mul` | `Backward.lean:61` | (σ * τ).permMatrix = τ.permMatrix * σ.permMatrix |
| `Equiv.Perm.permMatrix_pow` | `Backward.lean:68` | (σ^k).permMatrix = (σ.permMatrix)^k |
| `Equiv.Perm.permMatrix_eq_one_iff` | `Backward.lean:80` | σ.permMatrix = 1 ↔ σ = 1 |
| `Equiv.Perm.orderOf_permMatrix` | `Backward.lean:107` | orderOf (σ.permMatrix) = orderOf σ |

### `Mathlib.GroupTheory.Perm.Fin`

| Lemma | Location | Description |
|-------|----------|-------------|
| `Equiv.Perm.orderOf_finRotate` | `Backward.lean:132` | orderOf (finRotate n) = n for n ≥ 2 |

---

## Tier 3: Companion matrix infrastructure (significant contribution)

### New file: `Mathlib.LinearAlgebra.Matrix.Companion`

| Definition/Theorem | Location | Description |
|-------|----------|-------------|
| `companion` | `Companion/Basic.lean:69` | Companion matrix of a monic polynomial |
| `companion_charpoly` | `Companion/Basic.lean:496` | charpoly(companion p) = p |
| `companion_aeval_eq_zero` | `Companion/Basic.lean:568` | p(companion p) = 0 (Cayley-Hamilton) |
| `companion_pow_eq_one_of_dvd` | `Companion/Basic.lean:583` | If p ∣ X^m - 1, then companion(p)^m = 1 |

---

## Tier 4: Block diagonal matrix order

### `Mathlib.Data.Matrix.Block` or `Mathlib.GroupTheory.OrderOfElement`

| Lemma | Location | Description |
|-------|----------|-------------|
| `orderOf_blockDiag2` | `FiniteOrder/Order.lean:43` | orderOf (blockDiag A B) = lcm(orderOf A, orderOf B) |
| `ringChar_matrix_int` | `FiniteOrder/Basic.lean:64` | ringChar (Matrix (Fin N) (Fin N) ℤ) = 0 for N ≥ 1 |

---

## Recommended Submission Order

### Phase 1: Small self-contained lemmas
- `totient_ge_two_of_gt_two`
- `factorization_support_disjoint`
- `Finset.sum_le_prod_of_all_ge_two`
- `sum_le_prod_of_ge_two`

### Phase 2: Totient multiplicativity
- `Nat.totient_finset_prod_of_coprime`
- `Finset.prod_coprime_dvd`

### Phase 3: Permutation matrix lemmas
- Check if variants exist in Mathlib first
- `orderOf_permMatrix`
- `orderOf_finRotate`

### Phase 4: Companion matrix infrastructure
- Larger contribution worth a dedicated PR
- Includes definition and key theorems

---

## Pre-submission Checklist

For each lemma before submission:
- [ ] Check Mathlib for existing versions or near-duplicates
- [ ] Verify naming follows Mathlib conventions
- [ ] Remove `@[blueprint]` attributes
- [ ] Update namespace to match target Mathlib location
- [ ] Ensure imports are minimal
- [ ] Add appropriate docstrings
- [ ] Run Mathlib linter
