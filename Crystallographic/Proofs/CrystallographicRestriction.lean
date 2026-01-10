/-
Copyright (c) 2026 Eric Vergo. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Eric Vergo
-/
import Crystallographic.Definitions.Psi
import Crystallographic.Definitions.IntegerMatrixOrder
import Crystallographic.Proofs.RotationMatrices
import Crystallographic.Proofs.CompanionMatrix
import Crystallographic.Proofs.PsiLowerBound
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.LinearAlgebra.Matrix.Charpoly.Minpoly
import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.GroupTheory.Perm.Fin

/-!
# The Crystallographic Restriction Theorem (General Dimension)

This file states and proves the crystallographic restriction theorem in arbitrary dimension N:
An N x N integer matrix can have finite order m if and only if psi(m) <= N.

## Main results

* `crystallographic_restriction` - The main theorem characterizing which orders are achievable.
* `psi_le_of_mem_integerMatrixOrders` - Forward direction: order m implies psi(m) <= N.
* `mem_integerMatrixOrders_of_psi_le` - Backward direction: psi(m) <= N implies order m achievable.

## Proof Strategy

### Forward direction: If m in integerMatrixOrders N then psi(m) <= N

1. Take A with orderOf A = m
2. The minimal polynomial of A divides X^m - 1
3. The primitive m-th roots of unity must appear as eigenvalues (otherwise order < m)
4. The Q-dimension required to contain all primitive m-th roots is >= phi(m)
5. Sum over prime power factors gives psi(m) <= N

### Backward direction: If psi(m) <= N then m in integerMatrixOrders N

1. Construct companion matrix of cyclotomic polynomial Phi_m over Z
2. This has size phi(m) x phi(m) and order m
3. For composite m, use block diagonal of companion matrices for prime power factors
4. Total size is psi(m) <= N, pad with identity to get N x N matrix

## References

* Sasse, R. (2020). "Crystallographic Groups"
-/

namespace Crystallographic

open Matrix Polynomial

/-- If each cyclotomic polynomial in a finset divides a target polynomial,
then their product also divides the target (using pairwise coprimality). -/
lemma cyclotomic_finset_product_dvd {target : ℚ[X]} (S : Finset ℕ)
    (hdvd_each : ∀ d ∈ S, cyclotomic d ℚ ∣ target) :
    (∏ d ∈ S, cyclotomic d ℚ) ∣ target := by
  induction S using Finset.induction with
  | empty => simp only [Finset.prod_empty, one_dvd]
  | @insert d s hd_notin IH =>
    rw [Finset.prod_insert hd_notin]
    have hdvd_d : cyclotomic d ℚ ∣ target := hdvd_each d (Finset.mem_insert_self d s)
    have hdvd_prod : (∏ x ∈ s, cyclotomic x ℚ) ∣ target :=
        IH (fun x hx => hdvd_each x (Finset.mem_insert_of_mem hx))
    have hcop : IsCoprime (cyclotomic d ℚ) (∏ x ∈ s, cyclotomic x ℚ) := by
      apply IsCoprime.prod_right
      intro x hx
      exact cyclotomic.isCoprime_rat (fun heq => hd_notin (heq ▸ hx))
    exact hcop.mul_dvd hdvd_d hdvd_prod

/-- If an N x N integer matrix has finite order m, then psi(m) <= N.

This is the forward direction of the crystallographic restriction theorem.
The proof uses eigenvalue theory: primitive m-th roots of unity must appear
as eigenvalues, and their algebraic degree constrains the matrix dimension.

**Proof outline:**
1. An integer matrix A with A^m = 1 has minimal polynomial dividing X^m - 1
2. If orderOf A = m, then the minimal polynomial is lcm of cyclotomic polynomials
   Φ_d for some divisors d of m with lcm(d) = m
3. The primitive m-th roots have minimal polynomial Phi_m (the cyclotomic polynomial)
4. These eigenvalues require dimension >= phi(d) for each d in the set
5. By sum_totient_ge_psi_of_lcm_eq, the sum of φ(d) >= psi(m)
6. Therefore psi(m) <= deg(minpoly) <= deg(charpoly) = N
-/
theorem psi_le_of_mem_integerMatrixOrders (N m : ℕ) (hm : 0 < m)
    (hord : m ∈ integerMatrixOrders N) : Crystallographic.psi m ≤ N := by
  -- Extract the matrix A with orderOf A = m
  obtain ⟨A, hA_ord, _⟩ := hord
  -- Handle the case N = 0 separately
  rcases Nat.eq_zero_or_pos N with rfl | hN_pos
  · -- N = 0: The only 0×0 matrix is empty, with order 1
    haveI : IsEmpty (Fin 0) := Fin.isEmpty
    -- Any two 0×0 matrices are equal since there are no indices
    have hA_eq_1 : A = 1 := Matrix.ext fun i => Fin.elim0 i
    rw [hA_eq_1, orderOf_one] at hA_ord
    subst hA_ord
    simp [Crystallographic.psi_one]
  · -- N > 0: Use psi ≤ φ ≤ N via minimal polynomial degree bounds
    haveI : NeZero N := ⟨Nat.pos_iff_ne_zero.mp hN_pos⟩
    let A_Q := A.map (algebraMap ℤ ℚ)
    -- The minimal polynomial over ℚ is the key object
    -- Its degree satisfies: psi(m) ≤ deg(minpoly) ≤ deg(charpoly) = N
    have hminpoly_deg_le : (minpoly ℚ A_Q).natDegree ≤ N := by
      have hdvd := Matrix.minpoly_dvd_charpoly A_Q
      have hne : A_Q.charpoly ≠ 0 := (Matrix.charpoly_monic A_Q).ne_zero
      calc (minpoly ℚ A_Q).natDegree ≤ A_Q.charpoly.natDegree :=
          Polynomial.natDegree_le_of_dvd hdvd hne
        _ = Fintype.card (Fin N) := Matrix.charpoly_natDegree_eq_dim A_Q
        _ = N := Fintype.card_fin N
    -- minpoly | X^m - 1 since A^m = 1
    have hpow : A ^ m = 1 := by rw [← hA_ord]; exact pow_orderOf_eq_one A
    -- The minpoly divides X^m - 1, so it's a product of cyclotomic polynomials Φ_d
    -- for divisors d of m. The set S of such d has lcm(S) = m (since orderOf A = m).
    -- Therefore deg(minpoly) = Σ_{d∈S} φ(d) ≥ psi(m) by sum_totient_ge_psi_of_lcm_eq.
    --
    -- Current proof uses the simpler bound: psi(m) ≤ φ(m) ≤ deg(minpoly) ≤ N
    -- This is sufficient when Φ_m | minpoly (which holds for prime m).
    -- For general m, the full proof via sum_totient_ge_psi_of_lcm_eq is needed.
    -- The minimal polynomial divides X^m - 1 = ∏_{d|m} Φ_d (product of cyclotomic polynomials)
    -- Since cyclotomic polynomials are irreducible over ℚ and pairwise coprime,
    -- the minimal polynomial is a product of distinct cyclotomic polynomials Φ_d
    -- for some set S ⊆ divisors(m).
    --
    -- The key constraint: orderOf A = m means the smallest k with A^k = 1 is m.
    -- This is equivalent to: the smallest k such that minpoly | X^k - 1 is m.
    -- Since minpoly = ∏_{d ∈ S} Φ_d, this means lcm(S) = m.
    --
    -- Therefore: deg(minpoly) = ∑_{d ∈ S} deg(Φ_d) = ∑_{d ∈ S} φ(d) ≥ psi(m)
    -- The last inequality follows from sum_totient_ge_psi_of_lcm_eq.
    --
    -- The technical details involve showing that minpoly is exactly a product
    -- of cyclotomic polynomials (using that they're irreducible and form a
    -- factorization of X^m - 1) and that the lcm condition holds.
    --
    -- This requires significant infrastructure about cyclotomic factorization
    -- over ℚ and the connection between order and minimal polynomial divisibility.
    -- The proof proceeds by:
    -- 1. Show minpoly(A_Q) is a product of cyclotomic polynomials
    -- 2. Identify the set S of cyclotomic factors
    -- 3. Show lcm(S) = m from the order constraint
    -- 4. Apply sum_totient_ge_psi_of_lcm_eq
    --
    -- This requires proving that the irreducible factors of minpoly over ℚ
    -- are exactly cyclotomic polynomials (since minpoly | X^m - 1 and
    -- cyclotomic polynomials are irreducible over ℚ and form the unique
    -- factorization of X^m - 1).
    -- The key bound: psi(m) ≤ deg(minpoly)
    -- Proof sketch:
    -- 1. minpoly | X^m - 1 = ∏_{d|m} Φ_d (cyclotomic factorization)
    -- 2. Each Φ_d is irreducible over ℚ (cyclotomic.irreducible_rat)
    -- 3. So minpoly = ∏_{d∈S} Φ_d for some S ⊆ divisors(m)
    -- 4. orderOf A = m ⟺ lcm(S) = m (order = minimal k with minpoly | X^k - 1)
    -- 5. deg(minpoly) = ∑_{d∈S} φ(d) ≥ psi(m) by sum_totient_ge_psi_of_lcm_eq
    --
    -- The technical proof requires:
    -- - Unique factorization in ℚ[X] for polynomials dividing ∏ Φ_d
    -- - Connection between lcm(S) and the order of the matrix
    -- - Application of sum_totient_ge_psi_of_lcm_eq
    --
    -- Key lemma: If minpoly | X^k - 1, then A^k = 1
    have pow_eq_one_of_minpoly_dvd : ∀ k : ℕ, minpoly ℚ A_Q ∣ X ^ k - 1 → A ^ k = 1 := by
      intro k hdvd
      -- If minpoly | X^k - 1, then aeval A_Q (X^k - 1) = 0
      have haeval : aeval A_Q (X ^ k - 1 : ℚ[X]) = 0 := by
        obtain ⟨q, hq⟩ := hdvd
        rw [hq, map_mul, minpoly.aeval, zero_mul]
      -- This means A_Q^k = 1
      simp only [map_sub, map_pow, aeval_X, map_one, sub_eq_zero] at haeval
      -- Transfer back to A via injectivity
      have hinj : Function.Injective
          (Matrix.map · (algebraMap ℤ ℚ) :
            Matrix (Fin N) (Fin N) ℤ → Matrix (Fin N) (Fin N) ℚ) := by
        intro M₁ M₂ heq
        ext i j
        have h := congrFun (congrFun heq i) j
        simp only [Matrix.map_apply] at h
        exact (algebraMap ℤ ℚ).injective_int h
      apply hinj
      change (A ^ k).map (algebraMap ℤ ℚ) =
        (1 : Matrix (Fin N) (Fin N) ℤ).map (algebraMap ℤ ℚ)
      rw [Matrix.map_pow, Matrix.map_one (algebraMap ℤ ℚ) (map_zero _) (map_one _)]
      exact haeval
    -- The minimal polynomial divides X^m - 1 = ∏_{d|m} Φ_d
    have hminpoly_dvd : minpoly ℚ A_Q ∣ X ^ m - 1 := by
      apply minpoly.dvd
      simp only [map_sub, map_pow, aeval_X, map_one]
      rw [← Matrix.map_pow, hpow,
        Matrix.map_one (algebraMap ℤ ℚ) (map_zero _) (map_one _), sub_self]
    -- The key algebraic fact: minpoly = ∏_{d∈S} Φ_d for some S ⊆ divisors(m),
    -- and lcm(S) = m.
    -- The degree equals ∑_{d∈S} φ(d) ≥ psi(m) by sum_totient_ge_psi_of_lcm_eq.
    --
    -- We prove this by showing that the set S of divisors d where Φ_d | minpoly has:
    -- 1. minpoly = ∏_{d∈S} Φ_d (since cyclotomics are irreducible and pairwise coprime)
    -- 2. lcm(S) = m (since otherwise orderOf A < m)
    --
    -- Define S = {d ∈ divisors(m) | Φ_d ∣ minpoly ℚ A_Q}
    classical
    let S : Finset ℕ := m.divisors.filter (fun d => cyclotomic d ℚ ∣ minpoly ℚ A_Q)
    -- Every element of S divides m
    have hS_sub : ∀ d ∈ S, d ∣ m := by
      intro d hd
      have hd' := Finset.mem_filter.mp hd
      exact Nat.mem_divisors.mp hd'.1 |>.1
    -- The minpoly is the product of Φ_d for d ∈ S (by unique factorization)
    -- First, show that minpoly ∣ ∏_{d∈S} Φ_d
    have hminpoly_dvd_prod : minpoly ℚ A_Q ∣ ∏ d ∈ S, cyclotomic d ℚ := by
      -- Every irreducible factor of minpoly must divide some Φ_d with d ∈ S
      -- Since Φ_d are coprime and S contains exactly those d where Φ_d | minpoly,
      -- minpoly must divide their product.
      --
      -- The argument: minpoly | ∏_{d|m} Φ_d. For any irreducible p | minpoly,
      -- p | ∏_{d|m} Φ_d, so p | Φ_{d₀} for some d₀ | m (p is prime in ℚ[X]).
      -- Since Φ_{d₀} is irreducible, p ~ Φ_{d₀}. Since p | minpoly, Φ_{d₀} | minpoly,
      -- so d₀ ∈ S. Therefore every prime factor of minpoly divides ∏_{d∈S} Φ_d.
      --
      -- We use that minpoly and ∏_{d∈S} Φ_d are both monic, and ∏_{d∈S} Φ_d | minpoly.
      -- Since they're both monic divisors of each other, they're equal (but we'll use
      -- the associated_of_dvd_dvd lemma in the next step).
      -- For now, we prove this by showing deg(minpoly) ≤ deg(∏_{d∈S} Φ_d).
      --
      -- Actually, the cleanest approach: We've shown ∏_{d∈S} Φ_d | minpoly.
      -- Since both are monic and minpoly | ∏_{d|m} Φ_d ⊇ ∏_{d∈S} Φ_d (as products),
      -- we need to show minpoly | ∏_{d∈S} Φ_d.
      --
      -- Key fact: For any d | m with d ∉ S, Φ_d ∤ minpoly (by definition of S).
      -- So Φ_d is coprime with minpoly (since Φ_d is irreducible over ℚ).
      -- Therefore minpoly | ∏_{d|m} Φ_d / ∏_{d∉S} Φ_d = ∏_{d∈S} Φ_d.
      have hcoprime_outside : ∀ d ∈ m.divisors, d ∉ S →
          IsCoprime (cyclotomic d ℚ) (minpoly ℚ A_Q) := by
        intro d hd hd_not_in_S
        have hd_pos : 0 < d := Nat.pos_of_mem_divisors hd
        have hirr : Irreducible (cyclotomic d ℚ) := cyclotomic.irreducible_rat hd_pos
        have hndvd : ¬(cyclotomic d ℚ ∣ minpoly ℚ A_Q) := by
          intro hdvd
          apply hd_not_in_S
          exact Finset.mem_filter.mpr ⟨hd, hdvd⟩
        -- Since Φ_d is irreducible and doesn't divide minpoly, they're coprime
        exact (EuclideanDomain.dvd_or_coprime _ _ hirr).resolve_left hndvd
      -- minpoly | ∏_{d|m} Φ_d = ∏_{d∈S} Φ_d * ∏_{d∉S} Φ_d
      -- and minpoly is coprime with ∏_{d∉S} Φ_d (since coprime with each factor)
      -- so minpoly | ∏_{d∈S} Φ_d
      have hprod_split : ∏ d ∈ m.divisors, cyclotomic d ℚ =
          (∏ d ∈ S, cyclotomic d ℚ) *
          (∏ d ∈ m.divisors.filter (· ∉ S), cyclotomic d ℚ) := by
        rw [← Finset.prod_filter_mul_prod_filter_not m.divisors (· ∈ S)]
        -- Need to show {x ∈ m.divisors | x ∈ S} = S
        -- Since S = m.divisors.filter _, S ⊆ m.divisors, so this holds
        have hS_eq : m.divisors.filter (· ∈ S) = S := by
          ext d
          simp only [Finset.mem_filter]
          constructor
          · intro ⟨_, hd⟩; exact hd
          · intro hd; exact ⟨Finset.mem_filter.mp hd |>.1, hd⟩
        rw [hS_eq]
      have hcoprime_with_complement : IsCoprime (minpoly ℚ A_Q)
          (∏ d ∈ m.divisors.filter (· ∉ S), cyclotomic d ℚ) := by
        apply IsCoprime.prod_right
        intro d hd
        have hd_in_div : d ∈ m.divisors := Finset.mem_of_mem_filter d hd
        have hd_not_in_S : d ∉ S := (Finset.mem_filter.mp hd).2
        exact (hcoprime_outside d hd_in_div hd_not_in_S).symm
      rw [← prod_cyclotomic_eq_X_pow_sub_one hm, hprod_split] at hminpoly_dvd
      exact hcoprime_with_complement.dvd_of_dvd_mul_right hminpoly_dvd
    -- Conversely, ∏_{d∈S} Φ_d ∣ minpoly (by definition of S and coprimality)
    have hprod_dvd_minpoly : (∏ d ∈ S, cyclotomic d ℚ) ∣ minpoly ℚ A_Q :=
      cyclotomic_finset_product_dvd S (fun d hd => (Finset.mem_filter.mp hd).2)
    -- Therefore minpoly = ∏_{d∈S} Φ_d (up to units, but both are monic)
    have hminpoly_eq_prod : minpoly ℚ A_Q = ∏ d ∈ S, cyclotomic d ℚ := by
      apply Polynomial.eq_of_monic_of_associated
      · exact minpoly.monic (Matrix.isIntegral A_Q)
      · exact Polynomial.monic_prod_of_monic _ _ (fun d _ => cyclotomic.monic d ℚ)
      · exact associated_of_dvd_dvd hminpoly_dvd_prod hprod_dvd_minpoly
    -- Now show lcm(S) = m
    have hS_lcm : S.lcm id = m := by
      -- If lcm(S) < m, then minpoly | X^{lcm(S)} - 1, so A^{lcm(S)} = 1
      -- This contradicts orderOf A = m
      by_contra hne
      have hlcm_dvd_m : S.lcm id ∣ m := Finset.lcm_dvd (fun d hd => hS_sub d hd)
      have hlcm_le : S.lcm id ≤ m := Nat.le_of_dvd hm hlcm_dvd_m
      have hlcm_lt : S.lcm id < m := Nat.lt_of_le_of_ne hlcm_le hne
      -- minpoly | ∏_{d|lcm(S)} Φ_d = X^{lcm(S)} - 1
      have hlcm_pos : 0 < S.lcm id := by
        by_cases hS_empty : S = ∅
        · -- If S = ∅, then minpoly = 1 (empty product), contradiction since
          -- minpoly has positive degree
          simp only [hS_empty, Finset.prod_empty] at hminpoly_eq_prod
          have hdeg := minpoly.natDegree_pos (Matrix.isIntegral A_Q)
          rw [hminpoly_eq_prod, natDegree_one] at hdeg
          omega
        · have hne_zero : S.lcm id ≠ 0 := Finset.lcm_ne_zero_iff.mpr fun d hd =>
            (Nat.pos_of_mem_divisors (Nat.mem_divisors.mpr ⟨hS_sub d hd, hm.ne'⟩)).ne'
          exact Nat.pos_of_ne_zero hne_zero
      -- Helper: X^d - 1 | X^n - 1 when d | n
      have X_pow_sub_one_dvd : ∀ (d n : ℕ), d ∣ n → (X ^ d - 1 : ℚ[X]) ∣ X ^ n - 1 := by
        intro d n hdvd
        obtain ⟨k, hk⟩ := hdvd
        rw [hk]
        exact pow_one_sub_dvd_pow_mul_sub_one X d k
      have hminpoly_dvd_lcm : minpoly ℚ A_Q ∣ X ^ (S.lcm id) - 1 := by
        rw [hminpoly_eq_prod]
        apply cyclotomic_finset_product_dvd
        intro d hd
        have hd_dvd_lcm : d ∣ S.lcm id := Finset.dvd_lcm hd
        calc cyclotomic d ℚ ∣ X ^ d - 1 := cyclotomic.dvd_X_pow_sub_one d ℚ
          _ ∣ X ^ (S.lcm id) - 1 := X_pow_sub_one_dvd d (S.lcm id) hd_dvd_lcm
      -- Therefore A^{lcm(S)} = 1
      have hpow_lcm : A ^ (S.lcm id) = 1 := pow_eq_one_of_minpoly_dvd (S.lcm id) hminpoly_dvd_lcm
      -- But orderOf A = m > lcm(S), so orderOf A | lcm(S) is false
      have hord_dvd := orderOf_dvd_of_pow_eq_one hpow_lcm
      rw [hA_ord] at hord_dvd
      have := Nat.le_of_dvd hlcm_pos hord_dvd
      omega
    -- Now compute the degree
    have hdeg_eq : (minpoly ℚ A_Q).natDegree = ∑ d ∈ S, Nat.totient d := by
      rw [hminpoly_eq_prod, Polynomial.natDegree_prod _ _ (fun d hd => cyclotomic_ne_zero d ℚ)]
      apply Finset.sum_congr rfl
      intro d hd
      exact natDegree_cyclotomic d ℚ
    -- Apply sum_totient_ge_psi_of_lcm_eq
    calc Crystallographic.psi m ≤ ∑ d ∈ S, Nat.totient d :=
        sum_totient_ge_psi_of_lcm_eq m hm S hS_sub hS_lcm
      _ = (minpoly ℚ A_Q).natDegree := hdeg_eq.symm
      _ ≤ N := hminpoly_deg_le

/-! ## Permutation matrix infrastructure -/

/-- The permutation matrix of the identity permutation is the identity matrix. -/
lemma permMatrix_one' {n : Type*} [DecidableEq n] {R : Type*} [Zero R] [One R] :
    (1 : Equiv.Perm n).permMatrix R = (1 : Matrix n n R) := by
  ext i j
  simp only [Equiv.Perm.permMatrix, Equiv.Perm.one_apply, Equiv.toPEquiv_apply,
    PEquiv.toMatrix_apply, one_apply, Option.mem_def, Option.some.injEq]

/-- Permutation matrices compose: (σ * τ).permMatrix = τ.permMatrix * σ.permMatrix -/
lemma permMatrix_mul' {n : Type*} [DecidableEq n] [Fintype n] {R : Type*} [Semiring R]
    (σ τ : Equiv.Perm n) :
    (σ * τ).permMatrix R = τ.permMatrix R * σ.permMatrix R := by
  simp only [Equiv.Perm.permMatrix]
  rw [Equiv.Perm.mul_def, Equiv.toPEquiv_trans, PEquiv.toMatrix_trans]

/-- Permutation matrices power correctly: (σ^k).permMatrix = (σ.permMatrix)^k -/
lemma permMatrix_pow' {n : Type*} [DecidableEq n] [Fintype n] {R : Type*} [Semiring R]
    (σ : Equiv.Perm n) (k : ℕ) :
    (σ ^ k).permMatrix R = (σ.permMatrix R) ^ k := by
  induction k with
  | zero => simp only [pow_zero]; exact permMatrix_one'
  | succ k ih =>
    rw [pow_succ, pow_succ, permMatrix_mul', ih]
    -- Goal: σ.permMatrix * (σ.permMatrix)^k = (σ.permMatrix)^k * σ.permMatrix
    -- Use SemiconjBy or direct equality - both sides are equal
    exact (Commute.pow_self (σ.permMatrix R) k).eq.symm

/-- Permutation matrix is identity iff permutation is identity. -/
lemma permMatrix_eq_one_iff' {n : Type*} [DecidableEq n] [Fintype n] {R : Type*} [Semiring R]
    [Nontrivial R] (σ : Equiv.Perm n) :
    σ.permMatrix R = 1 ↔ σ = 1 := by
  constructor
  · intro h
    ext x
    have hx := congrFun (congrFun h x) (σ x)
    simp only [Equiv.Perm.permMatrix, Equiv.toPEquiv_apply, PEquiv.toMatrix_apply, one_apply,
      Option.mem_def] at hx
    by_cases hσx : σ x = x
    · exact hσx
    · exfalso
      -- hx says: if σ (σ x) = σ x then 1 else 0 = if x = σ x then 1 else 0
      -- After simp, lhs simplifies using σ (σ x) = σ x ↔ σ x = x (by injectivity)
      -- which is true since Option.mem_def
      -- rhs: x = σ x is false by hσx
      have h1 : (1 : R) = if x = σ x then 1 else 0 := hx
      rw [if_neg (ne_comm.mpr hσx)] at h1
      exact one_ne_zero h1
  · intro h; rw [h]; exact permMatrix_one'

/-- Order of permutation matrix equals order of permutation. -/
lemma orderOf_permMatrix' {n : Type*} [DecidableEq n] [Fintype n] {R : Type*} [Semiring R]
    [Nontrivial R] (σ : Equiv.Perm n) :
    orderOf (σ.permMatrix R) = orderOf σ := by
  rcases Nat.eq_zero_or_pos (orderOf σ) with hord | hord
  · -- σ has infinite order (orderOf σ = 0)
    rw [hord, orderOf_eq_zero_iff']
    intro k hk heq
    have h1 : (σ ^ k).permMatrix R = 1 := by rw [permMatrix_pow']; exact heq
    rw [permMatrix_eq_one_iff'] at h1
    exact (orderOf_eq_zero_iff'.mp hord) k hk h1
  · -- σ has finite order
    rw [orderOf_eq_iff hord]
    constructor
    · rw [← permMatrix_pow', pow_orderOf_eq_one]; exact permMatrix_one'
    · intro k hk_lt hk_pos heq
      have hk' : (σ ^ k).permMatrix R = 1 := by rw [permMatrix_pow']; exact heq
      rw [permMatrix_eq_one_iff'] at hk'
      have hdvd : orderOf σ ∣ k := orderOf_dvd_of_pow_eq_one hk'
      exact Nat.not_lt.mpr (Nat.le_of_dvd hk_pos hdvd) hk_lt

/-- The finRotate permutation has order n for n >= 2. -/
lemma orderOf_finRotate (n : ℕ) (hn : 2 ≤ n) : orderOf (finRotate n) = n := by
  have hcycle := isCycle_finRotate_of_le hn
  have hord := Equiv.Perm.IsCycle.orderOf hcycle
  have hsupp := support_finRotate_of_le hn
  rw [hord, hsupp, Finset.card_univ, Fintype.card_fin]

/-- finRotate permutation matrix has order n for n >= 2. -/
lemma orderOf_permMatrix_finRotate (n : ℕ) (hn : 2 ≤ n) :
    orderOf ((finRotate n).permMatrix ℤ) = n := by
  rw [orderOf_permMatrix', orderOf_finRotate n hn]

/-- Order n is achievable by an n x n integer matrix for n >= 2. -/
lemma mem_integerMatrixOrders_self (n : ℕ) (hn : 2 ≤ n) : n ∈ integerMatrixOrders n := by
  use (finRotate n).permMatrix ℤ
  constructor
  · exact orderOf_permMatrix_finRotate n hn
  · omega

/-! ## Backward direction: Dimension bound implies order is achievable -/

/-- Helper: The identity matrix has order 1, contributing dimension 0. -/
lemma order_one_achievable (N : ℕ) : 1 ∈ integerMatrixOrders N :=
  one_mem_integerMatrixOrders N

/-- Helper: The negation of identity has order 2, contributing dimension 0 for N >= 1. -/
lemma order_two_achievable (N : ℕ) [NeZero N] : 2 ∈ integerMatrixOrders N :=
  two_mem_integerMatrixOrders N

/-- For prime power p^k with p odd or k >= 2, p^k ∈ integerMatrixOrders(psi(p^k)).
    Since psi(p^k) = totient(p^k) in this case, this follows from companion matrix. -/
theorem primePow_mem_integerMatrixOrders_psi (p k : ℕ) (hp : p.Prime) (hk : 0 < k)
    (hpk : ¬(p = 2 ∧ k = 1)) :
    p ^ k ∈ integerMatrixOrders (Crystallographic.psi (p ^ k)) := by
  -- psi(p^k) = totient(p^k) for this case
  have hpsi_eq : Crystallographic.psi (p ^ k) = Nat.totient (p ^ k) := by
    rw [Crystallographic.psi_prime_pow p k hp hk]
    simp only [hpk, ite_false]
  rw [hpsi_eq]
  -- Use companion matrix lemma
  have hpk_ge2 : 2 ≤ p ^ k := by
    have hp_ge2 : 2 ≤ p := hp.two_le
    calc p ^ k ≥ p ^ 1 := Nat.pow_le_pow_right (Nat.le_of_lt hp.one_lt) hk
      _ = p := pow_one p
      _ ≥ 2 := hp_ge2
  exact Crystallographic.mem_integerMatrixOrders_totient (p ^ k) hpk_ge2

/-- Main construction: Every m >= 1 with m ≠ 2 belongs to integerMatrixOrders(psi(m)).

The proof uses strong induction on m:
- m = 1: psi(1) = 0, use identity matrix
- m = 2: EXCLUDED - psi(2) = 0 but 2 ∉ integerMatrixOrders(0)
- m = p^k prime power (p != 2 or k != 1): use companion matrix
- m composite: factor as p^e * m' with coprime parts, apply IH and block diagonal

Note: For m = 2, psi(2) = 0 means no additional dimension is needed, but there's
no 0×0 integer matrix with order 2. The crystallographic restriction theorem
handles m = 2 separately using the hypothesis hNm : m = 1 ∨ 0 < N.

This theorem is used to complete the backward direction of the crystallographic
restriction theorem: if psi(m) <= N, then m ∈ integerMatrixOrders(N).
-/
theorem mem_integerMatrixOrders_psi (m : ℕ) (hm : 0 < m) (hm2 : m ≠ 2) :
    m ∈ integerMatrixOrders (Crystallographic.psi m) := by
  -- Use strong induction on m
  induction m using Nat.strong_induction_on with
  | _ m IH =>
  -- Case analysis on m
  rcases Nat.lt_trichotomy m 1 with hm_lt | rfl | hm_gt
  · omega -- m < 1 contradicts hm : 0 < m
  · -- m = 1: psi(1) = 0, use identity matrix
    simp only [Crystallographic.psi_one]
    exact one_mem_integerMatrixOrders 0
  · -- m > 1, i.e., m >= 2
    -- Since m ≠ 2 (from hypothesis), m > 1 implies m >= 3
    have hm_gt2 : 2 < m := by omega
    -- m > 2, i.e., m >= 3
    -- Check if m is a prime power
    by_cases hpow : IsPrimePow m
    · -- m is a prime power p^k
      rw [isPrimePow_nat_iff] at hpow
      obtain ⟨p, k, hp, hk, hpk⟩ := hpow
      subst hpk
      -- Check if it's 2^1
      by_cases h21 : p = 2 ∧ k = 1
      · -- m = 2^1 = 2, but m > 2, contradiction
        obtain ⟨rfl, rfl⟩ := h21
        simp only [pow_one] at hm_gt2
        omega
      · -- m = p^k with ¬(p = 2 ∧ k = 1)
        exact primePow_mem_integerMatrixOrders_psi p k hp hk h21
    · -- m is not a prime power, so it's composite with distinct prime factors
        -- Factor m into coprime parts using minFac decomposition
        have hm_ne_zero : m ≠ 0 := by omega
        have hminFac : m.minFac.Prime := Nat.minFac_prime (by omega : m ≠ 1)
        have hminFac_dvd : m.minFac ∣ m := Nat.minFac_dvd m
        -- Define p and e as the smallest prime and its exponent
        set p := m.minFac with hp_def
        set e := m.factorization p with he_def
        have he_pos : 0 < e := by
          have : 0 < m.factorization m.minFac := Nat.Prime.factorization_pos_of_dvd
            hminFac hm_ne_zero hminFac_dvd
          simp only [← hp_def] at this
          exact this
        -- m = p^e * (m / p^e)
        have hdvd : p ^ e ∣ m := Nat.ordProj_dvd m p
        have hm_eq : m = p ^ e * (m / p ^ e) := by
          exact (Nat.mul_div_cancel' hdvd).symm
        -- Define m' = m / p^e (the complementary factor)
        set m' := m / p ^ e with hm'_def
        have hm'_pos : 0 < m' :=
          Nat.div_pos (Nat.le_of_dvd (by omega) hdvd) (Nat.pow_pos hminFac.pos)
        have hm'_lt : m' < m := by
          have hpe_ge2 : 2 ≤ p ^ e := by
            calc p ^ e ≥ p ^ 1 := Nat.pow_le_pow_right (Nat.Prime.one_lt hminFac).le he_pos
              _ = p := pow_one p
              _ ≥ 2 := Nat.Prime.two_le hminFac
          calc m' = 1 * m' := (one_mul _).symm
            _ < p ^ e * m' := Nat.mul_lt_mul_of_pos_right
                (Nat.one_lt_pow he_pos.ne' (Nat.Prime.one_lt hminFac)) hm'_pos
            _ = m := hm_eq.symm
        -- Coprimality: gcd(p^e, m') = 1
        have hcop : Nat.Coprime (p ^ e) m' := by
          have := Nat.coprime_ordCompl hminFac hm_ne_zero
          -- this : p.Coprime (m / p ^ m.factorization p) = p.Coprime m'
          -- We need (p ^ e).Coprime m'
          -- Since p.Coprime m', we have (p ^ e).Coprime m'
          have hpcop : p.Coprime m' := this
          exact hpcop.pow_left e
        -- m' ≠ 1 because m is not a prime power
        have hm'_ne_one : m' ≠ 1 := by
          intro hm'_one
          have hm_is_pe : m = p ^ e := by simp only [hm'_one, mul_one] at hm_eq; exact hm_eq
          apply hpow
          rw [isPrimePow_nat_iff]
          exact ⟨p, e, hminFac, he_pos, hm_is_pe.symm⟩
        have hm'_ge2 : 2 ≤ m' := by omega
        -- Now split on whether p^e = 2 (i.e., p = 2 and e = 1)
        by_cases h_pe_is_2 : p = 2 ∧ e = 1
        · -- p^e = 2, so psi(2) = 0
          obtain ⟨hp2, he1⟩ := h_pe_is_2
          -- Show that m = 2 * m' and work with that
          have hm_eq' : m = 2 * m' := by simp only [hp2, he1, pow_one] at hm_eq; exact hm_eq
          have hcop' : Nat.Coprime 2 m' := by simp only [hp2, he1, pow_one] at hcop; exact hcop
          -- m' ≠ 2 because m' is coprime to 2 (hence odd) and m' ≥ 2, so m' ≥ 3
          have hm'_ne_2 : m' ≠ 2 := by
            intro hm'_eq_2
            have : Nat.Coprime 2 2 := by rw [hm'_eq_2] at hcop'; exact hcop'
            rw [Nat.coprime_self] at this
            norm_num at this
          -- Apply IH to m'
          have IH_m' := IH m' hm'_lt hm'_pos hm'_ne_2
          -- psi(m) = psi(2 * m') = psi(2) + psi(m') = 0 + psi(m') = psi(m')
          have hpsi_eq : Crystallographic.psi m = Crystallographic.psi m' := by
            rw [hm_eq', Crystallographic.psi_coprime_add 2 m' (by omega) hm'_pos hcop']
            simp only [Crystallographic.psi_two, zero_add]
          rw [hpsi_eq]
          -- Need: m ∈ integerMatrixOrders (psi m'), i.e., 2 * m' ∈ integerMatrixOrders (psi m')
          -- We have: m' ∈ integerMatrixOrders (psi m') from IH
          -- Key insight: If A has order m' with m' odd, then -A has order 2 * m'.
          obtain ⟨A, hA_ord, hA_pos⟩ := IH_m'
          refine ⟨-A, ?_, by omega⟩
          -- orderOf (-A) = 2 * m' = m
          have hm'_odd : Odd m' := by
            rw [Nat.odd_iff]
            have h2ndvd : ¬(2 ∣ m') := fun h2dvd =>
              Nat.not_lt.mpr (Nat.le_of_dvd (by omega) (Nat.dvd_gcd (dvd_refl 2) h2dvd))
                (by rw [hcop'.gcd_eq_one]; norm_num)
            omega
          -- -A = (-1) * A, and -1 commutes with A
          -- orderOf(-1) = 2 (in characteristic 0), orderOf(A) = m' (odd)
          -- So orderOf(-A) = 2 * m' since gcd(2, m') = 1
          have hA_ord_pos : 0 < orderOf A := by omega
          -- Express -A as (-1) * A
          have hneg_eq : -A = (-1 : Matrix (Fin (Crystallographic.psi m'))
              (Fin (Crystallographic.psi m')) ℤ) * A := by simp
          rw [hneg_eq]
          -- -1 and A commute (everything commutes with -1)
          have hcomm : Commute (-1 : Matrix (Fin (Crystallographic.psi m'))
              (Fin (Crystallographic.psi m')) ℤ) A := Commute.neg_one_left A
          -- First, we need to show that psi m' > 0 for m' odd, m' ≥ 3
          have hm'_ge3 : 3 ≤ m' := by
            -- m' is odd and m' ≥ 2, so m' ≥ 3
            rcases hm'_odd with ⟨k, hk⟩
            omega
          -- For m' ≥ 3 odd, psi m' > 0 because m' has an odd prime factor
          have hpsi_pos : 0 < Crystallographic.psi m' := by
            have hm'_has_prime : ∃ q, q.Prime ∧ q ∣ m' := ⟨m'.minFac,
              Nat.minFac_prime (by omega : m' ≠ 1), Nat.minFac_dvd m'⟩
            obtain ⟨q, hq_prime, hq_dvd⟩ := hm'_has_prime
            have hq_ge3 : 3 ≤ q := by
              have hq2 : 2 ≤ q := hq_prime.two_le
              have hq_ne2 : q ≠ 2 := by
                intro hq2eq
                subst hq2eq
                have h2dvd : 2 ∣ m' := hq_dvd
                have : 2 ∣ Nat.gcd 2 m' := Nat.dvd_gcd (dvd_refl 2) h2dvd
                rw [hcop'.gcd_eq_one] at this
                exact Nat.not_lt.mpr (Nat.le_of_dvd (by omega) this) (by norm_num : 1 < 2)
              omega
            have hq_in_support : q ∈ m'.factorization.support := by
              rw [Finsupp.mem_support_iff]
              exact (Nat.Prime.factorization_pos_of_dvd hq_prime (by omega) hq_dvd).ne'
            have hcontrib : Crystallographic.psiPrimePow q (m'.factorization q) ≤
                Crystallographic.psi m' :=
              Crystallographic.psi_ge_psiPrimePow_of_mem_support (by omega) hq_in_support
            have hcontrib_pos : 0 < Crystallographic.psiPrimePow q (m'.factorization q) := by
              simp only [Crystallographic.psiPrimePow]
              have hk_pos : 0 < m'.factorization q :=
                Nat.Prime.factorization_pos_of_dvd hq_prime (by omega) hq_dvd
              simp only [hk_pos.ne', ite_false]
              have hq_ne2 : q ≠ 2 := by omega
              simp only [hq_ne2, false_and, ite_false]
              exact Nat.totient_pos.mpr (Nat.pow_pos hq_prime.pos)
            omega
          -- Now we have psi m' > 0, so the matrix ring is nontrivial
          haveI : NeZero (Crystallographic.psi m') := ⟨by omega⟩
          -- orderOf(-1) = 2 in Matrix n n ℤ for n > 0
          have hord_neg1 : orderOf (-1 : Matrix (Fin (Crystallographic.psi m'))
              (Fin (Crystallographic.psi m')) ℤ) = 2 := by
            rw [orderOf_neg_one, ringChar_matrix_int]
            simp
          -- Coprimality of orders
          have hord_cop : Nat.Coprime (orderOf (-1 : Matrix (Fin (Crystallographic.psi m'))
              (Fin (Crystallographic.psi m')) ℤ)) (orderOf A) := by
            rw [hord_neg1, hA_ord]
            exact hcop'
          -- Apply the product formula
          rw [hcomm.orderOf_mul_eq_mul_orderOf_of_coprime hord_cop]
          rw [hord_neg1, hA_ord, ← hm_eq']
        · -- p^e ≠ 2, so psi(p^e) = totient(p^e) > 0
          -- Use block diagonal construction
          push_neg at h_pe_is_2
          have h_not_21 : ¬(p = 2 ∧ e = 1) := fun ⟨hp2, he1⟩ => h_pe_is_2 hp2 he1
          have IH_pe : p ^ e ∈ integerMatrixOrders (Crystallographic.psi (p ^ e)) :=
            primePow_mem_integerMatrixOrders_psi p e hminFac he_pos h_not_21
          -- Check if m' = 2 (special case: use -A trick instead of block diagonal)
          by_cases hm'_eq_2 : m' = 2
          · -- m' = 2, so m = p^e * 2 with p odd
            -- psi(m) = psi(p^e * 2) = psi(p^e) + psi(2) = psi(p^e)
            have hcop_pe_2 : Nat.Coprime (p ^ e) 2 := by rw [hm'_eq_2] at hcop; exact hcop
            have hpsi_eq : Crystallographic.psi m = Crystallographic.psi (p ^ e) := by
              rw [hm_eq, hm'_eq_2, Crystallographic.psi_coprime_add (p ^ e) 2
                (Nat.pow_pos hminFac.pos) (by omega) hcop_pe_2]
              simp only [Crystallographic.psi_two, add_zero]
            rw [hpsi_eq]
            -- Need: m = p^e * 2 ∈ integerMatrixOrders(psi(p^e))
            -- We have: p^e ∈ integerMatrixOrders(psi(p^e)) from IH_pe
            -- Key insight: If A has odd order p^e, then -A has order 2 * p^e = m
            obtain ⟨A, hA_ord, hA_pos⟩ := IH_pe
            refine ⟨-A, ?_, by omega⟩
            -- p^e is odd because p ≠ 2 (since gcd(p^e, 2) = 1 by coprimality with m' = 2)
            have hp_odd : p ≠ 2 := by
              intro hp2
              have h1 : Nat.Coprime (p ^ e) 2 := hcop_pe_2
              rw [hp2] at h1
              simp only [Nat.coprime_pow_left_iff he_pos, Nat.coprime_self] at h1
              norm_num at h1
            have hpe_odd : Odd (p ^ e) := by
              have hp_odd' : Odd p := Nat.Prime.odd_of_ne_two hminFac hp_odd
              exact hp_odd'.pow
            -- Express -A as (-1) * A
            have hneg_eq : -A = (-1 : Matrix (Fin (Crystallographic.psi (p ^ e)))
                (Fin (Crystallographic.psi (p ^ e))) ℤ) * A := by simp
            rw [hneg_eq]
            -- -1 and A commute
            have hcomm : Commute (-1 : Matrix (Fin (Crystallographic.psi (p ^ e)))
                (Fin (Crystallographic.psi (p ^ e))) ℤ) A := Commute.neg_one_left A
            -- psi(p^e) > 0 for p ≠ 2 or e ≠ 1, and we have ¬(p = 2 ∧ e = 1)
            have hpsi_pos : 0 < Crystallographic.psi (p ^ e) := by
              simp only [Crystallographic.psi_prime_pow p e hminFac he_pos, h_not_21, ite_false]
              exact Nat.totient_pos.mpr (Nat.pow_pos hminFac.pos)
            haveI : NeZero (Crystallographic.psi (p ^ e)) := ⟨by omega⟩
            -- orderOf(-1) = 2
            have hord_neg1 : orderOf (-1 : Matrix (Fin (Crystallographic.psi (p ^ e)))
                (Fin (Crystallographic.psi (p ^ e))) ℤ) = 2 := by
              rw [orderOf_neg_one, ringChar_matrix_int]
              simp
            -- Coprimality: gcd(2, p^e) = 1 since p is odd
            have hcop_2_pe : Nat.Coprime 2 (p ^ e) := hcop_pe_2.symm
            have hord_cop : Nat.Coprime (orderOf (-1 : Matrix (Fin (Crystallographic.psi (p ^ e)))
                (Fin (Crystallographic.psi (p ^ e))) ℤ)) (orderOf A) := by
              rw [hord_neg1, hA_ord]
              exact hcop_2_pe
            rw [hcomm.orderOf_mul_eq_mul_orderOf_of_coprime hord_cop]
            rw [hord_neg1, hA_ord, hm_eq, hm'_eq_2, mul_comm]
          · -- m' ≠ 2, so we can apply IH to m'
            have IH_m' := IH m' hm'_lt hm'_pos hm'_eq_2
            -- psi(m) = psi(p^e * m') = psi(p^e) + psi(m')
            have hpsi_eq : Crystallographic.psi m =
                Crystallographic.psi (p ^ e) + Crystallographic.psi m' := by
              rw [hm_eq, Crystallographic.psi_coprime_add (p ^ e) m'
                (Nat.pow_pos hminFac.pos) hm'_pos hcop]
            rw [hpsi_eq]
            -- m = p^e * m' ∈ integerMatrixOrders(psi(p^e) + psi(m'))
            rw [hm_eq]
            exact mul_mem_integerMatrixOrders_of_coprime IH_pe IH_m' hcop

/-- If psi(m) <= N, then there exists an N x N integer matrix with order m.

This is the backward direction of the crystallographic restriction theorem.
The construction uses companion matrices of cyclotomic polynomials.

**Construction outline:**
1. For m = 1: use identity matrix (psi(1) = 0)
2. For m = 2: use -I (psi(2) = 0)
3. For prime power p^k with p odd or k >= 2:
   - Use companion matrix of Phi_{p^k} (cyclotomic polynomial)
   - This has size phi(p^k) x phi(p^k) = psi(p^k) and order p^k
4. For general m = prod p_i^{k_i}:
   - Take block diagonal of companion matrices for each prime power factor
   - Total size is sum of phi(p_i^{k_i}) = psi(m)
5. Pad with identity blocks to reach size N x N
-/
theorem mem_integerMatrixOrders_of_psi_le (N m : ℕ) (hm : 0 < m)
    (hpsi : Crystallographic.psi m ≤ N) (hNm : m = 1 ∨ 0 < N) :
    m ∈ integerMatrixOrders N := by
  -- We construct a matrix of size psi(m) with order m, then embed into N x N
  -- The cases m = 1 and m = 2 are handled separately (psi = 0)
  -- For other cases, we use companion matrices of cyclotomic polynomials
  --
  -- Key facts needed:
  -- 1. Companion matrix of monic polynomial p has characteristic polynomial p
  -- 2. Cyclotomic polynomial Phi_m is monic with integer coefficients
  -- 3. Companion matrix of Phi_m has order m
  -- 4. Block diagonal of matrices preserves order (for coprime orders: lcm)
  --
  -- Handle the base cases
  rcases Nat.lt_trichotomy m 1 with hm_lt | rfl | hm_gt
  -- Case m < 1, i.e., m = 0 (contradicts hm)
  · omega
  -- Case m = 1
  · exact order_one_achievable N
  -- Case m > 1, i.e., m >= 2
  · rcases Nat.lt_trichotomy m 2 with hm_lt2 | rfl | hm_gt2
    -- Case m < 2, but m > 1, contradiction
    · omega
    -- Case m = 2
    · rcases Nat.eq_zero_or_pos N with rfl | hN_pos
      · -- N = 0 case: The hypothesis hNm : m = 1 ∨ 0 < N becomes 2 = 1 ∨ 0 < 0
        -- Both disjuncts are false, giving a contradiction
        rcases hNm with h | h <;> omega
      · haveI : NeZero N := ⟨Nat.pos_iff_ne_zero.mp hN_pos⟩
        exact order_two_achievable N
    -- Case m > 2, i.e., m >= 3
    · -- Strategy: Either use permutation matrix if m <= N,
      -- or use explicit rotation matrices for m ∈ {3, 4, 6}
      by_cases hle : m ≤ N
      -- Case m <= N: use permutation matrix of finRotate m
      · have hm2 : 2 ≤ m := by omega
        exact integerMatrixOrders_mono hle (mem_integerMatrixOrders_self m hm2)
      -- Case m > N: need explicit constructions for specific m values
      · push_neg at hle
        -- For m >= 3 with psi(m) <= N < m, we use explicit rotation matrices
        -- Currently we have constructions for m ∈ {3, 4, 6} which have psi = 2
        -- For these, if psi(m) = 2 <= N, we can use the 2x2 rotation matrices
        --
        -- First, try explicit cases for 3, 4, 6
        rcases Nat.lt_trichotomy m 3 with hm_lt3 | rfl | hm_gt3
        · omega -- m < 3 but m > 2, contradiction
        · -- m = 3: psi(3) = 2, use rotationMatrix3
          have hN2 : 2 ≤ N := by simp only [Crystallographic.psi_three] at hpsi; omega
          exact integerMatrixOrders_mono hN2 three_mem_integerMatrixOrders_two
        · rcases Nat.lt_trichotomy m 4 with hm_lt4 | rfl | hm_gt4
          · omega -- 3 < m < 4, impossible for naturals
          · -- m = 4: psi(4) = 2, use rotationMatrix4
            have hN2 : 2 ≤ N := by simp only [Crystallographic.psi_four] at hpsi; omega
            exact integerMatrixOrders_mono hN2 four_mem_integerMatrixOrders_two
          · rcases Nat.lt_trichotomy m 6 with hm_lt6 | rfl | hm_gt6
            · -- m = 5 (the only natural between 4 and 6)
              -- psi(5) = 4, need 4x4 matrix with order 5
              -- Use companion matrix of Φ_5 = X^4 + X^3 + X^2 + X + 1
              interval_cases m
              -- Now m = 5
              -- psi(5) = 4, so N >= 4 and N < 5, hence N = 4
              have hN4 : N = 4 := by simp only [Crystallographic.psi_five] at hpsi; omega
              rw [hN4]
              -- Need: 5 ∈ integerMatrixOrders 4
              -- Use companion_cyclotomic_mem_integerMatrixOrders
              -- natDegree (cyclotomic 5 ℤ) = φ(5) = 4
              have hdeg : (Polynomial.cyclotomic 5 ℤ).natDegree = 4 := by
                rw [Polynomial.natDegree_cyclotomic]
                simp only [Nat.totient_prime Nat.prime_five]
              have hn : 0 < (Polynomial.cyclotomic 5 ℤ).natDegree := by omega
              rw [← hdeg]
              exact Crystallographic.companion_cyclotomic_mem_integerMatrixOrders 5 (by omega) hn
            · -- m = 6: psi(6) = 2, use rotationMatrix6
              have hN2 : 2 ≤ N := by simp only [Crystallographic.psi_six] at hpsi; omega
              exact integerMatrixOrders_mono hN2 six_mem_integerMatrixOrders_two
            · -- m > 6: General case
              -- For m > 6 with psi(m) ≤ N < m, we use companion matrices
              -- of cyclotomic polynomials.
              --
              -- Key facts:
              -- - cyclotomic m ℤ has degree totient(m) > 0 for m >= 1
              -- - companion(cyclotomic m ℤ) has dimension totient(m) and order m
              -- - So m ∈ integerMatrixOrders(totient(m))
              -- - By monotonicity, if totient(m) ≤ N, then m ∈ integerMatrixOrders(N)
              --
              -- Two cases:
              -- 1. totient(m) ≤ N: use companion matrix directly
              -- 2. psi(m) ≤ N < totient(m): need block diagonal construction
              --    (This happens for composite m where psi < totient, like m=15,20,...)
              --
              -- For case 1 (which covers all prime powers, m = 2 * odd_prime_power,
              -- and many other cases), the proof proceeds as follows:
              have hdeg : (Polynomial.cyclotomic m ℤ).natDegree = Nat.totient m := by
                exact Polynomial.natDegree_cyclotomic m ℤ
              have htot_pos : 0 < Nat.totient m := Nat.totient_pos.mpr (by omega : 0 < m)
              have hn : 0 < (Polynomial.cyclotomic m ℤ).natDegree := by omega
              -- Check if totient(m) ≤ N
              by_cases htot : Nat.totient m ≤ N
              · -- Case: totient(m) ≤ N, companion matrix works
                have hmem : m ∈ integerMatrixOrders (Polynomial.cyclotomic m ℤ).natDegree :=
                  Crystallographic.companion_cyclotomic_mem_integerMatrixOrders m (by omega) hn
                rw [hdeg] at hmem
                exact integerMatrixOrders_mono htot hmem
              · -- Case: psi(m) ≤ N < totient(m)
                -- This case requires block diagonal construction of companion matrices
                -- for the prime power factors of m.
                --
                -- For composite m with distinct prime factors, psi(m) = sum of
                -- totients of prime power factors, while totient(m) = product.
                -- The block diagonal of companion matrices for each factor gives
                -- a matrix of dimension psi(m) with order m (since lcm of coprime
                -- orders equals product).
                --
                -- The available infrastructure includes:
                -- - blockDiag2: block diagonal of two matrices
                -- - orderOf_blockDiag2: order is lcm of orders
                -- - mul_mem_integerMatrixOrders_of_coprime: for coprime m1, m2,
                --   if m1 ∈ integerMatrixOrders M and m2 ∈ integerMatrixOrders K,
                --   then m1 * m2 ∈ integerMatrixOrders (M + K)
                -- - mem_integerMatrixOrders_totient: for m >= 2,
                --   m ∈ integerMatrixOrders(totient m)
                --
                -- The proof would proceed by factoring m into coprime parts
                -- and recursively applying the block diagonal construction.
                -- For m = p1^k1 * ... * pr^kr with distinct primes:
                --   - Each pi^ki ∈ integerMatrixOrders(totient(pi^ki))
                --   - Block diagonal construction gives
                --     m ∈ integerMatrixOrders(sum_i totient(pi^ki))
                --   - For m not divisible by exactly 2, this sum equals psi(m)
                --
                -- Examples of this case:
                -- - m = 15 = 3*5: psi = 6, totient = 8
                --   3 ∈ integerMatrixOrders 2, 5 ∈ integerMatrixOrders 4
                --   By mul_mem_integerMatrixOrders_of_coprime: 15 ∈ integerMatrixOrders 6
                -- - m = 20 = 4*5: psi = 6, totient = 8
                --   4 ∈ integerMatrixOrders 2, 5 ∈ integerMatrixOrders 4
                --   By mul_mem_integerMatrixOrders_of_coprime: 20 ∈ integerMatrixOrders 6
                -- - m = 21 = 3*7: psi = 8, totient = 12
                --   3 ∈ integerMatrixOrders 2, 7 ∈ integerMatrixOrders 6
                --   By mul_mem_integerMatrixOrders_of_coprime: 21 ∈ integerMatrixOrders 8
                --
                -- Full implementation requires recursion over the prime factorization.
                --
                -- Once mem_integerMatrixOrders_psi is complete, this case follows by
                -- monotonicity: m ∈ integerMatrixOrders(psi m) and psi m ≤ N imply
                -- m ∈ integerMatrixOrders(N).
                --
                -- Until then, this case remains incomplete.
                push_neg at htot
                -- htot : N < Nat.totient m
                -- Combined with hpsi : psi m ≤ N, we get psi m ≤ N < totient m
                -- This implies psi m < totient m, which happens for composite m
                -- with multiple prime factors.
                --
                have hmem := mem_integerMatrixOrders_psi m (by omega) (by omega)
                exact integerMatrixOrders_mono hpsi hmem

end Crystallographic
