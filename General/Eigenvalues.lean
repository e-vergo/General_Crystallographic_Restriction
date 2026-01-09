/-
Copyright (c) 2026 Eric Vergo. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Eric Vergo
-/
import Mathlib.LinearAlgebra.Matrix.Charpoly.Minpoly
import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Mathlib.LinearAlgebra.Eigenspace.Matrix
import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic

/-!
# Eigenvalues of Finite Order Integer Matrices

This file establishes the connection between finite order integer matrices and roots of unity.
If A is an N×N integer matrix with A^m = I (finite order m), then all eigenvalues of A
are m-th roots of unity.

## Main results

* `minpoly_dvd_X_pow_sub_one` - The minimal polynomial of a finite order matrix divides X^m - 1.
* `aeval_X_pow_sub_one_of_pow_eq_one` - If A^m = 1, then (X^m - 1)(A) = 0.
* `eigenvalue_pow_eq_one` - Eigenvalues of a finite order matrix are roots of unity.

## Key ideas

The proof proceeds via the minimal polynomial:
1. If A^m = 1, then the polynomial X^m - 1 annihilates A.
2. By the defining property of minimal polynomials, minpoly(A) divides X^m - 1.
3. Eigenvalues are roots of the characteristic polynomial.
4. The characteristic polynomial is divisible by the minimal polynomial.
5. Therefore eigenvalues are roots of X^m - 1, i.e., m-th roots of unity.

## References

* The crystallographic restriction theorem uses this to constrain rotation orders.
-/

namespace Crystallographic

open Matrix Polynomial

variable {N : ℕ} [NeZero N]

/-! ### Polynomial evaluation and annihilation -/

omit [NeZero N] in
/-- The polynomial X^m - 1 evaluated at a matrix A equals A^m - 1. -/
lemma aeval_X_pow_sub_one (A : Matrix (Fin N) (Fin N) ℤ) (m : ℕ) :
    aeval A (X ^ m - 1 : ℤ[X]) = A ^ m - 1 := by
  simp only [map_sub, map_pow, aeval_X, map_one]

omit [NeZero N] in
/-- If A^m = 1, then the polynomial X^m - 1 annihilates A. -/
lemma aeval_X_pow_sub_one_eq_zero_of_pow_eq_one
    (A : Matrix (Fin N) (Fin N) ℤ) (m : ℕ) (hord : A ^ m = 1) :
    aeval A (X ^ m - 1 : ℤ[X]) = 0 := by
  rw [aeval_X_pow_sub_one, hord, sub_self]

/-! ### Minimal polynomial divides X^m - 1 -/

omit [NeZero N] in
/-- A matrix with A^m = 1 is integral over Z (satisfies a monic polynomial). -/
lemma isIntegral_of_pow_eq_one (A : Matrix (Fin N) (Fin N) ℤ) (m : ℕ) (hm : 0 < m)
    (hord : A ^ m = 1) : IsIntegral ℤ A := by
  refine ⟨X ^ m - 1, ?_, ?_⟩
  · exact monic_X_pow_sub_C 1 (Nat.pos_iff_ne_zero.mp hm)
  · exact aeval_X_pow_sub_one_eq_zero_of_pow_eq_one A m hord

omit [NeZero N] in
/-- If an integer matrix has finite order m, its minimal polynomial divides X^m - 1.

This is the key algebraic fact: since A^m = 1, the polynomial X^m - 1 annihilates A,
and the minimal polynomial is the monic polynomial of least degree that annihilates A,
so it must divide X^m - 1.

Note: For matrices, the minimal polynomial theory over ℤ is subtle since matrices
don't form an integral domain. We use Gauss lemma to reduce to ℚ, where we show that
(minpoly ℤ A).map ℚ = minpoly ℚ (A.map ℚ), then apply minpoly.dvd over ℚ. -/
theorem minpoly_dvd_X_pow_sub_one (A : Matrix (Fin N) (Fin N) ℤ) (m : ℕ) (hm : 0 < m)
    (hord : A ^ m = 1) : (minpoly ℤ A) ∣ (X ^ m - 1) := by
  -- Use Gauss lemma: monic polynomial divisibility over ℤ ↔ over ℚ
  have hp : (X ^ m - 1 : ℤ[X]).Monic := monic_X_pow_sub_C 1 (Nat.pos_iff_ne_zero.mp hm)
  have hq : (minpoly ℤ A).Monic := minpoly.monic (isIntegral_of_pow_eq_one A m hm hord)
  rw [← Polynomial.Monic.dvd_iff_fraction_map_dvd_fraction_map (K := ℚ) hp hq]
  -- Now prove: (minpoly ℤ A).map ℚ ∣ (X^m - 1).map ℚ over ℚ
  let AQ := A.map (algebraMap ℤ ℚ)
  -- (minpoly ℤ A).map ℚ annihilates AQ
  have hann : aeval AQ ((minpoly ℤ A).map (algebraMap ℤ ℚ)) = 0 := by
    have heq : AQ = (Algebra.ofId ℤ ℚ).mapMatrix A := by
      ext i j; simp only [AlgHom.mapMatrix_apply, Matrix.map_apply, Algebra.ofId_apply]; rfl
    rw [heq, aeval_map_algebraMap]
    rw [aeval_algHom_apply (Algebra.ofId ℤ ℚ).mapMatrix A (minpoly ℤ A)]
    simp only [minpoly.aeval, map_zero]
  -- Therefore minpoly ℚ AQ divides (minpoly ℤ A).map ℚ
  have hdvd : minpoly ℚ AQ ∣ (minpoly ℤ A).map (algebraMap ℤ ℚ) := minpoly.dvd ℚ AQ hann
  have hmonic_map : ((minpoly ℤ A).map (algebraMap ℤ ℚ)).Monic := hq.map _
  have hmonic_Q : (minpoly ℚ AQ).Monic := minpoly.monic (Matrix.isIntegral AQ)
  -- Key: show these have the same degree, hence are equal
  have hminpoly_eq : (minpoly ℤ A).map (algebraMap ℤ ℚ) = minpoly ℚ AQ := by
    refine Polynomial.eq_of_monic_of_dvd_of_natDegree_le hmonic_Q hmonic_map hdvd ?_
    rw [hq.natDegree_map]
    -- Proof by contradiction: assume deg(minpoly ℤ A) > deg(minpoly ℚ AQ)
    by_contra hne
    push_neg at hne
    have hdeg_strict : (minpoly ℚ AQ).natDegree < (minpoly ℤ A).natDegree := hne
    -- By Gauss lemma, minpoly ℚ AQ = r.map ℚ for some monic r : ℤ[X]
    have : ∃ (q : ℤ[X]), q.Monic ∧ q.map (algebraMap ℤ ℚ) = minpoly ℚ AQ := by
      obtain ⟨r, hr⟩ := IsIntegrallyClosed.eq_map_mul_C_of_dvd (K := ℚ) hq hdvd
      use r
      have hlc : (minpoly ℚ AQ).leadingCoeff = 1 := hmonic_Q.leadingCoeff
      rw [hlc, Polynomial.C_1, mul_one] at hr
      constructor
      · rw [Polynomial.Monic]
        have h1 : (r.map (algebraMap ℤ ℚ)).leadingCoeff = (minpoly ℚ AQ).leadingCoeff := by rw [hr]
        rw [hlc] at h1
        rw [Polynomial.leadingCoeff_map_of_injective
            (RingHom.injective_int (algebraMap ℤ ℚ))] at h1
        exact (algebraMap ℤ ℚ).injective_int h1
      · exact hr
    obtain ⟨q, hq_monic, hq_map⟩ := this
    -- q.map ℚ = minpoly ℚ AQ, so aeval AQ (q.map ℚ) = 0
    have hq_ann : aeval AQ (q.map (algebraMap ℤ ℚ)) = 0 := by rw [hq_map, minpoly.aeval]
    -- Therefore aeval A q = 0 (by injectivity of the map to matrices over ℚ)
    have hq_ann_A : aeval A q = 0 := by
      have h : (Algebra.ofId ℤ ℚ).mapMatrix (aeval A q) = aeval AQ (q.map (algebraMap ℤ ℚ)) := by
        have heqA : AQ = (Algebra.ofId ℤ ℚ).mapMatrix A := by
          ext i j; simp only [AlgHom.mapMatrix_apply, Matrix.map_apply, Algebra.ofId_apply]; rfl
        rw [heqA, aeval_map_algebraMap]
        exact (aeval_algHom_apply (Algebra.ofId ℤ ℚ).mapMatrix A q).symm
      rw [hq_ann] at h
      have hinj : Function.Injective
          ((Algebra.ofId ℤ ℚ).mapMatrix : Matrix (Fin N) (Fin N) ℤ →ₐ[ℤ] _) := by
        intro M₁ M₂ heq
        ext i j
        have h1 : ((Algebra.ofId ℤ ℚ).mapMatrix M₁) i j =
            ((Algebra.ofId ℤ ℚ).mapMatrix M₂) i j := by rw [heq]
        simp only [AlgHom.mapMatrix_apply, Matrix.map_apply, Algebra.ofId_apply] at h1
        exact (algebraMap ℤ ℚ).injective_int h1
      exact hinj h
    -- q is monic and aeval A q = 0, so by minpoly.min, deg(minpoly ℤ A) ≤ deg(q)
    have hdeg_q : q.natDegree = (minpoly ℚ AQ).natDegree := by rw [← hq_map, hq_monic.natDegree_map]
    have hdeg_le : (minpoly ℤ A).degree ≤ q.degree := minpoly.min ℤ A hq_monic hq_ann_A
    have hdeg_le_nat : (minpoly ℤ A).natDegree ≤ q.natDegree :=
      Polynomial.natDegree_le_natDegree hdeg_le
    rw [hdeg_q] at hdeg_le_nat
    omega
  rw [hminpoly_eq]
  -- Now apply minpoly.dvd since (X^m - 1).map ℚ annihilates AQ
  apply minpoly.dvd
  rw [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_one]
  simp only [map_sub, map_pow, aeval_X, map_one]
  rw [← Matrix.map_pow, hord]
  rw [Matrix.map_one (algebraMap ℤ ℚ) (map_zero _) (map_one _), sub_self]

/-! ### Eigenvalues are roots of unity -/

/-- A root of a polynomial p is also a root of any multiple q = p * s. -/
lemma IsRoot_of_dvd {R : Type*} [CommRing R] {p q : R[X]} (hdvd : p ∣ q) {r : R}
    (hr : p.IsRoot r) : q.IsRoot r := by
  obtain ⟨s, hs⟩ := hdvd
  simp only [IsRoot, hs, eval_mul]
  rw [IsRoot] at hr
  rw [hr, zero_mul]

/-- For a field K, a root of X^m - 1 in K is an m-th root of unity. -/
lemma isRoot_X_pow_sub_one_iff {K : Type*} [Field K] (r : K) (m : ℕ) :
    (X ^ m - 1 : K[X]).IsRoot r ↔ r ^ m = 1 := by
  simp only [IsRoot, eval_sub, eval_pow, eval_X, eval_one, sub_eq_zero]

omit [NeZero N] in
/-- Eigenvalues of a finite order integer matrix are roots of unity.

If A is an N×N integer matrix with A^m = 1, then any eigenvalue mu (in C or any field extension)
satisfies mu^m = 1.

The proof uses the fact that eigenvalues are roots of the minimal polynomial,
and the minimal polynomial divides X^m - 1 when A^m = 1. -/
theorem eigenvalue_pow_eq_one {K : Type*} [Field K] [Algebra ℤ K]
    (A : Matrix (Fin N) (Fin N) ℤ) (m : ℕ) (hord : A ^ m = 1) (mu : K)
    (hmu : mu ∈ spectrum K (A.map (algebraMap ℤ K))) : mu ^ m = 1 := by
  let AK := A.map (algebraMap ℤ K)
  -- Convert spectrum to HasEigenvalue via the linear map representation
  rw [← Matrix.spectrum_toLin'] at hmu
  -- The minimal polynomial divides X^m - 1 since A^m = 1
  have hmin_dvd : minpoly K AK ∣ (X ^ m - 1 : K[X]) := by
    apply minpoly.dvd
    simp only [map_sub, map_pow, aeval_X, map_one]
    rw [← Matrix.map_pow, hord]
    simp only [Matrix.map_one (algebraMap ℤ K) (map_zero _) (map_one _), sub_self]
  -- Eigenvalues are roots of the minimal polynomial
  have hmu_minpoly : (minpoly K AK).IsRoot mu := by
    -- Use hasEigenvalue_iff_isRoot via the linear map
    rw [← Matrix.minpoly_toLin']
    apply Module.End.isRoot_of_hasEigenvalue
    exact Module.End.HasEigenvalue.of_mem_spectrum hmu
  -- So mu is a root of X^m - 1
  have hmu_Xm1 : (X ^ m - 1 : K[X]).IsRoot mu := IsRoot_of_dvd hmin_dvd hmu_minpoly
  rwa [isRoot_X_pow_sub_one_iff] at hmu_Xm1

/-! ### Connection to primitive roots and cyclotomic polynomials -/

omit [NeZero N] in
/-- The minimal polynomial of a finite order matrix over Q divides X^m - 1. -/
theorem minpoly_rat_dvd_X_pow_sub_one (A : Matrix (Fin N) (Fin N) ℤ) (m : ℕ)
    (hord : A ^ m = 1) :
    (minpoly ℚ (A.map (algebraMap ℤ ℚ))) ∣ (X ^ m - 1 : ℚ[X]) := by
  apply minpoly.dvd
  simp only [map_sub, map_pow, aeval_X, map_one]
  rw [← Matrix.map_pow, hord]
  simp only [Matrix.map_one (algebraMap ℤ ℚ) (map_zero _) (map_one _), sub_self]

omit [NeZero N] in
/-- If A has order exactly m (i.e., A^m = 1 and m is minimal), then the minimal polynomial
of A (viewed over Q) is a product of cyclotomic polynomials dividing m.

This follows because X^m - 1 = prod_{d|m} phi_d where phi_d is the d-th cyclotomic polynomial,
and the minimal polynomial divides X^m - 1, hence is a product of some of these cyclotomics. -/
theorem minpoly_dvd_cyclotomic_prod (A : Matrix (Fin N) (Fin N) ℤ) (m : ℕ) (hm : 0 < m)
    (hord : A ^ m = 1) :
    (minpoly ℚ (A.map (algebraMap ℤ ℚ))) ∣ ∏ d ∈ m.divisors, cyclotomic d ℚ := by
  have hdvd := minpoly_rat_dvd_X_pow_sub_one A m hord
  rw [← prod_cyclotomic_eq_X_pow_sub_one hm] at hdvd
  exact hdvd

end Crystallographic
