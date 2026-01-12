/-
Copyright (c) 2026 Eric Vergo. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Eric Vergo
-/
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots

import Crystallographic.Companion
import Crystallographic.FiniteOrder.Basic

/-!
# Companion Matrices of Cyclotomic Polynomials

This file proves properties of companion matrices specifically for cyclotomic polynomials,
which are essential for the crystallographic restriction theorem.

## Main results

* `companion_cyclotomic_pow_eq_one` - companion(Phi_m)^m = 1
* `companion_cyclotomic_orderOf` - orderOf(companion(Phi_m)) = m for m >= 2
* `companion_cyclotomic_mem_integerMatrixOrders` - companion of Phi_m has order m
* `mem_integerMatrixOrders_totient` - m in integerMatrixOrders(totient m) for m >= 2

## References

* Sasse, R. (2020). "Crystallographic Groups"
-/

namespace Crystallographic

open Matrix Polynomial

@[blueprint "lem:companion-cycl-pow"
  (statement := /-- $C(\Phi_m)^m = I$. Since the cyclotomic polynomial $\Phi_m$ divides
  $X^m - 1$ (as $X^m - 1 = \prod_{d \mid m} \Phi_d$), we apply \texttt{companion\_pow\_eq\_one\_of\_dvd}.
  \uses{thm:companion-pow-dvd} -/)
  (proof := /-- Since $\Phi_m \mid X^m - 1$ (as $X^m - 1 = \prod_{d \mid m} \Phi_d$), we apply
  the general companion power theorem to conclude $C(\Phi_m)^m = I$. -/)]
lemma companion_cyclotomic_pow_eq_one (m : ℕ) (_hm : 0 < m)
    (hn : 0 < (cyclotomic m ℤ).natDegree) :
    (companion (cyclotomic m ℤ) (cyclotomic.monic m ℤ) hn) ^ m = 1 := by
  apply companion_pow_eq_one_of_dvd
  exact cyclotomic.dvd_X_pow_sub_one m ℤ

@[blueprint "thm:companion-cycl-order"
  (statement := /-- $\mathrm{ord}(C(\Phi_m)) = m$ for $m \geq 2$. The order is exactly $m$
  because: (1) $\Phi_m \mid X^m - 1$ implies $C(\Phi_m)^m = I$, and (2) if $C(\Phi_m)^d = I$
  for $d < m$, then $\Phi_m$ would divide $X^d - 1$, contradicting that primitive $m$-th
  roots of unity are not $d$-th roots of unity for $d < m$.
  \uses{lem:companion-cycl-pow, lem:companion-aeval-zero} -/)
  (proof := /-- The order is at most $m$ since $\Phi_m \mid X^m - 1$ implies $C(\Phi_m)^m = I$.
  For the lower bound: if $C(\Phi_m)^d = I$ for $d < m$, then $\Phi_m \mid X^d - 1$,
  but this contradicts that primitive $m$-th roots of unity are not $d$-th roots. -/)]
theorem companion_cyclotomic_orderOf (m : ℕ) (hm : 2 ≤ m)
    (hn : 0 < (cyclotomic m ℤ).natDegree) :
    orderOf (companion (cyclotomic m ℤ) (cyclotomic.monic m ℤ) hn) = m := by
  -- Use orderOf_eq_iff: need to show A^m = 1 and forall k, 0 < k < m -> A^k != 1
  let A := companion (cyclotomic m ℤ) (cyclotomic.monic m ℤ) hn
  have hm_pos : 0 < m := Nat.lt_of_lt_of_le (by norm_num : 0 < 2) hm
  rw [orderOf_eq_iff hm_pos]
  constructor
  · -- A^m = 1
    exact companion_cyclotomic_pow_eq_one m hm_pos hn
  · -- For k < m, 0 < k -> A^k != 1
    intro k hk hk_pos hAk
    -- If A^k = 1, then aeval A (X^k - 1) = 0
    have haeval_zero : aeval A (X ^ k - (1 : ℤ[X])) = 0 := by
      simp only [map_sub, map_pow, aeval_X, map_one]
      rw [hAk, sub_self]
    -- We also have aeval A (cyclotomic m Z) = 0
    have hcycl_zero : aeval A (cyclotomic m ℤ) = 0 :=
      companion_aeval_eq_zero (cyclotomic m ℤ) (cyclotomic.monic m ℤ) hn
    -- Map everything to Q and work there
    -- Let A_Q be the matrix over Q
    let A_Q := A.map (algebraMap ℤ ℚ)
    -- Both polynomials annihilate A_Q
    have haeval_Q_zero : aeval A_Q ((X ^ k - 1 : ℤ[X]).map (algebraMap ℤ ℚ)) = 0 := by
      have : A_Q = (Algebra.ofId ℤ ℚ).mapMatrix A := rfl
      rw [this, aeval_map_algebraMap, aeval_algHom_apply, haeval_zero, map_zero]
    have hcycl_Q_zero : aeval A_Q ((cyclotomic m ℤ).map (algebraMap ℤ ℚ)) = 0 := by
      have : A_Q = (Algebra.ofId ℤ ℚ).mapMatrix A := rfl
      rw [this, aeval_map_algebraMap, aeval_algHom_apply, hcycl_zero, map_zero]
    -- Simplify the mapped polynomials
    simp only [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_one]
      at haeval_Q_zero
    -- Convert algebraMap Z Q to Int.castRingHom Q for map_cyclotomic_int
    have hmap_eq : (cyclotomic m ℤ).map (algebraMap ℤ ℚ) = cyclotomic m ℚ := by
      have h1 : algebraMap ℤ ℚ = Int.castRingHom ℚ := rfl
      rw [h1, map_cyclotomic_int]
    rw [hmap_eq] at hcycl_Q_zero
    -- minpoly Q A_Q divides both X^k - 1 and cyclotomic m Q
    have hdvd1 : minpoly ℚ A_Q ∣ (X ^ k - 1 : ℚ[X]) := minpoly.dvd ℚ A_Q haeval_Q_zero
    have hdvd2 : minpoly ℚ A_Q ∣ cyclotomic m ℚ := minpoly.dvd ℚ A_Q hcycl_Q_zero
    -- minpoly divides charpoly, and charpoly = cyclotomic m Q
    have hcharpoly : A_Q.charpoly = cyclotomic m ℚ := by
      -- charpoly(A.map f) = (charpoly A).map f for ring homs
      have h1 : A_Q.charpoly = (A.charpoly).map (algebraMap ℤ ℚ) := by
        rw [Matrix.charpoly_map]
      rw [h1, companion_charpoly, hmap_eq]
    -- cyclotomic m Q is irreducible over Q
    have hirr : Irreducible (cyclotomic m ℚ) := cyclotomic.irreducible_rat hm_pos
    -- Since minpoly | cyclotomic (irreducible), minpoly = 1 or minpoly = cyclotomic
    -- But minpoly has degree >= 1 (A_Q is not in Q), so minpoly = cyclotomic m Q (up to unit)
    have hminpoly_eq : minpoly ℚ A_Q = cyclotomic m ℚ := by
      have hdvd := Matrix.minpoly_dvd_charpoly A_Q
      rw [hcharpoly] at hdvd
      -- minpoly | cyclotomic, cyclotomic irreducible
      -- By Irreducible.dvd_iff: minpoly | cycl <-> IsUnit minpoly or Associated cycl minpoly
      rcases hirr.dvd_iff.mp hdvd with hunit | hassoc
      · -- minpoly is unit, impossible since minpoly is monic and evaluates to zero at A_Q
        exfalso
        -- If minpoly is a unit, it must be a constant polynomial
        -- But minpoly is monic, so it would have to be 1
        -- But aeval A_Q (minpoly) = 0, so 1 = 0, contradiction
        have hmonic := minpoly.monic (Matrix.isIntegral A_Q)
        have haeval_minpoly := minpoly.aeval ℚ A_Q
        -- For a unit polynomial over a field to be monic, it must equal 1
        have hunit_eq : minpoly ℚ A_Q = 1 := by
          rcases Polynomial.isUnit_iff.mp hunit with ⟨c, hc, heq⟩
          rw [← heq] at hmonic
          -- Monic (C c) means leadingCoeff (C c) = 1
          -- For nonzero c, leadingCoeff (C c) = c
          -- So c = 1
          have hc_one : c = 1 := by
            unfold Polynomial.Monic at hmonic
            simp only [Polynomial.leadingCoeff_C] at hmonic
            exact hmonic
          simp [← heq, hc_one]
        rw [hunit_eq] at haeval_minpoly
        simp only [Polynomial.aeval_one] at haeval_minpoly
        -- haeval_minpoly : (1 : Matrix _ _ Q) = 0, which is false
        -- The matrix ring is nontrivial since the dimension is positive
        haveI : Nonempty (Fin (cyclotomic m ℤ).natDegree) := ⟨⟨0, hn⟩⟩
        -- (1 : Matrix n n R) (i, i) = 1 != 0 for nontrivial R
        have h1ne0 : (1 : Matrix (Fin (cyclotomic m ℤ).natDegree)
            (Fin (cyclotomic m ℤ).natDegree) ℚ) ≠ 0 := by
          intro h0
          have : (1 : Matrix (Fin (cyclotomic m ℤ).natDegree)
              (Fin (cyclotomic m ℤ).natDegree) ℚ) ⟨0, hn⟩ ⟨0, hn⟩ =
              (0 : Matrix (Fin (cyclotomic m ℤ).natDegree)
              (Fin (cyclotomic m ℤ).natDegree) ℚ) ⟨0, hn⟩ ⟨0, hn⟩ := by rw [h0]
          simp only [Matrix.one_apply_eq, Matrix.zero_apply] at this
          exact one_ne_zero this
        exact h1ne0 haeval_minpoly
      · -- Associated cyclotomic minpoly, so they're equal since both are monic
        have hmonic1 := minpoly.monic (Matrix.isIntegral A_Q)
        have hmonic2 := cyclotomic.monic m ℚ
        exact eq_of_monic_of_associated hmonic1 hmonic2 hassoc.symm
    -- So cyclotomic m Q | X^k - 1
    rw [hminpoly_eq] at hdvd1
    -- But cyclotomic m only divides X^n - 1 when m | n
    -- X^k - 1 = prod_{d | k} cyclotomic d Q
    -- So cyclotomic m | X^k - 1 iff m in k.divisors iff m | k
    have hm_dvd_k : m ∣ k := by
      -- Use that X^k - 1 = prod_{d | k} cyclotomic d
      rw [← prod_cyclotomic_eq_X_pow_sub_one hk_pos ℚ] at hdvd1
      -- cyclotomic m Q divides the product prod_{d | k} cyclotomic d Q
      -- Since cyclotomic polynomials are pairwise coprime (for different indices),
      -- and cyclotomic m is irreducible, it must equal one of the factors
      -- i.e., m in k.divisors
      have hcoprime : ∀ i j : ℕ, i ∈ k.divisors → j ∈ k.divisors → i ≠ j →
          IsCoprime (cyclotomic i ℚ) (cyclotomic j ℚ) := by
        intro i j _ _ hij
        exact cyclotomic.isCoprime_rat hij
      -- cyclotomic m is irreducible
      -- If it divides a product of coprimes, it must divide one factor
      -- Use Finset.prod_dvd_of_isUnit_of_dvd or similar
      by_contra hndvd
      have hm_notin : m ∉ k.divisors := by
        simp only [Nat.mem_divisors]
        push_neg
        intro hd
        -- If m | k then m <= k (since k > 0), but k < m, contradiction
        have hle : m ≤ k := Nat.le_of_dvd hk_pos hd
        omega
      -- cyclotomic m | prod_{d | k} cyclotomic d, but m notin k.divisors
      -- This is impossible because cyclotomics for different indices are coprime
      have : cyclotomic m ℚ ∣ ∏ d ∈ k.divisors, cyclotomic d ℚ := hdvd1
      -- If p is irreducible and divides a product of pairwise coprime terms,
      -- it must divide one of them
      have hex : ∃ d ∈ k.divisors, cyclotomic m ℚ ∣ cyclotomic d ℚ := by
        -- Use the fact that irreducible dividing product of coprime terms
        -- means it divides one of them
        -- This follows from unique factorization
        have huf := UniqueFactorizationMonoid.irreducible_iff_prime.mp hirr
        exact Prime.exists_mem_finset_dvd huf this
      obtain ⟨d, hd_mem, hdvd_d⟩ := hex
      -- cyclotomic m | cyclotomic d, both monic irreducible, so they're equal
      -- Since cyclotomic is injective on indices (over CharZero), m = d
      have heq : m = d := by
        have hirr_d : Irreducible (cyclotomic d ℚ) := by
          have hd_pos : 0 < d := Nat.pos_of_mem_divisors hd_mem
          exact cyclotomic.irreducible_rat hd_pos
        -- Two monic irreducible polynomials where one divides the other must be equal
        have hmonic_m := cyclotomic.monic m ℚ
        have hmonic_d := cyclotomic.monic d ℚ
        have hassoc : Associated (cyclotomic m ℚ) (cyclotomic d ℚ) :=
          associated_of_dvd_dvd hdvd_d (hirr.dvd_symm hirr_d hdvd_d)
        exact cyclotomic_injective (eq_of_monic_of_associated hmonic_m hmonic_d hassoc)
      rw [heq] at hm_notin
      exact hm_notin hd_mem
    -- m | k and 0 < k < m is a contradiction
    have : k < m := hk
    have : m ≤ k := Nat.le_of_dvd hk_pos hm_dvd_k
    omega

/-! ### Integer matrix membership -/

@[blueprint "thm:companion-cycl-mem"
  (statement := /-- $m \in \mathrm{Ord}_{\varphi(m)}$ via $C(\Phi_m)$. Since
  $\deg(\Phi_m) = \varphi(m)$, the companion matrix $C(\Phi_m)$ is $\varphi(m) \times \varphi(m)$
  with integer entries, and has order exactly $m$ by \texttt{companion\_cyclotomic\_orderOf}.
  \uses{thm:companion-cycl-order} -/)
  (proof := /-- The companion matrix $C(\Phi_m)$ witnesses the membership: it is an integer matrix
  of dimension $\deg(\Phi_m) = \varphi(m)$ with multiplicative order exactly $m$. -/)]
theorem companion_cyclotomic_mem_integerMatrixOrders (m : ℕ) (hm : 2 ≤ m)
    (hn : 0 < (cyclotomic m ℤ).natDegree) :
    m ∈ Crystallographic.integerMatrixOrders (cyclotomic m ℤ).natDegree := by
  use companion (cyclotomic m ℤ) (cyclotomic.monic m ℤ) hn
  constructor
  · exact companion_cyclotomic_orderOf m hm hn
  · omega

@[blueprint "thm:mem-orders-totient"
  (statement := /-- For $m \geq 2$, $m \in \mathrm{Ord}_{\varphi(m)}$. This is the key
  existence result: for every $m \geq 2$, there exists an integer matrix of dimension
  $\varphi(m)$ with multiplicative order exactly $m$, namely the companion matrix of $\Phi_m$.
  \uses{thm:companion-cycl-mem} -/)
  (proof := /-- Apply the cyclotomic companion membership theorem after noting that
  $\deg(\Phi_m) = \varphi(m)$. -/)]
theorem mem_integerMatrixOrders_totient (m : ℕ) (hm : 2 ≤ m) :
    m ∈ Crystallographic.integerMatrixOrders (Nat.totient m) := by
  have hdeg : (cyclotomic m ℤ).natDegree = Nat.totient m := Polynomial.natDegree_cyclotomic m ℤ
  have htot_pos : 0 < Nat.totient m := Nat.totient_pos.mpr (by omega)
  have hn : 0 < (cyclotomic m ℤ).natDegree := by omega
  rw [← hdeg]
  exact companion_cyclotomic_mem_integerMatrixOrders m hm hn

end Crystallographic
