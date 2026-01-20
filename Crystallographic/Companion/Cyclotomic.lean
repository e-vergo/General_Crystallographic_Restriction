/-
Copyright (c) 2026 Eric Vergo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo
-/
import Dress
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Crystallographic.Companion.Basic
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

## Tags

cyclotomic polynomial, companion matrix, integer matrix, finite order, roots of unity
-/

namespace Crystallographic

open Matrix Polynomial

@[blueprint "lem:companion-cycl-pow"
  (statement := /-- $C(\Phi_m)^m = I$. Since the cyclotomic polynomial $\Phi_m$ divides
  $X^m - 1$ (as $X^m - 1 = \prod_{d \mid m} \Phi_d$), we apply
  \texttt{companion\_pow\_eq\_one\_of\_dvd}.
  \uses{thm:companion-pow-dvd} -/)
  (proof := /-- Since $\Phi_m \mid X^m - 1$ (as $X^m - 1 = \prod_{d \mid m} \Phi_d$), we apply
  the general companion power theorem to conclude $C(\Phi_m)^m = I$. -/)]
lemma companion_cyclotomic_pow_eq_one (m : ℕ)
    (hn : 0 < (cyclotomic m ℤ).natDegree) :
    (companion (cyclotomic m ℤ) (cyclotomic.monic m ℤ) hn) ^ m = 1 := by
  apply companion_pow_eq_one_of_dvd
  exact cyclotomic.dvd_X_pow_sub_one m ℤ

/-- For the companion matrix of cyclotomic m ℤ, the minimal polynomial over ℚ equals cyclotomic m ℚ.
This uses that minpoly | charpoly = cyclotomic, and cyclotomic is monic irreducible over ℚ. -/
lemma companion_cyclotomic_minpoly (m : ℕ) (hm_pos : 0 < m)
    (hn : 0 < (cyclotomic m ℤ).natDegree) :
    let A := companion (cyclotomic m ℤ) (cyclotomic.monic m ℤ) hn
    let AQ := A.map (algebraMap ℤ ℚ)
    minpoly ℚ AQ = cyclotomic m ℚ := by
  intro A AQ
  have hcharpoly : AQ.charpoly = cyclotomic m ℚ := by
    have h1 : AQ.charpoly = (A.charpoly).map (algebraMap ℤ ℚ) := by
      rw [Matrix.charpoly_map]
    have hmap_eq : (cyclotomic m ℤ).map (algebraMap ℤ ℚ) = cyclotomic m ℚ := by
      have h : algebraMap ℤ ℚ = Int.castRingHom ℚ := rfl
      rw [h, map_cyclotomic_int]
    rw [h1, companion_charpoly, hmap_eq]
  have hirr : Irreducible (cyclotomic m ℚ) := cyclotomic.irreducible_rat hm_pos
  have hdvd := Matrix.minpoly_dvd_charpoly AQ
  rw [hcharpoly] at hdvd
  rcases hirr.dvd_iff.mp hdvd with hunit | hassoc
  · -- minpoly is a unit: impossible since minpoly ≠ 1
    haveI : Nonempty (Fin (cyclotomic m ℤ).natDegree) := ⟨⟨0, hn⟩⟩
    exact (minpoly.ne_one ℚ AQ ((minpoly.monic (Matrix.isIntegral AQ)).eq_one_of_isUnit hunit)).elim
  · -- Associated: equal since both monic
    have hmonic1 := minpoly.monic (Matrix.isIntegral AQ)
    have hmonic2 := cyclotomic.monic m ℚ
    exact eq_of_monic_of_associated hmonic1 hmonic2 hassoc.symm

/-- If cyclotomic m ℚ divides X^k - 1 for 0 < k, then m ∣ k.
This uses the factorization X^k - 1 = ∏_{d|k} Φ_d and that cyclotomic polynomials
are coprime for different indices. -/
lemma dvd_of_cyclotomic_dvd_X_pow_sub_one (m k : ℕ) (hm_pos : 0 < m)
    (hk_pos : 0 < k) (hdvd : cyclotomic m ℚ ∣ (X ^ k - 1 : ℚ[X])) :
    m ∣ k := by
  have hirr : Irreducible (cyclotomic m ℚ) := cyclotomic.irreducible_rat hm_pos
  rw [← prod_cyclotomic_eq_X_pow_sub_one hk_pos ℚ] at hdvd
  by_contra hndvd
  have hm_notin : m ∉ k.divisors := by
    simp only [Nat.mem_divisors]
    push_neg
    intro hd
    have hle : m ≤ k := Nat.le_of_dvd hk_pos hd
    omega
  have hex : ∃ d ∈ k.divisors, cyclotomic m ℚ ∣ cyclotomic d ℚ := by
    have huf := UniqueFactorizationMonoid.irreducible_iff_prime.mp hirr
    exact Prime.exists_mem_finset_dvd huf hdvd
  obtain ⟨d, hd_mem, hdvd_d⟩ := hex
  have heq : m = d := by
    have hirr_d : Irreducible (cyclotomic d ℚ) := by
      have hd_pos : 0 < d := Nat.pos_of_mem_divisors hd_mem
      exact cyclotomic.irreducible_rat hd_pos
    have hmonic_m := cyclotomic.monic m ℚ
    have hmonic_d := cyclotomic.monic d ℚ
    have hassoc : Associated (cyclotomic m ℚ) (cyclotomic d ℚ) :=
      associated_of_dvd_dvd hdvd_d (hirr.dvd_symm hirr_d hdvd_d)
    exact cyclotomic_injective (eq_of_monic_of_associated hmonic_m hmonic_d hassoc)
  rw [heq] at hm_notin
  exact hm_notin hd_mem

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
  let A := companion (cyclotomic m ℤ) (cyclotomic.monic m ℤ) hn
  have hm_pos : 0 < m := Nat.lt_of_lt_of_le (by norm_num : 0 < 2) hm
  rw [orderOf_eq_iff hm_pos]
  constructor
  · exact companion_cyclotomic_pow_eq_one m hn
  · intro k hk hk_pos hAk
    have haeval_zero : aeval A (X ^ k - (1 : ℤ[X])) = 0 := by
      simp only [map_sub, map_pow, aeval_X, map_one]
      rw [hAk, sub_self]
    -- Work over ℚ where cyclotomic is irreducible
    let AQ := A.map (algebraMap ℤ ℚ)
    have haeval_Q_zero : aeval AQ ((X ^ k - 1 : ℤ[X]).map (algebraMap ℤ ℚ)) = 0 := by
      have : AQ = (Algebra.ofId ℤ ℚ).mapMatrix A := rfl
      rw [this, aeval_map_algebraMap, aeval_algHom_apply, haeval_zero, map_zero]
    simp only [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_one]
      at haeval_Q_zero
    have hdvd1 : minpoly ℚ AQ ∣ (X ^ k - 1 : ℚ[X]) := minpoly.dvd ℚ AQ haeval_Q_zero
    have hminpoly_eq : minpoly ℚ AQ = cyclotomic m ℚ := companion_cyclotomic_minpoly m hm_pos hn
    rw [hminpoly_eq] at hdvd1
    exact Nat.not_dvd_of_pos_of_lt hk_pos hk (dvd_of_cyclotomic_dvd_X_pow_sub_one m k hm_pos hk_pos hdvd1)

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

