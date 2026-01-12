/-
Copyright (c) 2026 Eric Vergo. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Eric Vergo
-/
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.LinearAlgebra.Matrix.Charpoly.Minpoly
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots

import Architect

import Crystallographic.FiniteOrder.Order
import Crystallographic.Psi.Basic
import Crystallographic.Psi.Bounds
import Crystallographic.Companion.Cyclotomic

/-!
# The Crystallographic Restriction Theorem - Backward Direction

This file proves the backward direction of the crystallographic restriction theorem:
if psi(m) <= N, then there exists an N x N integer matrix with order m.

## Main results

* `mem_integerMatrixOrders_of_psi_le` - Backward direction: psi(m) <= N implies order m achievable.

## Proof Strategy

1. Construct companion matrix of cyclotomic polynomial Phi_m over Z
2. This has size phi(m) x phi(m) and order m
3. For composite m, use block diagonal of companion matrices for prime power factors
4. Total size is psi(m) <= N, pad with identity to get N x N matrix

## References

* Sasse, R. (2020). "Crystallographic Groups"
-/

namespace Crystallographic

open Matrix Polynomial

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
@[blueprint "lem:orderOf-permMatrix"
  (statement := /-- $\mathrm{ord}(P_\sigma) = \mathrm{ord}(\sigma)$ for permutation matrix. -/)]
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

/-- The finRotate permutation has order n for n at least 2. -/
@[blueprint "lem:orderOf-finRotate"
  (statement := /-- $\mathrm{ord}(\mathrm{finRotate}(n)) = n$. -/)]
lemma orderOf_finRotate (n : ℕ) (hn : 2 ≤ n) : orderOf (finRotate n) = n := by
  have hcycle := isCycle_finRotate_of_le hn
  have hord := Equiv.Perm.IsCycle.orderOf hcycle
  have hsupp := support_finRotate_of_le hn
  rw [hord, hsupp, Finset.card_univ, Fintype.card_fin]

/-- finRotate permutation matrix has order n for n >= 2. -/
lemma orderOf_permMatrix_finRotate (n : ℕ) (hn : 2 ≤ n) :
    orderOf ((finRotate n).permMatrix ℤ) = n := by
  rw [orderOf_permMatrix', orderOf_finRotate n hn]

/-- Order n is achievable by an n x n integer matrix for n at least 2. -/
@[blueprint "lem:mem-integerMatrixOrders-self"
  (statement := /-- $m \in \mathrm{Ord}_m$ for $m \geq 2$ via permutation matrix. -/)]
lemma mem_integerMatrixOrders_self (n : ℕ) (hn : 2 ≤ n) : n ∈ integerMatrixOrders n := by
  use (finRotate n).permMatrix ℤ
  constructor
  · exact orderOf_permMatrix_finRotate n hn
  · omega

/-! ## Backward direction: Dimension bound implies order is achievable -/

/-- Helper: The identity matrix has order 1, contributing dimension 0. -/
@[blueprint "lem:order-one-achievable"
  (statement := /-- Order 1 is achievable: $1 \in \mathrm{Ord}_N$ for any $N$. -/)]
lemma order_one_achievable (N : ℕ) : 1 ∈ integerMatrixOrders N :=
  one_mem_integerMatrixOrders N

/-- Helper: The negation of identity has order 2, contributing dimension 0 for N at least 1. -/
@[blueprint "lem:order-two-achievable"
  (statement := /-- Order 2 is achievable: $2 \in \mathrm{Ord}_N$ for $N \geq 1$. -/)]
lemma order_two_achievable (N : ℕ) [NeZero N] : 2 ∈ integerMatrixOrders N :=
  two_mem_integerMatrixOrders N

/-- For prime power with p odd or k at least 2, p^k is in integerMatrixOrders(psi(p^k)). -/
@[blueprint "thm:primePow-mem-integerMatrixOrders-psi"
  (statement := /-- $p^k \in \mathrm{Ord}_{\psi(p^k)}$ for prime powers with $p$ odd or $k \geq 2$.
  -/)]
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
@[blueprint "thm:backward-direction"
  (statement := /-- \textbf{Backward Direction:} If $\psi(m) \leq N$, then $m \in \mathrm{Ord}_N$.

  \textbf{Mathematical context:}
  The companion matrix of a monic polynomial $p(X)$ has $p(X)$ as both its characteristic
  and minimal polynomial. For the cyclotomic polynomial $\Phi_m$, the companion matrix $C_m$
  satisfies $\Phi_m(C_m) = 0$, so $C_m^m = I$, and since $\Phi_m$ is minimal (irreducible over
  $\mathbb{Q}$ and dividing $X^m - 1$ but not $X^k - 1$ for $k < m$), we get $\mathrm{ord}(C_m) = m$.
  The key optimization in the $\psi$ function is that $\psi(2) = 0$: order 2 is achieved by $-I$
  in any dimension, so we do not need to ``pay'' $\varphi(2) = 1$ for the factor of 2.

  \textbf{Proof by explicit construction:}
  \begin{enumerate}
  \item For $m = 1$: Use the identity matrix (any dimension).
  \item For $m = 2$: Use $-I$ (dimension $\geq 1$), achieving order 2 without adding to $\psi$.
  \item For odd prime power $p^k$: The companion matrix of $\Phi_{p^k}$ has size $\varphi(p^k)$.
  \item For $2^k$ with $k \geq 2$: The companion matrix of $\Phi_{2^k}$ has size $\varphi(2^k) = 2^{k-1}$.
  \item For $m = 2m'$ with $m'$ odd: If $A$ has order $m'$, then $-A$ has order $2m'$ (same dimension).
  \item For general $m = \prod p_i^{k_i}$: Block diagonal of companion matrices for $p_i^{k_i}$
        with $p_i \neq 2$ or $k_i \geq 2$. The orders combine via $\mathrm{lcm}$ (which equals
        the product for coprime factors), giving total order $m$ in dimension $\psi(m)$.
  \item Pad with identity blocks to reach size $N \times N$ (padding does not change order).
  \end{enumerate}
  \uses{integerMatrixOrders-def, psi-def, companion-def, thm:companion-charpoly,
        thm:companion-cycl-order, thm:mem-orders-totient} --/)
  (proof := /-- We construct a matrix of order $m$ in dimension $\psi(m)$ by taking block diagonals
  of companion matrices for cyclotomic polynomials $\Phi_{p^k}$ of each prime power factor.
  The companion matrix $C(\Phi_{p^k})$ has order exactly $p^k$ and size $\varphi(p^k)$.
  Block diagonal matrices have order equal to the lcm of block orders, which equals $m$
  for coprime factors. Identity padding extends to dimension $N \geq \psi(m)$. --/)]
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
      -- or use companion matrices of cyclotomic polynomials
      by_cases hle : m ≤ N
      -- Case m <= N: use permutation matrix of finRotate m
      · have hm2 : 2 ≤ m := by omega
        exact integerMatrixOrders_mono hle (mem_integerMatrixOrders_self m hm2)
      -- Case m > N: use companion matrices of cyclotomic polynomials
      · push_neg at hle
        -- For m >= 3 with psi(m) <= N < m, we use companion matrices.
        -- Since φ(m) >= psi(m), we have m ∈ integerMatrixOrders(φ(m)),
        -- and by monotonicity m ∈ integerMatrixOrders(N) when psi(m) <= N.
        --
        -- Handle small cases explicitly, then general case
        rcases Nat.lt_trichotomy m 3 with hm_lt3 | rfl | hm_gt3
        · omega -- m < 3 but m > 2, contradiction
        · -- m = 3: psi(3) = 2 = φ(3), use companion of Φ_3
          have hN2 : 2 ≤ N := by simp only [Crystallographic.psi_three] at hpsi; omega
          exact integerMatrixOrders_mono hN2 (mem_integerMatrixOrders_totient 3 (by omega))
        · rcases Nat.lt_trichotomy m 4 with hm_lt4 | rfl | hm_gt4
          · omega -- 3 < m < 4, impossible for naturals
          · -- m = 4: psi(4) = 2 = φ(4), use companion of Φ_4
            have hN2 : 2 ≤ N := by simp only [Crystallographic.psi_four] at hpsi; omega
            exact integerMatrixOrders_mono hN2 (mem_integerMatrixOrders_totient 4 (by omega))
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
            · -- m = 6: psi(6) = 2 = φ(6), use companion of Φ_6
              have hN2 : 2 ≤ N := by simp only [Crystallographic.psi_six] at hpsi; omega
              exact integerMatrixOrders_mono hN2 (mem_integerMatrixOrders_totient 6 (by omega))
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
              · push_neg at htot
                have hmem := mem_integerMatrixOrders_psi m (by omega) (by omega)
                exact integerMatrixOrders_mono hpsi hmem

end Crystallographic
