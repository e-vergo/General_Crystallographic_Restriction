/-
Copyright (c) 2026 Eric Vergo. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Eric Vergo
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Algebra.GCDMonoid.Nat
import Mathlib.Algebra.IsPrimePow
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Factorization.Basic

import Architect

/-!
# Auxiliary Lemmas for Crystallographic Restriction

This file contains general-purpose lemmas used throughout the crystallographic
restriction theorem proof that could potentially be upstreamed to Mathlib.

## Main results

* `Finset.sum_le_prod_of_all_ge_two` - For finsets where all values are ≥ 2, sum ≤ product
* `orderOf_neg_eq_two_mul_of_odd` - Order of -A is 2 * order of A when order is odd

-/

namespace Crystallographic

/-! ### Finset sum/product inequalities -/

/-- For a nonempty finset where all values of f are at least 2, we have sum f at most prod f. -/
@[blueprint "lem:sum-le-prod"
  (statement := /-- For a finset where all values $\geq 2$, the sum is at most the product. -/)]
lemma Finset.sum_le_prod_of_all_ge_two {α : Type*} [DecidableEq α]
    (s : Finset α) (f : α → ℕ) (hf : ∀ x ∈ s, 2 ≤ f x) :
    ∑ x ∈ s, f x ≤ ∏ x ∈ s, f x := by
  induction s using Finset.induction with
  | empty => simp
  | @insert a s' ha IH =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha]
    have h2_a : 2 ≤ f a := hf a (Finset.mem_insert_self a s')
    by_cases hs_empty : s' = ∅
    · simp [hs_empty]
    · have hs_nonempty : s'.Nonempty := Finset.nonempty_of_ne_empty hs_empty
      have hs'_ge2 : ∀ x ∈ s', 2 ≤ f x := fun x hx => hf x (Finset.mem_insert_of_mem hx)
      have h2_prod : 2 ≤ ∏ x ∈ s', f x := by
        obtain ⟨b, hb⟩ := hs_nonempty
        have h1 : ∀ x ∈ s', 1 ≤ f x := fun x hx => Nat.one_le_of_lt (hs'_ge2 x hx)
        calc ∏ x ∈ s', f x ≥ f b := Finset.single_le_prod' h1 hb
          _ ≥ 2 := hs'_ge2 b hb
      have IH' := IH hs'_ge2
      calc f a + ∑ x ∈ s', f x
          ≤ f a + ∏ x ∈ s', f x := by omega
        _ ≤ f a * ∏ x ∈ s', f x := Nat.add_le_mul h2_a h2_prod

/-! ### Finset lcm and factorization -/

/-- The factorization of a finset lcm at any prime is at most the supremum. -/
@[blueprint "lem:lcm-factorization-le-sup"
  (statement := /-- The factorization of $\mathrm{lcm}(S)$ at prime $q$ is bounded by
  $\sup_{x \in S} v_q(x)$. -/)]
lemma Finset.lcm_factorization_le_sup {α : Type*} [DecidableEq α] (S : Finset α) (f : α → ℕ)
    (q : ℕ) (hS_ne_zero : ∀ x ∈ S, f x ≠ 0) :
    (S.lcm f).factorization q ≤ S.sup (fun x => (f x).factorization q) := by
  induction S using Finset.induction with
  | empty =>
    simp only [Finset.lcm_empty, Nat.factorization_one, Finsupp.coe_zero, Pi.zero_apply,
      Finset.sup_empty, bot_eq_zero, le_refl]
  | @insert a s' ha IH =>
    simp only [Finset.lcm_insert, Finset.sup_insert]
    by_cases hs'_empty : s' = ∅
    · simp [hs'_empty]
    · have hs'_ne_zero : s'.lcm f ≠ 0 := by
        rw [ne_eq, Finset.lcm_eq_zero_iff]
        push_neg
        intro x hx
        exact hS_ne_zero x (Finset.mem_insert_of_mem hx)
      have ha_ne_zero : f a ≠ 0 := hS_ne_zero a (Finset.mem_insert_self a s')
      rw [lcm_eq_nat_lcm, Nat.factorization_lcm ha_ne_zero hs'_ne_zero]
      simp only [Finsupp.sup_apply, sup_le_iff]
      constructor
      · exact le_sup_left
      · have hIH := IH (fun x hx => hS_ne_zero x (Finset.mem_insert_of_mem hx))
        exact le_trans hIH le_sup_right

/-! ### Prime power divisor lemmas -/

/-- For a prime power, if a finset of divisors has lcm equal to the prime power, then
the prime power is in the finset. -/
@[blueprint "lem:primePow-mem-of-lcm-eq"
  (statement := /-- If $\mathrm{lcm}(S) = p^k$ and all elements of $S$ divide $p^k$,
  then $p^k \in S$. -/)]
lemma primePow_mem_of_lcm_eq {p k : ℕ} (hp : p.Prime) (hk : 0 < k) (S : Finset ℕ)
    (hS_sub : ∀ d ∈ S, d ∣ p ^ k) (hS_lcm : S.lcm id = p ^ k) :
    p ^ k ∈ S := by
  by_contra hm_not_in
  -- All elements of S are proper divisors of p^k, so they divide p^(k-1)
  have hall_lt : ∀ d ∈ S, d < p ^ k := fun d hd =>
    Nat.lt_of_le_of_ne (Nat.le_of_dvd (Nat.pow_pos hp.pos) (hS_sub d hd))
      (fun heq => hm_not_in (heq ▸ hd))
  have hall_le : ∀ d ∈ S, d ∣ p ^ (k - 1) := by
    intro d hd
    have hdvd := hS_sub d hd
    have hd_lt := hall_lt d hd
    have hpr : Prime p := Nat.Prime.prime hp
    rw [dvd_prime_pow hpr] at hdvd
    obtain ⟨j, _, hassoc⟩ := hdvd
    have hd_eq := associated_iff_eq.mp hassoc
    rw [hd_eq] at hd_lt
    have hj_lt : j < k := (Nat.pow_lt_pow_iff_right hp.one_lt).mp hd_lt
    have hj_le : j ≤ k - 1 := Nat.lt_succ_iff.mp (by omega)
    rw [hd_eq]
    exact Nat.pow_dvd_pow p hj_le
  have hlcm_le : S.lcm id ∣ p ^ (k - 1) := Finset.lcm_dvd_iff.mpr (fun d hd => hall_le d hd)
  rw [hS_lcm] at hlcm_le
  have hle : p ^ k ≤ p ^ (k - 1) := Nat.le_of_dvd (Nat.pow_pos hp.pos) hlcm_le
  have hpow_strict : p ^ (k - 1) < p ^ k :=
    Nat.pow_lt_pow_right hp.one_lt (Nat.sub_lt hk Nat.one_pos)
  omega

end Crystallographic
