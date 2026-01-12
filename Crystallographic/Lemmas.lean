/-
Copyright (c) 2026 Eric Vergo. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Eric Vergo
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Algebra.GCDMonoid.Nat
import Mathlib.Algebra.IsPrimePow
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.GCD.BigOperators
import Mathlib.Data.Nat.Totient
import Mathlib.GroupTheory.OrderOfElement

import Architect

import Crystallographic.FiniteOrder.Basic

/-!
# Auxiliary Lemmas for Crystallographic Restriction

This file contains general-purpose lemmas used throughout the crystallographic
restriction theorem proof that could potentially be upstreamed to Mathlib.

## Main results

* `Finset.sum_le_prod_of_all_ge_two` - For finsets where all values are >= 2, sum <= product
* `orderOf_neg_of_odd_order` - If A has odd order k, then -A has order 2*k

-/

namespace Crystallographic

/-! ### Finset sum/product inequalities -/

/-- For a nonempty finset where all values of f are at least 2, we have sum f at most prod f. -/
@[blueprint "lem:sum-le-prod"
  (statement := /-- For a finset where all values $\geq 2$, the sum is at most the product. -/)
  (proof := /-- By induction on the size of the finset. Base case: empty sum is $0 \leq 1$ (empty product).
  Inductive step: if $\sum_{x \in s} f(x) \leq \prod_{x \in s} f(x)$ and $f(a) \geq 2$, then
  $\sum_{x \in s \cup \{a\}} f(x) = f(a) + \sum_s f \leq f(a) \cdot \prod_s f \leq \prod_{s \cup \{a\}} f$
  using $1 + y \leq 2y$ for $y \geq 1$ and $f(a) \geq 2$. -/)]
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
  $\sup_{x \in S} v_q(x)$. -/)
  (proof := /-- The $q$-adic valuation of $\mathrm{lcm}(S)$ is the maximum of $q$-adic valuations over elements of $S$.
  This follows from the definition of lcm via factorization: $v_q(\mathrm{lcm}(S)) = \sup_{x \in S} v_q(x)$. -/)]
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
  then $p^k \in S$. -/)
  (proof := /-- Since $\mathrm{lcm}(S) = p^k$ and all elements divide $p^k$, each element has form $p^j$ for some $j \leq k$.
  Taking lcm over these powers gives $p^{\max_j} = p^k$, so some element must have $j = k$, meaning $p^k \in S$. -/)]
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

/-! ### Euler's totient function -/

/-- Euler's totient function is at least 2 for any n > 2. -/
@[blueprint "lem:totient-ge-two"
  (statement := /-- For $n > 2$, we have $\varphi(n) \geq 2$. -/)
  (proof := /-- Since $n > 2$, we have $n \neq 1$ and $n \neq 2$.
  By `Nat.totient_eq_one_iff`, $\varphi(n) = 1$ iff $n \in \{1, 2\}$.
  Since $n \notin \{1, 2\}$, we have $\varphi(n) \neq 1$.
  Also $\varphi(n) \neq 0$ since $n > 0$. Therefore $\varphi(n) \geq 2$. -/)]
theorem totient_ge_two_of_gt_two (n : ℕ) (hn : 2 < n) : 2 ≤ Nat.totient n := by
  have hn_pos : 0 < n := by omega
  have hn_ne_one : n ≠ 1 := by omega
  have hn_ne_two : n ≠ 2 := by omega
  have htot_pos : 0 < Nat.totient n := Nat.totient_pos.mpr hn_pos
  have htot_ne_one : Nat.totient n ≠ 1 := by
    intro htot_eq1
    have h12 := Nat.totient_eq_one_iff.mp htot_eq1
    rcases h12 with h1 | h2
    · exact hn_ne_one h1
    · exact hn_ne_two h2
  omega

/-! ### Coprime product divisibility -/

/-- If each f(a) divides d and they're pairwise coprime, then ∏ f(a) divides d. -/
@[blueprint "lem:prod-coprime-dvd"
  (statement := /-- If each $f(a)$ divides $d$ and the $f(a)$ are pairwise coprime,
  then $\prod_{a \in S} f(a)$ divides $d$. -/)
  (proof := /-- By Finset induction. Empty case: $1 \mid d$ trivially.
  Insert case: we have $f(q) \mid d$ and $\prod_{s'} f(r) \mid d$ by IH.
  Show $f(q)$ is coprime to $\prod_{s'} f(r)$ using `Nat.Coprime.prod_right`,
  then apply `Nat.Coprime.mul_dvd_of_dvd_of_dvd`. -/)]
theorem Finset.prod_coprime_dvd {α : Type*} [DecidableEq α] (S : Finset α) (f : α → ℕ) (d : ℕ)
    (h_dvd : ∀ a ∈ S, f a ∣ d)
    (h_coprime : ∀ a₁ ∈ S, ∀ a₂ ∈ S, a₁ ≠ a₂ → (f a₁).Coprime (f a₂)) :
    (∏ a ∈ S, f a) ∣ d := by
  induction S using Finset.induction with
  | empty => simp
  | @insert q s' hq_notin IH =>
    rw [Finset.prod_insert hq_notin]
    have hq_dvd : f q ∣ d := h_dvd q (Finset.mem_insert_self q s')
    have hs'_dvd : (∏ r ∈ s', f r) ∣ d := by
      apply IH
      · intro r hr; exact h_dvd r (Finset.mem_insert_of_mem hr)
      · intro a₁ ha₁ a₂ ha₂ hne
        exact h_coprime a₁ (Finset.mem_insert_of_mem ha₁) a₂
          (Finset.mem_insert_of_mem ha₂) hne
    have h_cop : (f q).Coprime (∏ r ∈ s', f r) := by
      apply Nat.Coprime.prod_right
      intro r hr
      have hne : q ≠ r := fun heq => hq_notin (heq ▸ hr)
      exact h_coprime q (Finset.mem_insert_self q s') r
        (Finset.mem_insert_of_mem hr) hne
    exact h_cop.mul_dvd_of_dvd_of_dvd hq_dvd hs'_dvd

/-! ### Totient and products -/

/-- Totient distributes over products of pairwise coprime values. -/
@[blueprint "lem:totient-prod-coprime"
  (statement := /-- For pairwise coprime $\{f(a)\}_{a \in S}$, we have
  $\varphi(\prod_{a \in S} f(a)) = \prod_{a \in S} \varphi(f(a))$. -/)
  (proof := /-- By Finset induction. Empty case: $\varphi(1) = 1$ equals empty product.
  Insert case: use $\varphi(ab) = \varphi(a)\varphi(b)$ for coprime $a, b$
  (`Nat.totient_mul`), where coprimality follows from `Nat.Coprime.prod_right`. -/)]
theorem Nat.totient_finset_prod_of_coprime {α : Type*} [DecidableEq α] (S : Finset α) (f : α → ℕ)
    (h_coprime : ∀ a₁ ∈ S, ∀ a₂ ∈ S, a₁ ≠ a₂ → (f a₁).Coprime (f a₂)) :
    Nat.totient (∏ a ∈ S, f a) = ∏ a ∈ S, Nat.totient (f a) := by
  induction S using Finset.induction with
  | empty => simp
  | @insert q s' hq_notin IH =>
    rw [Finset.prod_insert hq_notin, Finset.prod_insert hq_notin]
    have h_cop_q_s : (f q).Coprime (∏ r ∈ s', f r) := by
      apply Nat.Coprime.prod_right
      intro r hr
      have hne : q ≠ r := fun heq => hq_notin (heq ▸ hr)
      exact h_coprime q (Finset.mem_insert_self q s') r
        (Finset.mem_insert_of_mem hr) hne
    rw [Nat.totient_mul h_cop_q_s]
    congr 1
    apply IH
    intro a₁ ha₁ a₂ ha₂ hne
    exact h_coprime a₁ (Finset.mem_insert_of_mem ha₁) a₂
      (Finset.mem_insert_of_mem ha₂) hne

/-! ### Matrix order for negation -/

/-- If A has odd order k in a matrix ring over Z, then -A has order 2*k.
This uses orderOf(-1) = 2 (in char 0), commutativity of -1 with A,
and gcd(2, k) = 1 for odd k. -/
@[blueprint "lem:orderOf-neg-of-odd-order"
  (statement := /-- If $A$ has odd order $k$, then $-A$ has order $2k$. -/)
  (proof := /-- We have $-A = (-1) \cdot A$ where $-1$ commutes with $A$.
  In characteristic $0$, $\mathrm{ord}(-1) = 2$. Since $k$ is odd,
  $\gcd(2, k) = 1$, so by the product formula for commuting elements with
  coprime orders, $\mathrm{ord}(-A) = \mathrm{ord}(-1) \cdot \mathrm{ord}(A) = 2k$. -/)]
theorem orderOf_neg_of_odd_order {n : ℕ} [NeZero n] (k : ℕ) (hk_odd : Odd k)
    (A : Matrix (Fin n) (Fin n) ℤ) (hA_ord : orderOf A = k) :
    orderOf (-A) = 2 * k := by
  -- Express -A as (-1) * A
  have hneg_eq : -A = (-1 : Matrix (Fin n) (Fin n) ℤ) * A := by simp
  rw [hneg_eq]
  -- -1 and A commute
  have hcomm : Commute (-1 : Matrix (Fin n) (Fin n) ℤ) A := Commute.neg_one_left A
  -- orderOf(-1) = 2 in char 0
  have hord_neg1 : orderOf (-1 : Matrix (Fin n) (Fin n) ℤ) = 2 := by
    rw [orderOf_neg_one, ringChar_matrix_int]
    simp
  -- Coprimality: gcd(2, k) = 1 since k is odd
  have hcop : Nat.Coprime 2 k := Nat.Coprime.symm (Odd.coprime_two_right hk_odd)
  have hord_cop : Nat.Coprime (orderOf (-1 : Matrix (Fin n) (Fin n) ℤ)) (orderOf A) := by
    rw [hord_neg1, hA_ord]
    exact hcop
  -- Apply the product formula
  rw [hcomm.orderOf_mul_eq_mul_orderOf_of_coprime hord_cop]
  rw [hord_neg1, hA_ord]

end Crystallographic
