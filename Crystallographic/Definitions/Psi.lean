/-
Copyright (c) 2026 Eric Vergo. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Eric Vergo
-/
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Nat.Factorization.Basic

/-!
# The psi function for the crystallographic restriction theorem

This file defines the function psi : ℕ → ℕ, which gives the minimum dimension N such that
an N×N integer matrix can have a given order m.

## Main definitions

* `Crystallographic.psi` - The psi function for crystallographic restriction.
  - psi(1) = 0
  - psi(2) = 0
  - psi(n) = sum over prime power factors p^k of n: if p=2 and k=1 then 0 else phi(p^k)

## Main results

* `psi_one` - psi(1) = 0
* `psi_two` - psi(2) = 0
* `psi_prime_pow` - psi of a prime power p^k equals phi(p^k), except psi(2) = 0
* `psi_coprime_add` - psi is additive on coprime factors

## Values

| m      | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 12 |
|--------|---|---|---|---|---|---|---|---|---|----|----|
| psi(m) | 0 | 0 | 2 | 2 | 4 | 2 | 6 | 4 | 6 | 4  | 4  |

-/

namespace Crystallographic

open Nat Finsupp

/-- Helper function that computes the contribution of a single prime power p^k to psi.
    Returns 0 if k = 0, returns 0 if p = 2 and k = 1, otherwise returns phi(p^k). -/
def psiPrimePow (p k : ℕ) : ℕ :=
  if k = 0 then 0
  else if p = 2 ∧ k = 1 then 0
  else Nat.totient (p ^ k)

lemma psiPrimePow_zero (p : ℕ) : psiPrimePow p 0 = 0 := by
  simp [psiPrimePow]

/-- The psi function for crystallographic restriction.
    psi(m) is the minimum dimension N such that an N×N integer matrix can have order m.

    Defined as the sum over prime power factors: if m = prod p_i^{k_i}, then
    psi(m) = sum_i (if p_i = 2 and k_i = 1 then 0 else phi(p_i^{k_i})) -/
def psi (m : ℕ) : ℕ :=
  m.factorization.sum fun p k => psiPrimePow p k

@[simp] theorem psi_zero : psi 0 = 0 := by
  simp [psi, Nat.factorization_zero]

@[simp] theorem psi_one : psi 1 = 0 := by
  simp [psi, Nat.factorization_one]

@[simp] theorem psi_two : psi 2 = 0 := by
  simp only [psi]
  rw [Nat.prime_two.factorization]
  rw [Finsupp.sum_single_index (psiPrimePow_zero 2)]
  simp [psiPrimePow]

/-- psi of a prime power p^k equals phi(p^k), except psi(2) = 0 -/
theorem psi_prime_pow (p k : ℕ) (hp : p.Prime) (hk : 0 < k) :
    psi (p ^ k) = if p = 2 ∧ k = 1 then 0 else Nat.totient (p ^ k) := by
  simp only [psi]
  rw [hp.factorization_pow]
  rw [Finsupp.sum_single_index (psiPrimePow_zero p)]
  simp only [psiPrimePow, hk.ne']
  simp only [ite_false]

/-- psi(3) = 2 -/
@[simp] theorem psi_three : psi 3 = 2 := by
  have h := psi_prime_pow 3 1 Nat.prime_three (by norm_num : 0 < 1)
  simp only [pow_one] at h
  rw [h]
  simp only [show (3 : ℕ) ≠ 2 by decide, false_and, ite_false]
  rw [Nat.totient_prime Nat.prime_three]

/-- psi(4) = 2 -/
@[simp] theorem psi_four : psi 4 = 2 := by
  have h := psi_prime_pow 2 2 Nat.prime_two (by norm_num : 0 < 2)
  simp only [show (4 : ℕ) = 2 ^ 2 by norm_num] at h ⊢
  rw [h]
  simp only [show (2 : ℕ) ≠ 1 by decide, and_false, ite_false]
  rw [Nat.totient_prime_pow Nat.prime_two (by norm_num : 0 < 2)]
  norm_num

/-- psi(5) = 4 -/
@[simp] theorem psi_five : psi 5 = 4 := by
  have hp : Nat.Prime 5 := by decide
  have h := psi_prime_pow 5 1 hp (by norm_num : 0 < 1)
  simp only [pow_one] at h
  rw [h]
  simp only [show (5 : ℕ) ≠ 2 by decide, false_and, ite_false]
  rw [Nat.totient_prime hp]

/-- psi(7) = 6 -/
@[simp] theorem psi_seven : psi 7 = 6 := by
  have hp : Nat.Prime 7 := by decide
  have h := psi_prime_pow 7 1 hp (by norm_num : 0 < 1)
  simp only [pow_one] at h
  rw [h]
  simp only [show (7 : ℕ) ≠ 2 by decide, false_and, ite_false]
  rw [Nat.totient_prime hp]

/-- psi(8) = 4 -/
@[simp] theorem psi_eight : psi 8 = 4 := by
  have h := psi_prime_pow 2 3 Nat.prime_two (by norm_num : 0 < 3)
  simp only [show (8 : ℕ) = 2 ^ 3 by norm_num] at h ⊢
  rw [h]
  simp only [show (3 : ℕ) ≠ 1 by decide, and_false, ite_false]
  rw [Nat.totient_prime_pow Nat.prime_two (by norm_num : 0 < 3)]
  norm_num

/-- psi(9) = 6 -/
@[simp] theorem psi_nine : psi 9 = 6 := by
  have h := psi_prime_pow 3 2 Nat.prime_three (by norm_num : 0 < 2)
  simp only [show (9 : ℕ) = 3 ^ 2 by norm_num] at h ⊢
  rw [h]
  simp only [show (3 : ℕ) ≠ 2 by decide, false_and, ite_false]
  rw [Nat.totient_prime_pow Nat.prime_three (by norm_num : 0 < 2)]
  norm_num

/-- The supports of factorizations of coprime numbers are disjoint -/
lemma factorization_support_disjoint {m n : ℕ} (h : m.Coprime n) :
    Disjoint m.factorization.support n.factorization.support := by
  rw [Finset.disjoint_iff_ne]
  intro p hp q hq hpq
  rw [Nat.support_factorization, Nat.mem_primeFactors] at hp hq
  subst hpq
  have hdvd_m : p ∣ m := hp.2.1
  have hdvd_n : p ∣ n := hq.2.1
  have hp_prime := hp.1
  have : p ∣ m.gcd n := Nat.dvd_gcd hdvd_m hdvd_n
  rw [Nat.Coprime.gcd_eq_one h] at this
  exact Nat.Prime.not_dvd_one hp_prime this

/-- psi is additive on coprime factors -/
theorem psi_coprime_add (m n : ℕ) (hm : 0 < m) (hn : 0 < n) (h : m.Coprime n) :
    psi (m * n) = psi m + psi n := by
  simp only [psi, Finsupp.sum]
  rw [Nat.factorization_mul (Nat.pos_iff_ne_zero.mp hm) (Nat.pos_iff_ne_zero.mp hn)]
  have hdisj := factorization_support_disjoint h
  rw [Finsupp.support_add_eq hdisj]
  rw [Finset.sum_union hdisj]
  congr 1
  · apply Finset.sum_congr rfl
    intro p hp
    congr 1
    rw [Finsupp.add_apply]
    have : n.factorization p = 0 := by
      by_contra hne
      have hmem : p ∈ n.factorization.support := Finsupp.mem_support_iff.mpr hne
      exact Finset.disjoint_left.mp hdisj hp hmem
    simp [this]
  · apply Finset.sum_congr rfl
    intro p hp
    congr 1
    rw [Finsupp.add_apply]
    have : m.factorization p = 0 := by
      by_contra hne
      have hmem : p ∈ m.factorization.support := Finsupp.mem_support_iff.mpr hne
      exact Finset.disjoint_right.mp hdisj hp hmem
    simp [this]

/-- psi(6) = 2 -/
@[simp] theorem psi_six : psi 6 = 2 := by
  have h6 : (6 : ℕ) = 2 * 3 := by norm_num
  rw [h6, psi_coprime_add 2 3 (by norm_num) (by norm_num) (by decide)]
  simp

/-- psi(10) = 4 -/
@[simp] theorem psi_ten : psi 10 = 4 := by
  have h10 : (10 : ℕ) = 2 * 5 := by norm_num
  rw [h10, psi_coprime_add 2 5 (by norm_num) (by norm_num) (by decide)]
  simp

/-- psi(12) = 4 -/
@[simp] theorem psi_twelve : psi 12 = 4 := by
  have h12 : (12 : ℕ) = 4 * 3 := by norm_num
  rw [h12, psi_coprime_add 4 3 (by norm_num) (by norm_num) (by decide)]
  simp

/-! ## Bounds on psi contributions -/

/-- If m is positive and has a prime factor p in its support, then
    psi(m) >= psiPrimePow(p, m.factorization p) -/
lemma psi_ge_psiPrimePow_of_mem_support {m p : ℕ} (_hm : 0 < m)
    (hp : p ∈ m.factorization.support) :
    psiPrimePow p (m.factorization p) ≤ psi m := by
  simp only [psi, Finsupp.sum]
  have hnonneg : ∀ i ∈ m.factorization.support, 0 ≤ psiPrimePow i (m.factorization i) := by
    intro i _
    simp only [psiPrimePow]
    split_ifs <;> omega
  exact Finset.single_le_sum hnonneg hp

/-- psiPrimePow for odd primes p >= 5 gives at least 4 -/
lemma psiPrimePow_ge_four_of_prime_ge_five {p k : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hk : 0 < k) :
    4 ≤ psiPrimePow p k := by
  simp only [psiPrimePow, hk.ne']
  have hp2 : p ≠ 2 := by omega
  simp only [hp2, false_and, ite_false]
  rw [Nat.totient_prime_pow hp (by omega : 0 < k)]
  have hp_pos : 0 < p := hp.pos
  have hpow_pos : 0 < p ^ (k - 1) := Nat.pow_pos hp_pos
  have hpk : p ^ (k - 1) * (p - 1) ≥ p - 1 := Nat.le_mul_of_pos_left (p - 1) hpow_pos
  omega

/-- psiPrimePow for 2^k with k >= 3 gives at least 4 -/
lemma psiPrimePow_ge_four_of_two_pow_ge_three {k : ℕ} (hk : 3 ≤ k) :
    4 ≤ psiPrimePow 2 k := by
  simp only [psiPrimePow]
  have hk0 : k ≠ 0 := by omega
  have hk1 : k ≠ 1 := by omega
  simp only [hk0, ite_false, hk1, and_false]
  rw [Nat.totient_prime_pow Nat.prime_two (by omega : 0 < k)]
  have hge2 : k - 1 ≥ 2 := by omega
  calc 2 ^ (k - 1) * (2 - 1) = 2 ^ (k - 1) := by ring
    _ ≥ 2 ^ 2 := Nat.pow_le_pow_right (by omega) hge2
    _ = 4 := by norm_num

/-- psiPrimePow for 3^k with k >= 2 gives at least 6 -/
lemma psiPrimePow_ge_six_of_three_pow_ge_two {k : ℕ} (hk : 2 ≤ k) :
    6 ≤ psiPrimePow 3 k := by
  simp only [psiPrimePow]
  have hk0 : k ≠ 0 := by omega
  simp only [hk0, ite_false, show (3 : ℕ) ≠ 2 by decide, false_and]
  rw [Nat.totient_prime_pow Nat.prime_three (by omega : 0 < k)]
  have hge1 : k - 1 ≥ 1 := by omega
  calc 3 ^ (k - 1) * (3 - 1) = 2 * 3 ^ (k - 1) := by ring
    _ ≥ 2 * 3 ^ 1 := by
        apply Nat.mul_le_mul_left
        apply Nat.pow_le_pow_right (by omega) hge1
    _ = 6 := by norm_num

end Crystallographic
