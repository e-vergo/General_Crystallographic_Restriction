/-
Copyright (c) 2026 Eric Vergo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo
-/
import Architect
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Totient

/-!
# The psi function for the crystallographic restriction theorem

This file defines the function psi : ℕ → ℕ, which gives the minimum dimension N such that
an N×N integer matrix can have a given order m.

## Main definitions

* `Crystallographic.psi` - The psi function for crystallographic restriction.
  - `psi 1 = 0`
  - `psi 2 = 0`
  - `psi n` = sum over prime power factors p^k of n: if p=2 and k=1 then 0 else phi(p^k)

## Main results

* `psi_one` - `psi 1 = 0`
* `psi_two` - `psi 2 = 0`
* `psi_prime_pow` - `psi` of a prime power p^k equals phi(p^k), except `psi 2 = 0`
* `psi_coprime_add` - `psi` is additive on coprime factors

## Values

| m        | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 12 |
|----------|---|---|---|---|---|---|---|---|---|----|----|
| `psi m`  | 0 | 0 | 2 | 2 | 4 | 2 | 6 | 4 | 6 | 4  | 4  |

## References

* Sasse, R. (2020). "Crystallographic Groups"

## Tags

crystallographic restriction, psi function, totient, prime power, integer matrix, finite order
-/

namespace Crystallographic

open Nat Finsupp

/-- Helper function that computes the contribution of a single prime power p^k to psi.
    Returns 0 if k = 0, returns 0 if p = 2 and k = 1, otherwise returns phi(p^k). -/
@[blueprint
  "psiPrimePow-def"
  (statement := /-- The function $\psi_{\text{pp}}(p, k)$ computes the contribution of a single
  prime power $p^k$ to $\psi$. Returns $0$ if $k = 0$ or if $p = 2$ and $k = 1$,
  otherwise returns $\varphi(p^k)$.

  The special case $\psi_{\text{pp}}(2, 1) = 0$ reflects that $-I$ achieves order $2$ in any
  dimension $\geq 1$, so order $2$ does not require additional dimensions. For all other
  prime powers $p^k$, we need $\varphi(p^k)$ dimensions to achieve order $p^k$. -/)]
def psiPrimePow (p k : ℕ) : ℕ :=
  if k = 0 then 0
  else if p = 2 ∧ k = 1 then 0
  else Nat.totient (p ^ k)

/-- psiPrimePow at exponent 0 is always 0. -/
@[simp]
lemma psiPrimePow_zero (p : ℕ) : psiPrimePow p 0 = 0 := by
  simp [psiPrimePow]

/-- The psi function for crystallographic restriction.
    psi(m) is the minimum dimension N such that an N×N integer matrix can have order m.

    Defined as the sum over prime power factors: if m = prod p_i^{k_i}, then
    psi(m) = sum_i (if p_i = 2 and k_i = 1 then 0 else phi(p_i^{k_i})) -/
@[blueprint
  "psi-def"
  (statement := /-- The psi function $\psi(m) = \sum_{p^k \| m} \psi_{\text{pp}}(p, k)$,
  which gives the minimum dimension $N$ such that an $N \times N$ integer matrix
  can have order $m$.

  For $m$ with prime factorization $m = \prod_i p_i^{k_i}$:
  $$\psi(m) = \sum_i \psi_{\text{pp}}(p_i, k_i) =
    \sum_{\substack{p^k \| m \\ (p,k) \neq (2,1)}} \varphi(p^k)$$
  This gives the minimum dimension needed to realize order $m$.
  \uses{psiPrimePow-def} -/)]
def psi (m : ℕ) : ℕ :=
  m.factorization.sum fun p k => psiPrimePow p k

/-- `psi 0 = 0` by convention. -/
@[simp]
theorem psi_zero : psi 0 = 0 := by
  simp [psi, Nat.factorization_zero]

/-- `psi 1 = 0`: The identity matrix has order 1 in any dimension. -/
@[simp]
theorem psi_one : psi 1 = 0 := by
  simp [psi, Nat.factorization_one]

/-- `psi 2 = 0`: The negation of identity has order 2 in any dimension ≥ 1. -/
@[simp]
theorem psi_two : psi 2 = 0 := by
  simp only [psi]
  rw [Nat.prime_two.factorization]
  rw [Finsupp.sum_single_index (psiPrimePow_zero 2)]
  simp [psiPrimePow]

/-- `psi` of a prime power p^k equals phi(p^k), except `psi 2 = 0` -/
@[blueprint "lem:psi-prime-pow"
  (statement := /-- For prime $p$ and $k > 0$: $\psi(p^k) = \varphi(p^k)$ unless $p = 2, k = 1$.

  For a prime power $p^k$, the factorization has a single term, so
  $\psi(p^k) = \psi_{\text{pp}}(p, k)$. This equals $\varphi(p^k) = p^{k-1}(p-1)$ except
  when $p = 2$ and $k = 1$.
  \uses{psiPrimePow-def, psi-def} -/)
  (proof := /-- For prime power $p^k$, the factorization has a single term, so
  $\psi(p^k) = \psi_{pp}(p, k)$. This equals $\varphi(p^k)$ except when $p = 2, k = 1$. -/)]
theorem psi_prime_pow (p k : ℕ) (hp : p.Prime) (hk : 0 < k) :
    psi (p ^ k) = if p = 2 ∧ k = 1 then 0 else Nat.totient (p ^ k) := by
  simp only [psi]
  rw [hp.factorization_pow]
  rw [Finsupp.sum_single_index (psiPrimePow_zero p)]
  simp only [psiPrimePow, hk.ne', ite_false]

/-- psi of an odd prime p equals p - 1 -/
theorem psi_odd_prime (p : ℕ) (hp : p.Prime) (hp_odd : p ≠ 2) : psi p = p - 1 := by
  have h := psi_prime_pow p 1 hp (by norm_num : 0 < 1)
  simp only [pow_one] at h
  rw [h, if_neg (by simp [hp_odd]), Nat.totient_prime hp]

/-- `psi 3 = 2` -/
theorem psi_three : psi 3 = 2 := psi_odd_prime 3 Nat.prime_three (by decide)

/-- `psi 5 = 4` -/
theorem psi_five : psi 5 = 4 := psi_odd_prime 5 (by decide) (by decide)

/-- `psi 7 = 6` -/
theorem psi_seven : psi 7 = 6 := psi_odd_prime 7 (by decide) (by decide)

/-- psi of 2^k for k ≥ 2 equals φ(2^k) = 2^(k-1) -/
theorem psi_two_pow (k : ℕ) (hk : 2 ≤ k) : psi (2 ^ k) = 2 ^ (k - 1) := by
  have h := psi_prime_pow 2 k Nat.prime_two (by omega : 0 < k)
  rw [h, if_neg (by omega : ¬(2 = 2 ∧ k = 1))]
  rw [Nat.totient_prime_pow Nat.prime_two (by omega : 0 < k)]
  ring

/-- psi of p^k for odd prime p equals φ(p^k) -/
theorem psi_odd_prime_pow (p k : ℕ) (hp : p.Prime) (hp_odd : p ≠ 2) (hk : 0 < k) :
    psi (p ^ k) = p ^ (k - 1) * (p - 1) := by
  rw [psi_prime_pow p k hp hk, if_neg (by simp [hp_odd])]
  rw [Nat.totient_prime_pow hp hk]

/-- `psi 4 = 2` -/
theorem psi_four : psi 4 = 2 := by simpa using psi_two_pow 2 (by norm_num)

/-- `psi 8 = 4` -/
theorem psi_eight : psi 8 = 4 := by simpa using psi_two_pow 3 (by norm_num)

/-- `psi 9 = 6` -/
theorem psi_nine : psi 9 = 6 := by simpa using psi_odd_prime_pow 3 2 Nat.prime_three (by decide) (by norm_num)

/-- The supports of factorizations of coprime numbers are disjoint.

If gcd(m, n) = 1, then m and n share no common prime factors. -/
@[blueprint "lem:factorization-disjoint"
  (statement := /-- Coprime numbers have disjoint prime factorization supports. -/)
  (proof := /-- If $p$ divides both $m$ and $n$, then $p \mid \gcd(m,n) = 1$, contradicting $p$ prime. -/)]
lemma factorization_support_disjoint {m n : ℕ} (h : m.Coprime n) :
    Disjoint m.factorization.support n.factorization.support :=
  Nat.support_factorization m ▸ Nat.support_factorization n ▸ h.disjoint_primeFactors

private lemma factorization_eq_zero_of_disjoint_support {m n p : ℕ}
    (hdisj : Disjoint m.factorization.support n.factorization.support)
    (hp : p ∈ m.factorization.support) : n.factorization p = 0 := by
  by_contra hne
  exact Finset.disjoint_left.mp hdisj hp (Finsupp.mem_support_iff.mpr hne)

/-- `psi` is additive on coprime factors.

For coprime m and n, `psi (m * n) = psi m + psi n`. This follows from the
factorization m * n = prod(p_i^{k_i}) * prod(q_j^{l_j}) where the prime
factors of m and n are disjoint. -/
@[blueprint "lem:psi-coprime-add"
  (statement := /-- $\psi(mn) = \psi(m) + \psi(n)$ for coprime $m, n$.

  When $\gcd(m, n) = 1$, the prime factorizations of $m$ and $n$ share no common primes, so
  $$\psi(mn) = \sum_{p^k \| mn} \psi_{\text{pp}}(p, k) =
    \sum_{p^k \| m} \psi_{\text{pp}}(p, k) + \sum_{p^k \| n} \psi_{\text{pp}}(p, k) =
    \psi(m) + \psi(n).$$
  \uses{psi-def, lem:factorization-disjoint} -/)
  (proof := /-- When $\gcd(m, n) = 1$, the factorizations of $m$ and $n$ are disjoint.
  Each prime power in $mn$ comes from exactly one of $m$ or $n$, so the
  $\psi$ contributions add. -/)]
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
    rw [Finsupp.add_apply, factorization_eq_zero_of_disjoint_support hdisj hp, add_zero]
  · apply Finset.sum_congr rfl
    intro p hp
    congr 1
    rw [Finsupp.add_apply, factorization_eq_zero_of_disjoint_support hdisj.symm hp, zero_add]

/-- `psi 6 = 2` -/
theorem psi_six : psi 6 = 2 := by
  have h6 : (6 : ℕ) = 2 * 3 := by norm_num
  rw [h6, psi_coprime_add 2 3 (by norm_num) (by norm_num) (by decide)]
  rw [psi_two, psi_three]

/-- `psi 10 = 4` -/
theorem psi_ten : psi 10 = 4 := by
  have h10 : (10 : ℕ) = 2 * 5 := by norm_num
  rw [h10, psi_coprime_add 2 5 (by norm_num) (by norm_num) (by decide)]
  rw [psi_two, psi_five]

/-- `psi 12 = 4` -/
theorem psi_twelve : psi 12 = 4 := by
  have h12 : (12 : ℕ) = 4 * 3 := by norm_num
  rw [h12, psi_coprime_add 4 3 (by norm_num) (by norm_num) (by decide)]
  rw [psi_four, psi_three]

/-! ## Bounds on psi contributions -/

/-- `psi m` is at least the contribution from any single prime power factor.

If p^k divides m exactly, then `psi m ≥ psiPrimePow p k`. -/
@[blueprint "lem:psi-ge-psiPrimePow"
  (statement := /-- $\psi(m) \geq \psi_{\mathrm{pp}}(p, v_p(m))$ for each prime $p \mid m$. -/)
  (proof := /-- The sum $\psi(m)$ includes the term $\psi_{\mathrm{pp}}(p, v_p(m))$, and all terms are non-negative. -/)]
lemma psi_ge_psiPrimePow_of_mem_support {m p : ℕ}
    (hp : p ∈ m.factorization.support) :
    psiPrimePow p (m.factorization p) ≤ psi m := by
  simp only [psi, Finsupp.sum]
  have hnonneg : ∀ i ∈ m.factorization.support, 0 ≤ psiPrimePow i (m.factorization i) := by
    intro i _
    simp only [psiPrimePow]
    split_ifs <;> omega
  exact Finset.single_le_sum hnonneg hp

end Crystallographic

#export_blueprint_highlighting
