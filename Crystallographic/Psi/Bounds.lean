/-
Copyright (c) 2026 Eric Vergo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo
-/
import Dress
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.GCD.BigOperators
import Mathlib.Data.Nat.Totient
import Crystallographic.Main.Lemmas
import Crystallographic.Psi.Basic

/-!
# Psi Lower Bound Lemmas

This file contains lemmas establishing lower bounds on the psi function,
which are used in the forward direction of the crystallographic restriction theorem.

## Main results

* `psiPrimePow_le_totient` - psiPrimePow is always <= totient
* `psi_le_totient` - psi(m) <= totient(m) for all m >= 1
* `sum_totient_ge_psi_of_lcm_eq` - For any S with lcm(S) = m, sum of totients >= psi(m)

## References

* Sasse, R. (2020). "Crystallographic Groups"

## Tags

crystallographic restriction, psi function, totient, lower bound, prime factorization
-/

namespace Crystallographic

/-! ## Helper lemmas for the forward direction -/

@[blueprint "lem:two-le-totient-prime-pow"
  (above := /-- A recurring theme in the bounds on $\psi$ is that $\varphi(p^k) \geq 2$
  whenever $(p,k) \neq (2,1)$. This threshold is what makes $\sum a_i \leq \prod a_i$
  applicable, converting additive $\psi$ bounds into multiplicative $\varphi$ bounds. -/)
  (title := "Totient of Prime Power")
  (statement := /-- For any prime power $p^k > 2$, we have $2 \leq \varphi(p^k)$.

  Specifically, $\varphi(p^k) = p^{k-1}(p-1) \geq 2$ unless $(p, k) = (2, 1)$,
  in which case $\varphi(2) = 1$. This bound is essential for showing that sums
  of totients are bounded by products when factors are coprime.
  \uses{} --/)
  (proof := /-- By cases on $p = 2$: if $p \neq 2$, then $p \geq 3$ so
  $\varphi(p^k) = p^{k-1}(p-1) \geq 1 \cdot 2 = 2$. If $p = 2$ and $k \geq 2$,
  then $\varphi(2^k) = 2^{k-1} \geq 2$. The case $(2, 1)$ is excluded by hypothesis. -/)]
theorem two_le_totient_primePow {p k : ℕ} (hp : p.Prime) (hk : 0 < k)
    (h : ¬(p = 2 ∧ k = 1)) : 2 ≤ Nat.totient (p ^ k) := by
  rw [Nat.totient_prime_pow hp hk]
  by_cases hp2 : p = 2
  · simpa [hp2] using Nat.pow_le_pow_right (by omega) (by omega : 1 ≤ k - 1)
  · have hp3 : 3 ≤ p := Nat.lt_of_le_of_ne hp.two_le (Ne.symm hp2)
    calc p ^ (k - 1) * (p - 1) ≥ 1 * (p - 1) := Nat.mul_le_mul_right _ (Nat.one_le_pow _ _ hp.pos)
      _ ≥ 2 := by omega

/-- For coprime factors with both totients ≥ 2, psi sum ≤ totient product.

This handles the "composite without 2^1 factor" case in `psi_le_totient`:
when neither factor is 2, both totients are ≥ 2, so the sum of psi values
is bounded by the sum of totients, which is bounded by their product. -/
private lemma psi_sum_le_totient_prod_of_ge_two {a b : ℕ}
    (hpsi_a : psi a ≤ Nat.totient a) (hpsi_b : psi b ≤ Nat.totient b)
    (htot_a_ge2 : 2 ≤ Nat.totient a) (htot_b_ge2 : 2 ≤ Nat.totient b) :
    psi a + psi b ≤ Nat.totient a * Nat.totient b :=
  calc psi a + psi b
      ≤ Nat.totient a + Nat.totient b := by omega
    _ ≤ Nat.totient a * Nat.totient b := Nat.add_le_mul htot_a_ge2 htot_b_ge2

@[blueprint "lem:factorization-split-lt"
  (above := /-- The proof of $\psi(m) \leq \varphi(m)$ proceeds by strong induction. When $m$
  is not a prime power, we need to split it into strictly smaller coprime factors so that the
  inductive hypothesis applies to both parts. -/)
  (title := "Factorization Split Bound")
  (statement := /-- A composite number $m > 2$ that is not a prime power can be written
  as $m = p^e \cdot m'$ where $p$ is prime, $e > 0$, $\gcd(p^e, m') = 1$, and both
  $p^e < m$ and $1 < m' < m$.

  This decomposition is essential for strong induction proofs on composite numbers:
  it provides strictly smaller coprime factors to which the inductive hypothesis applies.
  \uses{} --/)
  (proof := /-- Take $p = \mathrm{minFac}(m)$ and $e = \nu_p(m)$, the $p$-adic valuation.
  Then $m' = m / p^e$ is coprime to $p^e$ (disjoint prime support). Since $m$ is not
  a prime power, $m' \neq 1$. The bounds $p^e < m$ and $m' < m$ follow from $m' > 1$
  and $p^e \geq 2$ respectively. -/)
  (below := /-- This decomposition is the structural backbone of the strong induction in
  the psi-totient bound: it reduces the composite case to coprime factors where
  $\psi$ additivity and $\varphi$ multiplicativity can be combined. -/)]
theorem factorization_split_lt {m : ℕ} (hm : 2 < m) (h_not_pp : ¬IsPrimePow m) :
    ∃ (p e m' : ℕ), p.Prime ∧ 0 < e ∧ p ^ e * m' = m ∧
    (p ^ e).Coprime m' ∧ 1 < m' ∧ m' < m ∧ p ^ e < m := by
  have hm_ne_zero : m ≠ 0 := by omega
  have hm_ne_one : m ≠ 1 := by omega
  have hm_pos : 0 < m := by omega
  have hminFac_prime : m.minFac.Prime := Nat.minFac_prime hm_ne_one
  set p := m.minFac
  set e := m.factorization p
  have he_pos : 0 < e :=
    Nat.Prime.factorization_pos_of_dvd hminFac_prime hm_ne_zero (Nat.minFac_dvd m)
  have hdvd : p ^ e ∣ m := Nat.ordProj_dvd m p
  set m' := m / p ^ e
  have hm'_pos : 0 < m' := Nat.div_pos (Nat.le_of_dvd hm_pos hdvd) (Nat.pow_pos hminFac_prime.pos)
  have hm_eq : m = p ^ e * m' := (Nat.mul_div_cancel' hdvd).symm
  have hcop : Nat.Coprime (p ^ e) m' := Nat.coprime_ordCompl hminFac_prime hm_ne_zero |>.pow_left e
  -- m' ≠ 1 because m is not a prime power
  have hm'_ne_one : m' ≠ 1 := by
    intro hm'_one
    apply h_not_pp
    rw [isPrimePow_nat_iff]
    exact ⟨p, e, hminFac_prime, he_pos, by rw [hm_eq, hm'_one, mul_one]⟩
  have hm'_gt_one : 1 < m' := by omega
  have hm'_lt : m' < m := by
    have hpe_ge2 : 2 ≤ p ^ e := by
      calc p ^ e ≥ p ^ 1 := Nat.pow_le_pow_right hminFac_prime.one_lt.le he_pos
        _ = p := pow_one p
        _ ≥ 2 := hminFac_prime.two_le
    calc m' = 1 * m' := (one_mul _).symm
      _ < p ^ e * m' := Nat.mul_lt_mul_of_pos_right
          (Nat.one_lt_pow he_pos.ne' hminFac_prime.one_lt) hm'_pos
      _ = m := hm_eq.symm
  have hpe_lt : p ^ e < m := by
    calc p ^ e = p ^ e * 1 := (mul_one _).symm
      _ < p ^ e * m' := Nat.mul_lt_mul_of_pos_left hm'_gt_one (Nat.pow_pos hminFac_prime.pos)
      _ = m := hm_eq.symm
  exact ⟨p, e, m', hminFac_prime, he_pos, hm_eq.symm, hcop, hm'_gt_one, hm'_lt, hpe_lt⟩

@[blueprint "lem:psi-pos-of-odd"
  (above := /-- A useful consequence of the definition: for odd $m \geq 3$, every prime
  factor is at least $3$, so every prime power contribution is positive and
  $\psi(m) > 0$. This is needed in the backward direction to ensure
  the block-diagonal construction produces matrices of the correct dimension. -/)
  (title := "Psi Positive for Odd")
  (statement := /-- For odd $m \geq 3$, we have $\psi(m) > 0$.

  Since $m \geq 3$ and $m$ is odd, $m$ has a prime factor $q \geq 3$ (specifically,
  $q = \mathrm{minFac}(m)$). The prime power $q^{\nu_q(m)}$ contributes
  $\psi_{\mathrm{pp}}(q, \nu_q(m)) = \varphi(q^{\nu_q(m)}) > 0$ to $\psi(m)$,
  since $(q, \nu_q(m)) \neq (2, 1)$.
  \uses{psi-def, psiPrimePow-def} --/)
  (proof := /-- The minimal prime factor $q = \mathrm{minFac}(m)$ satisfies $q \geq 3$
  (since $2 \nmid m$). Thus $(q, \nu_q(m))$ is a nontrivial pair, and
  $\psi(m) \geq \psi_{\mathrm{pp}}(q, \nu_q(m)) = \varphi(q^{\nu_q(m)}) > 0$. -/)]
theorem psi_pos_of_odd_ge_three {m : ℕ} (hm : 3 ≤ m) (hm_odd : Odd m) :
    0 < psi m := by
  -- m >= 3 implies m != 1, so minFac(m) is prime
  have hm_ne_one : m ≠ 1 := by omega
  have hm_ne_zero : m ≠ 0 := by omega
  set q := m.minFac with hq_def
  have hq_prime : q.Prime := Nat.minFac_prime hm_ne_one
  have hq_dvd : q ∣ m := Nat.minFac_dvd m
  -- m is odd, so minFac(m) != 2 (otherwise 2 would divide m)
  have hq_ne2 : q ≠ 2 := by
    intro hq2eq
    rw [hq2eq] at hq_dvd
    exact hm_odd.not_two_dvd_nat hq_dvd
  -- Therefore minFac(m) >= 3
  have hq_ge3 : 3 ≤ q := by
    have hq2 : 2 ≤ q := hq_prime.two_le
    omega
  -- q is in the factorization support
  have hq_in_support : q ∈ m.factorization.support := by
    rw [Finsupp.mem_support_iff]
    exact (Nat.Prime.factorization_pos_of_dvd hq_prime hm_ne_zero hq_dvd).ne'
  -- psi(m) >= psiPrimePow(q, ord_q(m))
  have hcontrib : psiPrimePow q (m.factorization q) ≤ psi m :=
    psi_ge_psiPrimePow_of_mem_support hq_in_support
  -- psiPrimePow(q, k) = totient(q^k) > 0 for q >= 3 (since q != 2 means (q, k) != (2, 1))
  have hcontrib_pos : 0 < psiPrimePow q (m.factorization q) := by
    simp only [psiPrimePow]
    have hk_pos : 0 < m.factorization q :=
      Nat.Prime.factorization_pos_of_dvd hq_prime hm_ne_zero hq_dvd
    simp only [hk_pos.ne', ite_false]
    simp only [hq_ne2, false_and, ite_false]
    exact Nat.totient_pos.mpr (Nat.pow_pos hq_prime.pos)
  omega

/-! ## Forward direction: Order implies dimension bound -/

/-- psi(m) ≤ totient(m) for all m ≥ 1.

The proof proceeds by strong induction on m, using the coprime multiplicativity
of both psi (additive) and totient (multiplicative).

Key cases:
- m = 1: psi(1) = 0 ≤ 1 = totient(1)
- m = prime power p^k: psi = totient (except psi(2) = 0 ≤ 1 = totient(2))
- m = 2 * odd (with odd > 1): psi(m) = psi(odd) ≤ totient(odd) = totient(m)
- m = composite without 2^1 factor: each φ(p^k) ≥ 2, so sum ≤ product -/
@[blueprint "lem:psi-le-totient"
  (above := /-- The inequality $\psi(m) \leq \varphi(m)$ is the first of two key bounds.
  Intuitively, $\psi$ and $\varphi$ agree on every prime power except $(2,1)$, and the
  multiplicativity of $\varphi$ (versus the additivity of $\psi$) creates slack at every
  composite level: $a + b \leq ab$ whenever $a, b \geq 2$. The proof makes this precise
  by strong induction. -/)
  (title := "Psi Totient Bound")
  (statement := /-- For all $m \geq 1$, we have $\psi(m) \leq \varphi(m)$.

  We prove $\psi(m) \leq \varphi(m)$ by strong induction on $m$. The key observation is that
  $\psi$ excludes the contribution from $(2, 1)$, while $\varphi$ includes $\varphi(2) = 1$,
  so $\psi \leq \varphi$ with equality when $2 \nmid m$ or $4 \mid m$.

  The proof proceeds by strong induction on $m$:
  \begin{itemize}
  \item For $m = 1$: $\psi(1) = 0 \leq 1 = \varphi(1)$
  \item For prime powers $p^k$: $\psi(p^k) = \varphi(p^k)$ (with the exception $\psi(2) = 0$)
  \item For composite $m = 2 \cdot \text{odd}$:
        $\psi(m) = \psi(\text{odd}) \leq \varphi(\text{odd}) = \varphi(m)$
  \item For general composite without $2^1$ factor:
        each $\varphi(p^k) \geq 2$, so sum $\leq$ product
  \end{itemize}
  \uses{psi-def, psiPrimePow-def} --/)
  (proof := /-- By strong induction on $m$. For $m = 1$: both sides are $0$. For $m > 1$:
  use coprime factorization $m = a \cdot b$ with $1 < a, b < m$. Then
  $\psi(m) = \psi(a) + \psi(b) \leq \varphi(a) + \varphi(b) \leq \varphi(m)$
  by the inductive hypothesis and multiplicativity of $\varphi$. -/)
  (below := /-- This bound is used directly in the sum-of-totients lemma and also
  provides a quick proof when $m$ itself belongs to the set $S$ of divisors. The sharper
  result we need for the forward direction is the sum-of-totients bound below. -/)]
lemma psi_le_totient (m : ℕ) (hm : 0 < m) : psi m ≤ Nat.totient m := by
  -- Strong induction on m
  induction m using Nat.strong_induction_on with
  | _ m IH =>
  -- Handle small cases separately
  rcases Nat.lt_trichotomy m 1 with hm0 | rfl | hm_gt1
  · omega -- m < 1 contradicts hm
  · simp [psi_one] -- m = 1
  · rcases Nat.lt_trichotomy m 2 with hm_lt2 | rfl | hm_ge3
    · omega -- m < 2 but m > 1, contradiction
    · simp [psi_two] -- m = 2
    · -- m ≥ 3
      have hm_gt1 : 1 < m := by omega
      -- Check if m is a prime power
      by_cases hpow : IsPrimePow m
      · -- m is a prime power p^k
        rw [isPrimePow_nat_iff] at hpow
        obtain ⟨p, k, hp, hk, rfl⟩ := hpow
        rw [psi_prime_pow p k hp hk]
        split_ifs with h21
        · simp -- psi(2) = 0 ≤ totient(2)
        · exact le_refl _ -- psi(p^k) = totient(p^k) for other prime powers
      · -- m is not a prime power, so it has multiple distinct prime factors
        -- Factor m = p^e * m' using factorization_split_lt
        obtain ⟨p, e, m', hp, he_pos, hm_eq, hcop, hm'_gt_one, hm'_lt, _⟩ :=
          factorization_split_lt (by omega : 2 < m) hpow
        have hm'_pos : 0 < m' := by omega
        have hm'_ne_one : m' ≠ 1 := by omega
        -- psi and totient are additive/multiplicative on coprime factors
        rw [← hm_eq, psi_coprime_add _ _ (Nat.pow_pos hp.pos) hm'_pos hcop,
            Nat.totient_mul hcop]
        -- By IH: psi(m') ≤ totient(m')
        have IH_m' : psi m' ≤ Nat.totient m' := IH m' hm'_lt hm'_pos
        -- For the prime power part: psi(p^e) ≤ totient(p^e)
        have hpsi_pe : psi (p ^ e) ≤ Nat.totient (p ^ e) := by
          rw [psi_prime_pow p e hp he_pos]
          split_ifs <;> simp
        -- Three cases based on whether p^e or m' equals 2
        by_cases h21 : p = 2 ∧ e = 1
        · -- Case 1: p^e = 2, so psi(2) = 0 and totient(2) = 1
          obtain ⟨hp2, he1⟩ := h21
          simp only [hp2, he1, pow_one, psi_two, Nat.totient_two, zero_add,
            one_mul]
          exact IH_m'
        · by_cases hm'2 : m' = 2
          · -- Case 2: m' = 2, so psi(2) = 0 and totient(2) = 1
            simp only [hm'2, psi_two, Nat.totient_two, add_zero, mul_one]
            exact hpsi_pe
          · -- Case 3: Neither is 2^1, so both totients >= 2
            have htot_m'_ge2 : 2 ≤ Nat.totient m' :=
              two_le_totient_of_two_lt m' (by omega : 2 < m')
            have htot_pe_ge2 : 2 ≤ Nat.totient (p ^ e) := two_le_totient_primePow hp he_pos h21
            exact psi_sum_le_totient_prod_of_ge_two hpsi_pe IH_m' htot_pe_ge2 htot_m'_ge2

@[blueprint "lem:prime-pow-achieved-of-lcm-eq"
  (above := /-- We now develop the machinery for the sum-of-totients bound. The central
  idea is to assign each prime power $q^{\nu_q(m)}$ to a ``witness'' $d \in S$ that
  is divisible by it. The following lemma guarantees such witnesses exist. -/)
  (title := "Prime Power Achievement")
  (statement := /-- If $S$ is a finite set of divisors of $m$ with $\mathrm{lcm}(S) = m$,
  then for each prime $q$ dividing $m$, some element $d \in S$ is divisible by $q^{\nu_q(m)}$.

  In other words, the full $q$-power component of $m$ must be "achieved" by some element of $S$.
  This is the key combinatorial fact ensuring that $\psi(m) \leq \sum_{d \in S} \varphi(d)$.
  \uses{lem:lcm-factorization-le-sup} --/)
  (proof := /-- By contradiction: if all $d \in S$ have $\nu_q(d) < \nu_q(m)$, then
  $\nu_q(\mathrm{lcm}(S)) = \sup_{d \in S} \nu_q(d) < \nu_q(m)$, contradicting
  $\mathrm{lcm}(S) = m$. -/)
  (below := /-- Given achievement, we partition the nontrivial primes of $m$ by their
  witness and bound each fiber's totient sum by $\varphi(d)$. Summing over $S$
  yields $\psi(m) \leq \sum_{d \in S} \varphi(d)$. -/)]
lemma primePow_achieved_of_lcm_eq {m : ℕ} (hm : 0 < m) (S : Finset ℕ)
    (hS_sub : ∀ d ∈ S, d ∣ m) (hS_lcm : S.lcm id = m) :
    ∀ q ∈ m.factorization.support, ∃ d ∈ S, q ^ m.factorization q ∣ d := by
  intro q hq
  have hq_prime := Nat.prime_of_mem_primeFactors (Nat.support_factorization m ▸ hq)
  by_contra hall
  push_neg at hall
  -- All d ∈ S have q^{ord_q(m)} not dividing d
  have hall' : ∀ d ∈ S, d.factorization q < m.factorization q := by
    intro d hd
    have hndvd := hall d hd
    have hdvd : d ∣ m := hS_sub d hd
    have hd_pos : 0 < d := Nat.pos_of_dvd_of_pos hdvd hm
    by_contra hge
    push_neg at hge
    have := (hq_prime.pow_dvd_iff_le_factorization hd_pos.ne').mpr hge
    exact hndvd this
  -- lcm(S).factorization q = sup of d.factorization q, which is < m.factorization q
  -- This contradicts hS_lcm since lcm(S) = m requires matching factorizations.
  have hne_zero : S.lcm id ≠ 0 := by rw [hS_lcm]; exact hm.ne'
  have hk_pos : 0 < m.factorization q := Finsupp.mem_support_iff.mp hq |> Nat.pos_of_ne_zero
  have hfact_q : (S.lcm id).factorization q < m.factorization q := by
    -- Show: (S.lcm id).factorization q ≤ S.sup (d.factorization q) < m.factorization q
    have hsup_lt : S.sup (fun d => d.factorization q) < m.factorization q :=
      Finset.sup_lt_iff hk_pos |>.mpr (fun d hd => hall' d hd)
    -- Use extracted lemma for lcm factorization bound
    have hS_ne_zero : ∀ d ∈ S, d ≠ 0 := fun d hd =>
      (Nat.pos_of_dvd_of_pos (hS_sub d hd) hm).ne'
    exact lt_of_le_of_lt (Finset.lcm_factorization_le_sup S id q hS_ne_zero) hsup_lt
  rw [hS_lcm] at hfact_q
  omega

/-- The nontrivial primes of m are those q with q^k || m where (q,k) ≠ (2,1). -/
private abbrev nontrivialPrimes (m : ℕ) : Finset ℕ :=
  m.factorization.support.filter (fun q => ¬(q = 2 ∧ m.factorization q = 1))

/-- psi(m) equals the sum of φ(q^{ord_q(m)}) over nontrivial primes q of m.
This rewrites psi in terms of the filtered factorization support. -/
@[blueprint "lem:psi-eq-sum-nontrivial-totients" (title := "Psi as Sum of Nontrivial Totients")]
lemma psi_eq_sum_nontrivial_totients (m : ℕ) :
    psi m = ∑ q ∈ nontrivialPrimes m, Nat.totient (q ^ m.factorization q) := by
  unfold psi nontrivialPrimes
  simp only [Finsupp.sum, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro q hq
  simp only [psiPrimePow]
  have hk_pos : 0 < m.factorization q :=
    Finsupp.mem_support_iff.mp hq |> Nat.pos_of_ne_zero
  simp only [hk_pos.ne', ite_false]
  by_cases hqk : q = 2 ∧ m.factorization q = 1
  · simp [hqk]
  · simp [hqk]

/-- For a fiber of primes mapping to the same element d, the sum of φ(q^k) over the fiber
is bounded by φ(d).

The key insight: if q₁^{k₁}, q₂^{k₂}, ... all divide d with distinct primes qᵢ,
then their product also divides d. By multiplicativity of φ and the inequality
∑ aᵢ ≤ ∏ aᵢ when all aᵢ ≥ 2, we get the bound. -/
@[blueprint "lem:fiber-totient-sum-le-totient" (title := "Fiber Totient Sum Bound")]
lemma fiber_totient_sum_le_totient {m d : ℕ} (hd_pos : 0 < d)
    (fiber : Finset ℕ)
    (h_fiber_primes : ∀ q ∈ fiber, q.Prime)
    (h_fiber_dvd : ∀ q ∈ fiber, q ^ m.factorization q ∣ d)
    (h_fiber_ge2 : ∀ q ∈ fiber, 2 ≤ Nat.totient (q ^ m.factorization q)) :
    ∑ q ∈ fiber, Nat.totient (q ^ m.factorization q) ≤ Nat.totient d := by
  by_cases h_fiber_empty : fiber = ∅
  · rw [h_fiber_empty, Finset.sum_empty]
    exact Nat.zero_le _
  · have h_fiber_nonempty : fiber.Nonempty := Finset.nonempty_of_ne_empty h_fiber_empty
    -- The primes in fiber are pairwise coprime
    have h_coprime : ∀ q₁ ∈ fiber, ∀ q₂ ∈ fiber, q₁ ≠ q₂ →
        (q₁ ^ m.factorization q₁).Coprime (q₂ ^ m.factorization q₂) := by
      intro q₁ hq₁ q₂ hq₂ hne
      apply Nat.Coprime.pow
      exact (Nat.coprime_primes (h_fiber_primes q₁ hq₁) (h_fiber_primes q₂ hq₂)).mpr hne
    -- ∏_{q∈fiber} q^{ord_q(m)} divides d
    have h_prod_dvd : (∏ q ∈ fiber, q ^ m.factorization q) ∣ d :=
      Finset.prod_coprime_dvd fiber (fun q => q ^ m.factorization q) d h_fiber_dvd h_coprime
    -- φ(∏ q^k) = ∏ φ(q^k) by coprimality
    have h_totient_prod : Nat.totient (∏ q ∈ fiber, q ^ m.factorization q) =
        ∏ q ∈ fiber, Nat.totient (q ^ m.factorization q) :=
      Nat.totient_finset_prod_of_coprime fiber (fun q => q ^ m.factorization q) h_coprime
    -- φ(n) | φ(d) when n | d, hence φ(n) ≤ φ(d)
    have h_totient_ge_prod :
        ∏ q ∈ fiber, Nat.totient (q ^ m.factorization q) ≤ Nat.totient d := by
      rw [← h_totient_prod]
      have h_dvd : Nat.totient (∏ q ∈ fiber, q ^ m.factorization q) ∣ Nat.totient d :=
        Nat.totient_dvd_of_dvd h_prod_dvd
      have h_pos : 0 < Nat.totient d := Nat.totient_pos.mpr hd_pos
      exact Nat.le_of_dvd h_pos h_dvd
    -- ∏ ≥ ∑ when all factors ≥ 2
    have h_prod_ge_sum : ∑ q ∈ fiber, Nat.totient (q ^ m.factorization q) ≤
        ∏ q ∈ fiber, Nat.totient (q ^ m.factorization q) :=
      Finset.sum_le_prod_of_all_ge_two fiber _ h_fiber_ge2
    exact le_trans h_prod_ge_sum h_totient_ge_prod

/-- For a finite set S of divisors of m with achiever function mapping nontrivial primes
to elements of S, the sum of φ(q^k) over nontrivial primes is bounded by ∑_{d∈S} φ(d).

This is the fiberwise bound: we partition nontrivial primes by their achiever,
and for each fiber, the sum of φ(q^k) is bounded by φ(d) where d is the achiever. -/
@[blueprint "lem:sum-nontrivial-totients-le-sum-totients" (title := "Nontrivial Totient Sum Bound")]
lemma sum_nontrivial_totients_le_sum_totients {m : ℕ} (S : Finset ℕ)
    (hS_pos : ∀ d ∈ S, 0 < d)
    (achiever : ℕ → ℕ)
    (h_achiever_mem : ∀ q ∈ nontrivialPrimes m, achiever q ∈ S)
    (h_achiever_dvd : ∀ q ∈ nontrivialPrimes m, q ^ m.factorization q ∣ achiever q) :
    ∑ q ∈ nontrivialPrimes m, Nat.totient (q ^ m.factorization q) ≤ ∑ d ∈ S, Nat.totient d := by
  -- Use fiberwise sum: ∑_{q∈NT} f(q) = ∑_{d∈S} ∑_{q∈NT: achiever q = d} f(q)
  have h_fiberwise : ∑ q ∈ nontrivialPrimes m, Nat.totient (q ^ m.factorization q) =
      ∑ d ∈ S, ∑ q ∈ (nontrivialPrimes m).filter (fun q => achiever q = d),
        Nat.totient (q ^ m.factorization q) := by
    symm
    apply Finset.sum_fiberwise_of_maps_to
    intro q hq; exact h_achiever_mem q hq
  calc ∑ q ∈ nontrivialPrimes m, Nat.totient (q ^ m.factorization q)
    = ∑ d ∈ S, ∑ q ∈ (nontrivialPrimes m).filter (fun q => achiever q = d),
        Nat.totient (q ^ m.factorization q) := h_fiberwise
    _ ≤ ∑ d ∈ S, Nat.totient d := by
      apply Finset.sum_le_sum
      intro d hd
      -- For this d, bound the fiber sum by φ(d) using helper lemma
      let fiber := (nontrivialPrimes m).filter (fun q => achiever q = d)
      -- Establish hypotheses for the helper lemma
      have h_fiber_dvd : ∀ q ∈ fiber, q ^ m.factorization q ∣ d := by
        intro q hq
        have hq_NT : q ∈ nontrivialPrimes m := Finset.mem_of_mem_filter q hq
        have hq_eq : achiever q = d := (Finset.mem_filter.mp hq).2
        rw [← hq_eq]
        exact h_achiever_dvd q hq_NT
      have h_fiber_primes : ∀ q ∈ fiber, q.Prime := by
        intro q hq
        have hq_supp := Finset.mem_of_mem_filter q (Finset.mem_of_mem_filter q hq)
        exact Nat.prime_of_mem_primeFactors (Nat.support_factorization m ▸ hq_supp)
      have h_fiber_ge2 : ∀ q ∈ fiber, 2 ≤ Nat.totient (q ^ m.factorization q) := by
        intro q hq
        have hq_NT := Finset.mem_of_mem_filter q hq
        have hq_supp := Finset.mem_of_mem_filter q hq_NT
        have hq_prime :=
          Nat.prime_of_mem_primeFactors (Nat.support_factorization m ▸ hq_supp)
        have hk_pos : 0 < m.factorization q :=
          Finsupp.mem_support_iff.mp hq_supp |> Nat.pos_of_ne_zero
        have hqk_nontrivial : ¬(q = 2 ∧ m.factorization q = 1) :=
          (Finset.mem_filter.mp hq_NT).2
        exact two_le_totient_primePow hq_prime hk_pos hqk_nontrivial
      exact fiber_totient_sum_le_totient (hS_pos d hd) fiber
        h_fiber_primes h_fiber_dvd h_fiber_ge2

/-- If m ∈ S, then ∑_{d∈S} φ(d) ≥ psi(m) follows from psi(m) ≤ φ(m) and m contributing to the sum. -/
@[blueprint "lem:totient-sum-ge-psi-of-mem" (title := "Totient Sum Bound via Membership")]
lemma totient_sum_ge_psi_of_mem {m : ℕ} (hm : 0 < m) (S : Finset ℕ)
    (hS_sub : ∀ d ∈ S, d ∣ m) (hm_in_S : m ∈ S) :
    psi m ≤ ∑ d ∈ S, Nat.totient d := by
  calc psi m ≤ Nat.totient m := psi_le_totient m hm
    _ ≤ ∑ d ∈ S, Nat.totient d := Finset.single_le_sum
        (fun d _ => Nat.le_of_lt (Nat.totient_pos.mpr (Nat.pos_of_mem_divisors
          (Nat.mem_divisors.mpr ⟨hS_sub d (by assumption), hm.ne'⟩)))) hm_in_S

@[blueprint "lem:finset-nonempty-of-two-le-lcm"
  (above := /-- The final ingredient for the sum-of-totients bound is a pair of
  bookkeeping lemmas about sets with large lcm. -/)
  (title := "Nonempty Finset from LCM")
  (statement := /-- If $\mathrm{lcm}(S) \geq 2$ for a finite set $S$ of natural numbers,
  then $S$ is nonempty.

  This follows immediately from the fact that $\mathrm{lcm}(\emptyset) = 1$ by convention.
  \uses{} --/)
  (proof := /-- By contradiction: if $S = \emptyset$, then $\mathrm{lcm}(S) = 1 < 2$,
  contradicting the hypothesis. -/)]
lemma Finset.nonempty_of_two_le_lcm {S : Finset ℕ} (hS_lcm_ge2 : 2 ≤ S.lcm id) :
    S.Nonempty := by
  by_contra h
  rw [Finset.not_nonempty_iff_eq_empty] at h
  simp only [h, Finset.lcm_empty] at hS_lcm_ge2
  omega

@[blueprint "lem:finset-exists-one-lt-of-two-le-lcm"
  (title := "Finset Element Exists")
  (statement := /-- If $S$ is a finite set of positive integers with $\mathrm{lcm}(S) \geq 2$,
  then some element $d \in S$ satisfies $d > 1$.

  This is because $\mathrm{lcm}$ of a set where all elements equal $1$ would be $1$.
  \uses{lem:finset-nonempty-of-two-le-lcm} --/)
  (proof := /-- By contradiction: if all $d \in S$ satisfy $d \leq 1$, then since
  all $d > 0$ we have $d = 1$ for all $d \in S$. Thus $\mathrm{lcm}(S) = 1 < 2$,
  a contradiction. -/)]
lemma Finset.exists_one_lt_of_two_le_lcm {S : Finset ℕ} (hS_pos : ∀ d ∈ S, 0 < d)
    (hS_lcm_ge2 : 2 ≤ S.lcm id) : ∃ d ∈ S, 1 < d := by
  by_contra hall_le1
  push_neg at hall_le1
  have hall_eq1 : ∀ d ∈ S, d = 1 := fun d hd => by
    have hd_pos := hS_pos d hd
    have hd_le1 := hall_le1 d hd
    omega
  have hlcm_eq1 : S.lcm id = 1 := by
    apply Nat.eq_one_of_dvd_one
    apply Finset.lcm_dvd_iff.mpr
    intro d hd
    simp only [id_eq, hall_eq1 d hd, Nat.one_dvd]
  omega

/-- Key lemma: For any S ⊆ m.divisors with lcm(S) = m, we have Σ_{d∈S} φ(d) ≥ psi(m).

This is the combinatorial heart of the forward direction. The minimum is achieved when
S consists of one prime power for each distinct prime in m's factorization, giving psi(m).

The proof proceeds by showing that any other choice of S either:
1. Includes redundant elements (increasing the sum), or
2. Uses a composite element d covering multiple prime powers, which costs
   φ(d) = Π φ(p^k) ≥ Σ φ(p^k) when each φ(p^k) ≥ 2. -/
@[blueprint "lem:sum-totient-ge-psi"
  (above := /-- We arrive at the combinatorial heart of the forward direction. Given a
  finite-order integer matrix $A$ of order $m$, the minimal polynomial of $A$ is a
  product of cyclotomic polynomials $\Phi_{d_1} \cdots \Phi_{d_r}$ with
  $\mathrm{lcm}(d_1, \ldots, d_r) = m$. The dimension of $A$ is at least
  $\sum \deg \Phi_{d_i} = \sum \varphi(d_i)$. The following bound shows that this sum
  is always at least $\psi(m)$, completing the chain
  $N \geq \sum \varphi(d_i) \geq \psi(m)$. -/)
  (title := "Totient Sum Lower Bound")
  (statement := /-- For any finite set $S$ of divisors of $m$ with $\mathrm{lcm}(S) = m$,
  we have $\psi(m) \leq \sum_{d \in S} \varphi(d)$.

  For a finite set $S$ of divisors of $m$ with $\mathrm{lcm}(S) = m$, we have
  $\sum_{d \in S} \varphi(d) \geq \psi(m)$. This follows from the prime factorization structure:
  each prime power $p^k \| m$ must appear in some $d \in S$, contributing at least
  $\psi_{\mathrm{pp}}(p, k)$. This is the combinatorial heart of the forward direction.
  The minimum sum is achieved when $S$ consists of one prime power for each distinct prime
  in $m$'s prime factorization, giving exactly $\psi(m)$.
  \uses{psi-def, lem:psi-le-totient, lem:finset-nonempty-of-two-le-lcm, lem:finset-exists-one-lt-of-two-le-lcm, lem:prime-pow-achieved-of-lcm-eq} --/)
  (proof := /-- For each prime power $p^k \| m$, some $d \in S$ must have $p^k \mid d$
  (since $\mathrm{lcm}(S) = m$). The element with maximal $p$-valuation contributes
  at least $\varphi(p^k) \geq \psi_{\mathrm{pp}}(p, k)$. Summing over distinct prime powers
  and using non-negativity gives the bound. -/)
  (below := /-- Combined with the cyclotomic divisor structure of minimal polynomials,
  this yields the forward direction of the crystallographic restriction: if
  $A \in \mathrm{GL}_N(\mathbb{Z})$ has order $m$, then $N \geq \psi(m)$. -/)]
lemma sum_totient_ge_psi_of_lcm_eq (m : ℕ) (hm : 0 < m) (S : Finset ℕ)
    (hS_sub : ∀ d ∈ S, d ∣ m) (hS_lcm : S.lcm id = m) :
    psi m ≤ ∑ d ∈ S, Nat.totient d := by
  -- If m ∈ S, apply helper lemma directly
  by_cases hm_in_S : m ∈ S
  · exact totient_sum_ge_psi_of_mem hm S hS_sub hm_in_S
  -- If m ∉ S, we use strong induction on m
  · induction m using Nat.strong_induction_on generalizing S with
    | _ m IH =>
    -- For m = 1: psi(1) = 0 ≤ any sum
    by_cases hm_eq1 : m = 1
    · simp only [hm_eq1, psi_one, Nat.zero_le]
    have hm_ge2 : 2 ≤ m := by omega
    have hS_lcm_ge2 : 2 ≤ S.lcm id := hS_lcm ▸ hm_ge2
    have hS_pos : ∀ d ∈ S, 0 < d := fun d hd => Nat.pos_of_dvd_of_pos (hS_sub d hd) hm
    -- S is nonempty since lcm(S) >= 2
    have _hS_ne : S.Nonempty := Finset.nonempty_of_two_le_lcm hS_lcm_ge2
    -- Some element of S is > 1
    have _hS_has_gt1 : ∃ d ∈ S, 1 < d := Finset.exists_one_lt_of_two_le_lcm hS_pos hS_lcm_ge2
    -- Check if m is a prime power
    by_cases hpow : IsPrimePow m
    · -- m is a prime power p^k: contradiction since p^k must be in S
      exfalso
      rw [isPrimePow_nat_iff] at hpow
      obtain ⟨p, k, hp, hk, hm_eq⟩ := hpow
      exact hm_in_S (hm_eq ▸ Finset.prime_pow_mem_of_lcm_eq hp hk S
        (fun d hd => hm_eq ▸ hS_sub d hd) (hm_eq ▸ hS_lcm))
    · -- m is not a prime power: use achiever function approach
      have h_achieves := primePow_achieved_of_lcm_eq hm S hS_sub hS_lcm
      have h_ach : ∀ q ∈ nontrivialPrimes m, ∃ d ∈ S, q ^ m.factorization q ∣ d := fun q hq =>
        h_achieves q (Finset.mem_of_mem_filter q hq)
      -- Construct achiever function and prove its properties
      let achiever : ℕ → ℕ := fun q =>
        if hq : q ∈ nontrivialPrimes m then (h_ach q hq).choose else 0
      have h_achiever_mem : ∀ q ∈ nontrivialPrimes m, achiever q ∈ S := fun q hq => by
        simp only [achiever, dif_pos hq]; exact (h_ach q hq).choose_spec.1
      have h_achiever_dvd : ∀ q ∈ nontrivialPrimes m, q ^ m.factorization q ∣ achiever q :=
        fun q hq => by simp only [achiever, dif_pos hq]; exact (h_ach q hq).choose_spec.2
      -- Apply the fiberwise bound
      calc psi m
          = ∑ q ∈ nontrivialPrimes m, Nat.totient (q ^ m.factorization q) :=
            psi_eq_sum_nontrivial_totients m
        _ ≤ ∑ d ∈ S, Nat.totient d :=
            sum_nontrivial_totients_le_sum_totients S hS_pos achiever h_achiever_mem h_achiever_dvd


end Crystallographic

