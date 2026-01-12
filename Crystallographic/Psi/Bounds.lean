/-
Copyright (c) 2026 Eric Vergo. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Eric Vergo
-/
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.GCD.BigOperators
import Mathlib.Data.Nat.Totient

import Architect

import Crystallographic.Psi.Basic
import Crystallographic.Lemmas

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
-/

namespace Crystallographic

/-! ## Helper lemmas for the forward direction -/

/-- Totient of a prime power is at least 2 unless it's (2,1). -/
theorem totient_primePow_ge_two {p k : ℕ} (hp : p.Prime) (hk : 0 < k)
    (h : ¬(p = 2 ∧ k = 1)) : 2 ≤ Nat.totient (p ^ k) := by
  rw [Nat.totient_prime_pow hp hk]
  by_cases hp2 : p = 2
  · -- p = 2 but k ≠ 1 (since ¬(p = 2 ∧ k = 1)), so k ≥ 2
    have he_ge2 : 2 ≤ k := by omega
    calc p ^ (k - 1) * (p - 1) = 2 ^ (k - 1) := by rw [hp2]; ring
      _ ≥ 2 ^ 1 := Nat.pow_le_pow_right (by omega) (by omega : 1 ≤ k - 1)
  · -- p ≥ 3
    have hp_ge3 : 3 ≤ p := Nat.lt_of_le_of_ne hp.two_le (Ne.symm hp2)
    calc p ^ (k - 1) * (p - 1) ≥ 1 * (p - 1) := Nat.mul_le_mul_right _ (Nat.one_le_pow _ _ hp.pos)
      _ = p - 1 := one_mul _
      _ ≥ 2 := by omega

/-- For a, b ≥ 2, we have a + b ≤ a * b. -/
theorem sum_le_prod_of_ge_two {a b : ℕ} (ha : 2 ≤ a) (hb : 2 ≤ b) : a + b ≤ a * b := by
  -- Key: a ≤ b * (a - 1) when b ≥ 2 and a ≥ 2
  -- Since 2*(a-1) ≥ a when a ≥ 2
  have ha_pos : 0 < a := by omega
  have key : a ≤ b * (a - 1) := by
    calc a ≤ 2 * (a - 1) := by omega
      _ ≤ b * (a - 1) := Nat.mul_le_mul_right _ hb
  calc a + b ≤ b * (a - 1) + b := Nat.add_le_add_right key b
    _ = b * (a - 1 + 1) := by ring
    _ = b * a := by rw [Nat.sub_add_cancel (by omega : 1 ≤ a)]
    _ = a * b := by ring

/-- For m > 2 that is not a prime power, we can factor m = p^e * m' with:
    - p is the minimal prime factor
    - 0 < e = ord_p(m)
    - p^e and m' are coprime
    - 1 < m' < m
    - p^e < m -/
theorem factorization_split_lt {m : ℕ} (hm : 2 < m) (h_not_pp : ¬IsPrimePow m) :
    ∃ (p e m' : ℕ), p.Prime ∧ 0 < e ∧ p ^ e * m' = m ∧
    (p ^ e).Coprime m' ∧ 1 < m' ∧ m' < m ∧ p ^ e < m := by
  have hm_ne_zero : m ≠ 0 := by omega
  have hm_ne_one : m ≠ 1 := by omega
  have hm_pos : 0 < m := by omega
  have hminFac_prime : m.minFac.Prime := Nat.minFac_prime hm_ne_one
  set p := m.minFac
  set e := m.factorization p
  have he_pos : 0 < e := Nat.Prime.factorization_pos_of_dvd hminFac_prime hm_ne_zero (Nat.minFac_dvd m)
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

/-- For m odd and m >= 3, we have psi(m) > 0.
This is because m has an odd prime factor q >= 3, which contributes phi(q^k) > 0 to psi. -/
theorem psi_pos_of_odd_ge_three {m : ℕ} (hm : 3 ≤ m) (hm_odd : Odd m) :
    0 < Crystallographic.psi m := by
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
  have hcontrib : Crystallographic.psiPrimePow q (m.factorization q) ≤
      Crystallographic.psi m :=
    Crystallographic.psi_ge_psiPrimePow_of_mem_support (by omega) hq_in_support
  -- psiPrimePow(q, k) = totient(q^k) > 0 for q >= 3 (since q != 2 means (q, k) != (2, 1))
  have hcontrib_pos : 0 < Crystallographic.psiPrimePow q (m.factorization q) := by
    simp only [Crystallographic.psiPrimePow]
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
  (latexEnv := "auxlemma")
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
  by the inductive hypothesis and multiplicativity of $\varphi$. -/)]
lemma psi_le_totient (m : ℕ) (hm : 0 < m) : Crystallographic.psi m ≤ Nat.totient m := by
  -- Strong induction on m
  induction m using Nat.strong_induction_on with
  | _ m IH =>
  -- Handle small cases separately
  rcases Nat.lt_trichotomy m 1 with hm0 | rfl | hm_gt1
  · omega -- m < 1 contradicts hm
  · simp [Crystallographic.psi_one] -- m = 1
  · rcases Nat.lt_trichotomy m 2 with hm_lt2 | rfl | hm_ge3
    · omega -- m < 2 but m > 1, contradiction
    · simp [Crystallographic.psi_two] -- m = 2
    · -- m ≥ 3
      have hm_gt1 : 1 < m := by omega
      -- Check if m is a prime power
      by_cases hpow : IsPrimePow m
      · -- m is a prime power p^k
        rw [isPrimePow_nat_iff] at hpow
        obtain ⟨p, k, hp, hk, rfl⟩ := hpow
        rw [Crystallographic.psi_prime_pow p k hp hk]
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
        rw [← hm_eq, Crystallographic.psi_coprime_add _ _ (Nat.pow_pos hp.pos) hm'_pos hcop,
            Nat.totient_mul hcop]
        -- By IH: psi(m') ≤ totient(m')
        have IH_m' : Crystallographic.psi m' ≤ Nat.totient m' := IH m' hm'_lt hm'_pos
        -- For the prime power part: psi(p^e) ≤ totient(p^e)
        have hpsi_pe : Crystallographic.psi (p ^ e) ≤ Nat.totient (p ^ e) := by
          rw [Crystallographic.psi_prime_pow p e hp he_pos]
          split_ifs <;> simp
        -- Three cases based on whether p^e or m' equals 2
        by_cases h21 : p = 2 ∧ e = 1
        · -- Case 1: p^e = 2, so psi(2) = 0 and totient(2) = 1
          obtain ⟨hp2, he1⟩ := h21
          simp only [hp2, he1, pow_one, Crystallographic.psi_two, Nat.totient_two, zero_add, one_mul]
          exact IH_m'
        · by_cases hm'2 : m' = 2
          · -- Case 2: m' = 2, so psi(2) = 0 and totient(2) = 1
            simp only [hm'2, Crystallographic.psi_two, Nat.totient_two, add_zero, mul_one]
            exact hpsi_pe
          · -- Case 3: Neither is 2^1, so both totients >= 2
            have htot_m'_ge2 : 2 ≤ Nat.totient m' :=
              totient_ge_two_of_gt_two m' (by omega : 2 < m')
            have htot_pe_ge2 : 2 ≤ Nat.totient (p ^ e) := totient_primePow_ge_two hp he_pos h21
            calc Crystallographic.psi (p ^ e) + Crystallographic.psi m'
                ≤ Nat.totient (p ^ e) + Nat.totient m' := by omega
              _ ≤ Nat.totient (p ^ e) * Nat.totient m' := sum_le_prod_of_ge_two htot_pe_ge2 htot_m'_ge2

/-- Key lemma: For any S ⊆ m.divisors with lcm(S) = m, we have Σ_{d∈S} φ(d) ≥ psi(m).

This is the combinatorial heart of the forward direction. The minimum is achieved when
S consists of one prime power for each distinct prime in m's factorization, giving psi(m).

The proof proceeds by showing that any other choice of S either:
1. Includes redundant elements (increasing the sum), or
2. Uses a composite element d covering multiple prime powers, which costs
   φ(d) = Π φ(p^k) ≥ Σ φ(p^k) when each φ(p^k) ≥ 2. -/
@[blueprint "lem:sum-totient-ge-psi"
  (latexEnv := "auxlemma")
  (statement := /-- For any finite set $S$ of divisors of $m$ with $\mathrm{lcm}(S) = m$,
  we have $\psi(m) \leq \sum_{d \in S} \varphi(d)$.

  For a finite set $S$ of divisors of $m$ with $\mathrm{lcm}(S) = m$, we have
  $\sum_{d \in S} \varphi(d) \geq \psi(m)$. This follows from the prime factorization structure:
  each prime power $p^k \| m$ must appear in some $d \in S$, contributing at least
  $\psi_{\mathrm{pp}}(p, k)$. This is the combinatorial heart of the forward direction.
  The minimum sum is achieved when $S$ consists of one prime power for each distinct prime
  in $m$'s prime factorization, giving exactly $\psi(m)$.
  \uses{psi-def, lem:psi-le-totient} --/)
  (proof := /-- For each prime power $p^k \| m$, some $d \in S$ must have $p^k \mid d$
  (since $\mathrm{lcm}(S) = m$). The element with maximal $p$-valuation contributes
  at least $\varphi(p^k) \geq \psi_{\mathrm{pp}}(p, k)$. Summing over distinct prime powers
  and using non-negativity gives the bound. -/)]
lemma sum_totient_ge_psi_of_lcm_eq (m : ℕ) (hm : 0 < m) (S : Finset ℕ)
    (hS_sub : ∀ d ∈ S, d ∣ m) (hS_lcm : S.lcm id = m) :
    Crystallographic.psi m ≤ ∑ d ∈ S, Nat.totient d := by
  -- If m ∈ S, then ∑ φ(d) ≥ φ(m) ≥ psi(m) by psi_le_totient
  by_cases hm_in_S : m ∈ S
  · calc Crystallographic.psi m ≤ Nat.totient m := psi_le_totient m hm
      _ ≤ ∑ d ∈ S, Nat.totient d := Finset.single_le_sum
          (fun d _ => Nat.le_of_lt (Nat.totient_pos.mpr (Nat.pos_of_mem_divisors
            (Nat.mem_divisors.mpr ⟨hS_sub d (by assumption), hm.ne'⟩)))) hm_in_S
  -- If m ∉ S, we use strong induction on m
  · induction m using Nat.strong_induction_on generalizing S with
    | _ m IH =>
    -- The lcm(S) = m condition with m ∉ S means S has multiple elements
    -- whose combined prime powers give m.
    --
    -- For m = 1: lcm(S) = 1 forces S ⊆ {1}, and psi(1) = 0 ≤ any sum
    by_cases hm_eq1 : m = 1
    · simp only [hm_eq1, Crystallographic.psi_one, Nat.zero_le]
    have hm_ge2 : 2 ≤ m := by omega
    -- For m ≥ 2: S nonempty (since lcm(S) = m ≥ 2 requires S ≠ ∅)
    -- Pick some element d ∈ S with d ≠ 1
    have hS_nonempty : S.Nonempty := by
      by_contra hempty
      simp only [Finset.not_nonempty_iff_eq_empty] at hempty
      simp only [hempty, Finset.lcm_empty] at hS_lcm
      omega
    -- There exists d ∈ S with d > 1 (since lcm > 1)
    have hexists_gt1 : ∃ d ∈ S, 1 < d := by
      by_contra hall_le1
      push_neg at hall_le1
      -- If all d ∈ S satisfy d ≤ 1, then since d > 0 (as d | m > 0), d = 1
      -- So S ⊆ {1}, which means lcm(S) = 1, contradicting lcm(S) = m ≥ 2
      have hall_eq1 : ∀ d ∈ S, d = 1 := by
        intro d hd
        have hd_pos : 0 < d := Nat.pos_of_dvd_of_pos (hS_sub d hd) hm
        have hd_le1 := hall_le1 d hd
        omega
      have hlcm_eq1 : S.lcm id = 1 := by
        apply Nat.eq_one_of_dvd_one
        apply Finset.lcm_dvd_iff.mpr
        intro d hd
        simp only [id_eq, hall_eq1 d hd, Nat.one_dvd]
      omega
    obtain ⟨d, hd_in_S, hd_gt1⟩ := hexists_gt1
    -- d divides m
    have hd_dvd_m := hS_sub d hd_in_S
    -- d ≠ m (since m ∉ S)
    have hd_ne_m : d ≠ m := fun heq => hm_in_S (heq ▸ hd_in_S)
    have hd_lt_m : d < m := Nat.lt_of_le_of_ne (Nat.le_of_dvd hm hd_dvd_m) hd_ne_m
    have hd_pos : 0 < d := Nat.zero_lt_of_lt hd_gt1
    -- Check if m is a prime power
    by_cases hpow : IsPrimePow m
    · -- m is a prime power p^k - use extracted lemma
      exfalso
      rw [isPrimePow_nat_iff] at hpow
      obtain ⟨p, k, hp, hk, hm_eq⟩ := hpow
      have hS_sub' : ∀ d ∈ S, d ∣ p ^ k := fun d hd => hm_eq ▸ hS_sub d hd
      have hS_lcm' : S.lcm id = p ^ k := hm_eq ▸ hS_lcm
      exact hm_in_S (hm_eq ▸ Crystallographic.primePow_mem_of_lcm_eq hp hk S hS_sub' hS_lcm')
    · -- m is not a prime power, so it has ≥ 2 distinct prime factors
      -- Factor m = a * b with coprime a, b > 1
      -- Use psi(m) = psi(a) + psi(b) and recursion
      have hm_ne_zero : m ≠ 0 := hm.ne'
      have hminFac : m.minFac.Prime := Nat.minFac_prime (by omega : m ≠ 1)
      have hminFac_dvd : m.minFac ∣ m := Nat.minFac_dvd m
      set p := m.minFac with hp_def
      set e := m.factorization p with he_def
      have he_pos : 0 < e := Nat.Prime.factorization_pos_of_dvd hminFac hm_ne_zero hminFac_dvd
      have hdvd_pe : p ^ e ∣ m := Nat.ordProj_dvd m p
      set m' := m / p ^ e with hm'_def
      have hm'_pos : 0 < m' := Nat.div_pos (Nat.le_of_dvd hm hdvd_pe) (Nat.pow_pos hminFac.pos)
      have hm_eq : m = p ^ e * m' := (Nat.mul_div_cancel' hdvd_pe).symm
      have hcop : Nat.Coprime (p ^ e) m' := Nat.coprime_ordCompl hminFac hm_ne_zero |>.pow_left e
      -- m' ≠ 1 because m is not a prime power
      have hm'_ne_one : m' ≠ 1 := by
        intro hm'_one
        apply hpow
        rw [isPrimePow_nat_iff]
        exact ⟨p, e, hminFac, he_pos, by rw [hm_eq, hm'_one, mul_one]⟩
      have hm'_lt : m' < m := by
        have hpe_ge2 : 2 ≤ p ^ e := by
          calc p ^ e ≥ p ^ 1 := Nat.pow_le_pow_right (Nat.Prime.one_lt hminFac).le he_pos
            _ = p := pow_one p
            _ ≥ 2 := Nat.Prime.two_le hminFac
        calc m' = 1 * m' := (one_mul _).symm
          _ < p ^ e * m' := Nat.mul_lt_mul_of_pos_right
              (Nat.one_lt_pow he_pos.ne' (Nat.Prime.one_lt hminFac)) hm'_pos
          _ = m := hm_eq.symm
      have hpe_lt : p ^ e < m := by
        have hm'_ge2 : 2 ≤ m' := by omega
        calc p ^ e = p ^ e * 1 := (mul_one _).symm
          _ < p ^ e * m' := Nat.mul_lt_mul_of_pos_left (by omega) (Nat.pow_pos hminFac.pos)
          _ = m := hm_eq.symm

      have h_achieves : ∀ q ∈ m.factorization.support,
          ∃ d ∈ S, q ^ m.factorization q ∣ d := by
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
      calc Crystallographic.psi m
        -- psi(m) = sum over nontrivial primes of φ(p^{ord_p(m)})
          = (m.factorization.support.filter (fun q => ¬(q = 2 ∧ m.factorization q = 1))).sum
              (fun q => Nat.totient (q ^ m.factorization q)) := by
            unfold Crystallographic.psi
            simp only [Finsupp.sum, Finset.sum_filter]
            apply Finset.sum_congr rfl
            intro q hq
            simp only [Crystallographic.psiPrimePow]
            have hk_pos : 0 < m.factorization q :=
              Finsupp.mem_support_iff.mp hq |> Nat.pos_of_ne_zero
            simp only [hk_pos.ne', ite_false]
            by_cases hqk : q = 2 ∧ m.factorization q = 1
            · simp [hqk]
            · simp [hqk]
        -- Each nontrivial prime q has some d ∈ S with q^{ord_q(m)} | d
        -- ∑_q φ(q^{ord_q(m)}) ≤ ∑_d φ(d) via the covering argument
          _ ≤ ∑ d ∈ S, Nat.totient d := by
            -- Define NT = nontrivial primes of m
            let NT := m.factorization.support.filter (fun q => ¬(q = 2 ∧ m.factorization q = 1))
            -- For each q ∈ NT, there exists an achiever d_q ∈ S with q^{ord_q(m)} | d_q
            have h_ach : ∀ q ∈ NT, ∃ d ∈ S, q ^ m.factorization q ∣ d := fun q hq =>
              h_achieves q (Finset.mem_of_mem_filter q hq)
            have hS_pos : ∀ d ∈ S, 0 < d := fun d hd => Nat.pos_of_dvd_of_pos (hS_sub d hd) hm
            -- Choose a specific achiever function for each q (using 0 as default for q ∉ NT)
            -- The achiever function maps q to some d ∈ S with q^{ord_q(m)} | d
            let achiever : ℕ → ℕ := fun q =>
              if hq : q ∈ NT then (h_ach q hq).choose else 0
            have h_achiever : ∀ q ∈ NT,
                achiever q ∈ S ∧ q ^ m.factorization q ∣ achiever q := by
              intro q hq
              have heq : achiever q = (h_ach q hq).choose := dif_pos hq
              rw [heq]
              exact (h_ach q hq).choose_spec
            -- The sum over NT is bounded by sum over S via the fiberwise argument
            -- ∑_{q∈NT} φ(q^k) = ∑_{d∈S} ∑_{q∈NT: achiever q = d} φ(q^k)
            --                 ≤ ∑_{d∈S} φ(d)
            -- The key inequality: for each d, ∑_{q: achiever q = d} φ(q^k) ≤ φ(d)
            -- This uses: φ(d) ≥ ∏_{q: q^k | d} φ(q^k) ≥ ∑_{q: q^k | d} φ(q^k)
            -- (product ≥ sum when all factors ≥ 2, which holds for nontrivial primes)
            -- Use fiberwise sum: ∑_{q∈NT} f(q) = ∑_{d∈S} ∑_{q∈NT: achiever q = d} f(q)
            have h_fiberwise : ∑ q ∈ NT, Nat.totient (q ^ m.factorization q) =
                ∑ d ∈ S, ∑ q ∈ NT.filter (fun q => achiever q = d),
                  Nat.totient (q ^ m.factorization q) := by
              symm
              apply Finset.sum_fiberwise_of_maps_to
              intro q hq; exact (h_achiever q hq).1
            calc ∑ q ∈ NT, Nat.totient (q ^ m.factorization q)
              = ∑ d ∈ S, ∑ q ∈ NT.filter (fun q => achiever q = d),
                  Nat.totient (q ^ m.factorization q) := h_fiberwise
              _ ≤ ∑ d ∈ S, Nat.totient d := by
                apply Finset.sum_le_sum
                intro d hd
                -- For this d, bound the fiber sum by φ(d)
                -- The fiber consists of q ∈ NT where achiever q = d
                let fiber := NT.filter (fun q => achiever q = d)
                -- For each q in fiber, q^{ord_q(m)} | d (by achiever property)
                have h_fiber_dvd : ∀ q ∈ fiber, q ^ m.factorization q ∣ d := by
                  intro q hq
                  have hq_NT : q ∈ NT := Finset.mem_of_mem_filter q hq
                  have hq_eq : achiever q = d := (Finset.mem_filter.mp hq).2
                  rw [← hq_eq]
                  exact (h_achiever q hq_NT).2
                -- The fiber elements are distinct primes
                have h_fiber_primes : ∀ q ∈ fiber, q.Prime := by
                  intro q hq
                  have hq_supp := Finset.mem_of_mem_filter q (Finset.mem_of_mem_filter q hq)
                  exact Nat.prime_of_mem_primeFactors (Nat.support_factorization m ▸ hq_supp)
                -- The fiber elements have totients ≥ 2 (nontrivial condition)
                have h_fiber_ge2 : ∀ q ∈ fiber, 2 ≤ Nat.totient (q ^ m.factorization q) := by
                  intro q hq
                  have hq_NT := Finset.mem_of_mem_filter q hq
                  have hq_supp := Finset.mem_of_mem_filter q hq_NT
                  have hq_prime := Nat.prime_of_mem_primeFactors (Nat.support_factorization m ▸ hq_supp)
                  have hk_pos : 0 < m.factorization q := Finsupp.mem_support_iff.mp hq_supp |> Nat.pos_of_ne_zero
                  have hqk_nontrivial : ¬(q = 2 ∧ m.factorization q = 1) := (Finset.mem_filter.mp hq_NT).2
                  exact totient_primePow_ge_two hq_prime hk_pos hqk_nontrivial
                -- Now show: ∑_{q∈fiber} φ(q^k) ≤ φ(d)
                -- Use: φ(d) ≥ ∏_{q∈fiber} φ(q^k) ≥ ∑_{q∈fiber} φ(q^k)
                -- The first inequality: since q^{ord_q(m)} | d for each q in fiber,
                -- and these are distinct primes, ∏_{q∈fiber} q^{ord_q(m)} | d.
                -- Hence φ(d) ≥ φ(∏_{q∈fiber} q^k) = ∏_{q∈fiber} φ(q^k).
                -- The second: ∏ ≥ ∑ when all factors ≥ 2.
                by_cases h_fiber_empty : fiber = ∅
                · -- Empty fiber: the sum over fiber is 0, which is ≤ φ(d)
                  -- The sum is over `NT with achiever q = d` which equals `fiber`
                  have h_eq : NT.filter (fun q => achiever q = d) = fiber := rfl
                  rw [h_eq, h_fiber_empty, Finset.sum_empty]
                  exact Nat.zero_le _
                · have h_fiber_nonempty : fiber.Nonempty :=
                    Finset.nonempty_of_ne_empty h_fiber_empty
                  -- The primes in fiber are pairwise coprime
                  have h_coprime : ∀ q₁ ∈ fiber, ∀ q₂ ∈ fiber, q₁ ≠ q₂ →
                      (q₁ ^ m.factorization q₁).Coprime (q₂ ^ m.factorization q₂) := by
                    intro q₁ hq₁ q₂ hq₂ hne
                    apply Nat.Coprime.pow
                    exact (Nat.coprime_primes (h_fiber_primes q₁ hq₁)
                      (h_fiber_primes q₂ hq₂)).mpr hne
                  -- ∏_{q∈fiber} q^{ord_q(m)} divides d
                  have h_prod_dvd : (∏ q ∈ fiber, q ^ m.factorization q) ∣ d :=
                    Finset.prod_coprime_dvd fiber (fun q => q ^ m.factorization q) d h_fiber_dvd h_coprime
                  -- φ(d) ≥ φ(∏_{q∈fiber} q^{ord_q(m)})
                  -- φ(∏ q^k) = ∏ φ(q^k) by coprimality
                  have h_totient_prod : Nat.totient (∏ q ∈ fiber, q ^ m.factorization q) =
                      ∏ q ∈ fiber, Nat.totient (q ^ m.factorization q) :=
                    Nat.totient_finset_prod_of_coprime fiber (fun q => q ^ m.factorization q) h_coprime
                  -- φ(n) | φ(d) when n | d, hence φ(n) ≤ φ(d)
                  have h_totient_ge_prod : ∏ q ∈ fiber, Nat.totient (q ^ m.factorization q) ≤
                      Nat.totient d := by
                    rw [← h_totient_prod]
                    have h_dvd : Nat.totient (∏ q ∈ fiber, q ^ m.factorization q) ∣
                        Nat.totient d := Nat.totient_dvd_of_dvd h_prod_dvd
                    have h_pos : 0 < Nat.totient d := Nat.totient_pos.mpr (hS_pos d hd)
                    exact Nat.le_of_dvd h_pos h_dvd
                  -- ∏ ≥ ∑ when all factors ≥ 2
                  have h_prod_ge_sum : ∑ q ∈ fiber, Nat.totient (q ^ m.factorization q) ≤
                      ∏ q ∈ fiber, Nat.totient (q ^ m.factorization q) :=
                    Finset.sum_le_prod_of_all_ge_two fiber _ h_fiber_ge2
                  exact le_trans h_prod_ge_sum h_totient_ge_prod


end Crystallographic
