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

import Crystallographic.Definitions.Psi

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

/-- psiPrimePow is always ≤ totient. -/
lemma psiPrimePow_le_totient (p k : ℕ) :
    Crystallographic.psiPrimePow p k ≤ Nat.totient (p ^ k) := by
  simp only [Crystallographic.psiPrimePow]
  split_ifs with hk h2
  · simp [hk]
  · obtain ⟨rfl, rfl⟩ := h2
    simp [Nat.totient_prime Nat.prime_two]
  · exact le_refl _


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
  (statement := /-- For all $m \geq 1$, we have $\psi(m) \leq \varphi(m)$.

  The proof proceeds by strong induction on $m$:
  \begin{itemize}
  \item For $m = 1$: $\psi(1) = 0 \leq 1 = \varphi(1)$
  \item For prime powers $p^k$: $\psi(p^k) = \varphi(p^k)$ (with the exception $\psi(2) = 0$)
  \item For composite $m = 2 \cdot \text{odd}$: $\psi(m) = \psi(\text{odd}) \leq \varphi(\text{odd}) = \varphi(m)$
  \item For general composite without $2^1$ factor: each $\varphi(p^k) \geq 2$, so sum $\leq$ product
  \end{itemize}
  \uses{psi-def, psiPrimePow-def} --/)]
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
        -- Factor m as p^e * m' where p is the smallest prime factor
        have hm_ne_one : m ≠ 1 := by omega
        have hminFac_prime : m.minFac.Prime := Nat.minFac_prime hm_ne_one
        set p := m.minFac
        set e := m.factorization p
        have he_pos : 0 < e := Nat.Prime.factorization_pos_of_dvd hminFac_prime (by omega)
          (Nat.minFac_dvd m)
        have hdvd : p ^ e ∣ m := Nat.ordProj_dvd m p
        set m' := m / p ^ e
        have hm'_pos : 0 < m' := Nat.div_pos (Nat.le_of_dvd hm hdvd) (Nat.pow_pos hminFac_prime.pos)
        have hm_eq : m = p ^ e * m' := (Nat.mul_div_cancel' hdvd).symm
        have hcop : Nat.Coprime (p ^ e) m' := Nat.coprime_ordCompl hminFac_prime (by omega)
          |>.pow_left e
        -- m' ≠ 1 because m is not a prime power
        have hm'_ne_one : m' ≠ 1 := by
          intro hm'_one
          apply hpow
          rw [isPrimePow_nat_iff]
          exact ⟨p, e, hminFac_prime, he_pos, by rw [hm_eq, hm'_one, mul_one]⟩
        have hm'_lt : m' < m := by
          have hpe_ge2 : 2 ≤ p ^ e := by
            calc p ^ e ≥ p ^ 1 := Nat.pow_le_pow_right hminFac_prime.one_lt.le he_pos
              _ = p := pow_one p
              _ ≥ 2 := hminFac_prime.two_le
          calc m' = 1 * m' := (one_mul _).symm
            _ < p ^ e * m' := Nat.mul_lt_mul_of_pos_right
                (Nat.one_lt_pow he_pos.ne' hminFac_prime.one_lt) hm'_pos
            _ = m := hm_eq.symm
        -- psi and totient are additive/multiplicative on coprime factors
        rw [hm_eq,
            Crystallographic.psi_coprime_add _ _ (Nat.pow_pos hminFac_prime.pos) hm'_pos hcop,
            Nat.totient_mul hcop]
        -- Now we need: psi(p^e) + psi(m') ≤ totient(p^e) * totient(m')
        -- By IH: psi(m') ≤ totient(m')
        have IH_m' : Crystallographic.psi m' ≤ Nat.totient m' := IH m' hm'_lt hm'_pos
        -- For the prime power part: psi(p^e) ≤ totient(p^e)
        have hpsi_pe : Crystallographic.psi (p ^ e) ≤ Nat.totient (p ^ e) := by
          rw [Crystallographic.psi_prime_pow p e hminFac_prime he_pos]
          split_ifs <;> simp
        -- Now show psi(p^e) + psi(m') ≤ totient(p^e) * totient(m')
        -- This follows from: a + b ≤ a * b when a ≥ 1 and b ≥ 2, or when a = 0
        -- Need to show: psi(p^e) + psi(m') ≤ totient(p^e) * totient(m')
        -- Three cases:
        -- 1. p = 2 and e = 1: psi(2) = 0, totient(2) = 1 → psi(m') ≤ totient(m')
        -- 2. m' = 2: psi(2) = 0, totient(2) = 1 → psi(p^e) ≤ totient(p^e)
        -- 3. Otherwise: both totients ≥ 2, use a + b ≤ a * b
        by_cases h21 : p = 2 ∧ e = 1
        · -- Case 1: p = 2 and e = 1: psi(2) = 0, totient(2) = 1
          obtain ⟨hp2, he1⟩ := h21
          have hpsi_2 : Crystallographic.psi (2 ^ 1) = 0 := by
            simp only [pow_one, Crystallographic.psi_two]
          have htot_2 : Nat.totient (2 ^ 1) = 1 := by
            simp only [pow_one, Nat.totient_prime Nat.prime_two]
          calc Crystallographic.psi (p ^ e) + Crystallographic.psi m'
              = Crystallographic.psi (2 ^ 1) + Crystallographic.psi m' := by rw [hp2, he1]
            _ = 0 + Crystallographic.psi m' := by rw [hpsi_2]
            _ = Crystallographic.psi m' := by ring
            _ ≤ Nat.totient m' := IH_m'
            _ = 1 * Nat.totient m' := by ring
            _ = Nat.totient (2 ^ 1) * Nat.totient m' := by rw [htot_2]
            _ = Nat.totient (p ^ e) * Nat.totient m' := by rw [hp2, he1]
        · by_cases hm'2 : m' = 2
          · -- Case 2: m' = 2: psi(2) = 0, totient(2) = 1
            have hpsi_2 : Crystallographic.psi 2 = 0 := Crystallographic.psi_two
            have htot_2 : Nat.totient 2 = 1 := Nat.totient_prime Nat.prime_two
            calc Crystallographic.psi (p ^ e) + Crystallographic.psi m'
                = Crystallographic.psi (p ^ e) + Crystallographic.psi 2 := by rw [hm'2]
              _ = Crystallographic.psi (p ^ e) + 0 := by rw [hpsi_2]
              _ = Crystallographic.psi (p ^ e) := by ring
              _ ≤ Nat.totient (p ^ e) := hpsi_pe
              _ = Nat.totient (p ^ e) * 1 := by ring
              _ = Nat.totient (p ^ e) * Nat.totient 2 := by rw [htot_2]
              _ = Nat.totient (p ^ e) * Nat.totient m' := by rw [hm'2]
          · -- Case 3: Neither is 2^1, so both totients ≥ 2
            have htot_m'_ge2 : 2 ≤ Nat.totient m' := by
              -- m' > 1 and m' ≠ 1, 2, so totient(m') ≥ 2
              have hm'_ge3 : 3 ≤ m' := by
                have hm'_ge2 : 2 ≤ m' := by omega
                rcases Nat.eq_or_lt_of_le hm'_ge2 with h | h
                · exact (hm'2 h.symm).elim
                · omega
              have htot_pos : 0 < Nat.totient m' := Nat.totient_pos.mpr hm'_pos
              have hne1 : Nat.totient m' ≠ 1 := by
                intro htot_eq1
                have h12 := Nat.totient_eq_one_iff.mp htot_eq1
                rcases h12 with h1 | h2
                · exact hm'_ne_one h1
                · exact hm'2 h2
              omega
            have htot_pe_ge2 : 2 ≤ Nat.totient (p ^ e) := by
              rw [Nat.totient_prime_pow hminFac_prime he_pos]
              by_cases hp2 : p = 2
              · -- p = 2, but e ≠ 1 since ¬(p = 2 ∧ e = 1)
                have he_ge2 : 2 ≤ e := by omega
                calc p ^ (e - 1) * (p - 1) = 2 ^ (e - 1) * (2 - 1) := by rw [hp2]
                  _ = 2 ^ (e - 1) := by ring
                  _ ≥ 2 ^ 1 := Nat.pow_le_pow_right (by omega) (by omega : 1 ≤ e - 1)
                  _ = 2 := by ring
              · -- p ≥ 3
                have hp_ge3 : 3 ≤ p := Nat.lt_of_le_of_ne hminFac_prime.two_le (Ne.symm hp2)
                calc p ^ (e - 1) * (p - 1) ≥ 1 * (p - 1) :=
                    Nat.mul_le_mul_right _ (Nat.one_le_pow _ _ hminFac_prime.pos)
                  _ = p - 1 := one_mul _
                  _ ≥ 3 - 1 := Nat.sub_le_sub_right hp_ge3 1
                  _ = 2 := by norm_num
            calc Crystallographic.psi (p ^ e) + Crystallographic.psi m'
              ≤ Crystallographic.psi (p ^ e) + Nat.totient m' := Nat.add_le_add_left IH_m' _
            _ ≤ Nat.totient (p ^ e) + Nat.totient m' := Nat.add_le_add_right hpsi_pe _
            _ ≤ Nat.totient (p ^ e) * Nat.totient m' := by
                -- Now we have a ≥ 2 and b ≥ 2, so a + b ≤ a * b
                -- a + b ≤ a * b ⟺ a + b ≤ a * b ⟺ 1 ≤ a * (b - 1) + (1 - a) (rearranging)
                -- Actually: a + b ≤ a * b ⟺ a ≤ a * b - b = (a - 1) * b ⟺ a ≤ (a - 1) * b
                -- For b ≥ 2 and a ≥ 2: (a - 1) * b ≥ 1 * 2 = 2 ≥ a? No, a can be large.
                -- Better: a + b ≤ a*b ⟺ a/b + 1 ≤ a ⟺ 1/b ≤ (a-1)/a ⟺ a ≤ b*(a-1)
                -- Since b ≥ 2, b * (a - 1) ≥ 2 * (a - 1) = 2a - 2 ≥ a when a ≥ 2.
                -- So the key is: for a ≥ 2 and b ≥ 2, 2a - 2 ≥ a, i.e., a ≥ 2. ✓
                have key : Nat.totient (p ^ e) ≤ Nat.totient m' * (Nat.totient (p ^ e) - 1) := by
                  calc Nat.totient (p ^ e) ≤ 2 * (Nat.totient (p ^ e) - 1) := by omega
                    _ ≤ Nat.totient m' * (Nat.totient (p ^ e) - 1) :=
                        Nat.mul_le_mul_right _ htot_m'_ge2
                -- Now: a + b ≤ a * b ⟺ a ≤ a * (b - 1) ⟺ a ≤ (b - 1) * a
                -- We have: a ≤ b * (a - 1) from key
                -- Hmm, let me just be more direct
                calc Nat.totient (p ^ e) + Nat.totient m'
                    ≤ Nat.totient m' * (Nat.totient (p ^ e) - 1) + Nat.totient m' := by
                      exact Nat.add_le_add_right key _
                  _ = Nat.totient m' * ((Nat.totient (p ^ e) - 1) + 1) := by ring
                  _ = Nat.totient m' * Nat.totient (p ^ e) := by
                      congr 1
                      omega
                  _ = Nat.totient (p ^ e) * Nat.totient m' := by ring

/-- Key lemma: For any S ⊆ m.divisors with lcm(S) = m, we have Σ_{d∈S} φ(d) ≥ psi(m).

This is the combinatorial heart of the forward direction. The minimum is achieved when
S consists of one prime power for each distinct prime in m's factorization, giving psi(m).

The proof proceeds by showing that any other choice of S either:
1. Includes redundant elements (increasing the sum), or
2. Uses a composite element d covering multiple prime powers, which costs
   φ(d) = Π φ(p^k) ≥ Σ φ(p^k) when each φ(p^k) ≥ 2. -/
@[blueprint "lem:sum-totient-ge-psi"
  (statement := /-- For any finite set $S$ of divisors of $m$ with $\mathrm{lcm}(S) = m$,
  we have $\psi(m) \leq \sum_{d \in S} \varphi(d)$.

  This is the combinatorial heart of the forward direction. The minimum sum is achieved when
  $S$ consists of one prime power for each distinct prime in $m$'s factorization, giving exactly $\psi(m)$.
  \uses{psi-def, lem:psi-le-totient} --/)]
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
    · -- m is a prime power p^k
      -- For lcm(S) = p^k with all elements dividing p^k, some element must equal p^k
      -- (since divisors of p^k are 1, p, p^2, ..., p^k and lcm of smaller ones < p^k)
      exfalso
      rw [isPrimePow_nat_iff] at hpow
      obtain ⟨p, k, hp, hk, hm_eq⟩ := hpow
      -- S consists of divisors of p^k = m, i.e., powers of p
      -- The lcm of powers of p is the maximum power
      -- So lcm(S) = p^k = m requires m ∈ S (the only way to get full p^k)
      -- This contradicts hm_in_S
      --
      -- Key fact: for divisors of a prime power p^k, lcm equals the max
      -- If all d ∈ S satisfy d < m = p^k, then they're all ≤ p^(k-1)
      -- and lcm(S) ≤ p^(k-1) < p^k = m, contradiction
      have : m ∈ S := by
        by_contra hm_not_in
        -- All elements of S are proper divisors of m = p^k
        -- So they're ≤ p^(k-1)
        have hall_lt : ∀ d ∈ S, d < m := fun d hd =>
          Nat.lt_of_le_of_ne (Nat.le_of_dvd hm (hS_sub d hd))
            (fun heq => hm_not_in (heq ▸ hd))
        -- For prime power m = p^k, proper divisors are ≤ p^(k-1)
        have hall_le : ∀ d ∈ S, d ∣ p ^ (k - 1) := by
          intro d hd
          have hdvd : d ∣ m := hS_sub d hd
          rw [← hm_eq] at hdvd
          have hd_lt := hall_lt d hd
          rw [← hm_eq] at hd_lt
          -- d | p^k and d < p^k, so d | p^(k-1)
          have hpr : Prime p := Nat.Prime.prime hp
          rw [dvd_prime_pow hpr] at hdvd
          obtain ⟨j, hj, hassoc⟩ := hdvd
          have hd_eq := associated_iff_eq.mp hassoc
          -- d = p^j and d < p^k, so p^j < p^k, hence j < k
          rw [hd_eq] at hd_lt
          have hj_lt : j < k := (Nat.pow_lt_pow_iff_right hp.one_lt).mp hd_lt
          -- j < k implies j ≤ k - 1
          have hj_le : j ≤ k - 1 := Nat.lt_succ_iff.mp (by omega)
          -- d = p^j with j ≤ k-1, so d | p^(k-1)
          rw [hd_eq]
          exact Nat.pow_dvd_pow p hj_le
        -- lcm of divisors of p^(k-1) is ≤ p^(k-1)
        have hlcm_le : S.lcm id ∣ p ^ (k - 1) := Finset.lcm_dvd_iff.mpr (fun d hd => hall_le d hd)
        -- But lcm(S) = m = p^k, so p^k | p^(k-1), contradiction for k > 0
        rw [hS_lcm, ← hm_eq] at hlcm_le
        have : p ^ k ≤ p ^ (k - 1) := Nat.le_of_dvd (Nat.pow_pos hp.pos) hlcm_le
        have hk_gt1 : 1 ≤ k := hk
        have hpow_strict : p ^ (k - 1) < p ^ k :=
          Nat.pow_lt_pow_right hp.one_lt (Nat.sub_lt hk_gt1 Nat.one_pos)
        omega
      exact hm_in_S this
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
          -- For the first inequality, we prove by induction on S that
          -- (S.lcm id).factorization q ≤ S.sup (d.factorization q)
          -- We use a helper function since direct induction loses context
          suffices h : ∀ (T : Finset ℕ), (∀ d ∈ T, d ≠ 0) →
              (T.lcm id).factorization q ≤ T.sup (fun d => d.factorization q) by
            have hS_ne_zero : ∀ d ∈ S, d ≠ 0 := fun d hd =>
              (Nat.pos_of_dvd_of_pos (hS_sub d hd) hm).ne'
            exact lt_of_le_of_lt (h S hS_ne_zero) hsup_lt
          intro T hT_ne_zero
          induction T using Finset.induction with
          | empty =>
            simp only [Finset.lcm_empty, Nat.factorization_one, Finsupp.coe_zero, Pi.zero_apply,
              Finset.sup_empty, bot_eq_zero, le_refl]
          | @insert a s' ha IH_inner =>
            simp only [Finset.lcm_insert, Finset.sup_insert]
            by_cases hs'_empty : s' = ∅
            · simp [hs'_empty]
            · have hs'_ne_zero : s'.lcm id ≠ 0 := by
                rw [ne_eq, Finset.lcm_eq_zero_iff]
                push_neg
                intro d hd
                simp only [id_eq]
                exact hT_ne_zero d (Finset.mem_insert_of_mem hd)
              have ha_ne_zero : a ≠ 0 := hT_ne_zero a (Finset.mem_insert_self a s')
              simp only [id_eq, lcm_eq_nat_lcm]
              rw [Nat.factorization_lcm ha_ne_zero hs'_ne_zero]
              simp only [Finsupp.sup_apply, sup_le_iff]
              constructor
              · exact le_sup_left
              · have hIH := IH_inner (fun d hd => hT_ne_zero d (Finset.mem_insert_of_mem hd))
                exact le_trans hIH le_sup_right
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
                  have hq_prime := Nat.prime_of_mem_primeFactors
                    (Nat.support_factorization m ▸ hq_supp)
                  have hk_pos : 0 < m.factorization q :=
                    Finsupp.mem_support_iff.mp hq_supp |> Nat.pos_of_ne_zero
                  have hqk_nontrivial : ¬(q = 2 ∧ m.factorization q = 1) :=
                    (Finset.mem_filter.mp hq_NT).2
                  -- φ(p^k) ≥ 2 when (p,k) ≠ (2,1) and k > 0
                  rw [Nat.totient_prime_pow hq_prime hk_pos]
                  by_cases h2 : q = 2
                  · subst h2
                    have hk_ge2 : 2 ≤ m.factorization 2 := by
                      by_contra hlt; push_neg at hlt
                      have hk1 : m.factorization 2 = 1 := by omega
                      exact hqk_nontrivial ⟨rfl, hk1⟩
                    calc 2 ^ (m.factorization 2 - 1) * (2 - 1)
                        = 2 ^ (m.factorization 2 - 1) := by ring
                      _ ≥ 2 ^ 1 := Nat.pow_le_pow_right (by omega) (by omega)
                      _ = 2 := by ring
                  · have hp3 : 3 ≤ q := Nat.lt_of_le_of_ne hq_prime.two_le (Ne.symm h2)
                    calc q ^ (m.factorization q - 1) * (q - 1)
                        ≥ 1 * (q - 1) := Nat.mul_le_mul_right _ (Nat.one_le_pow _ _ hq_prime.pos)
                      _ = q - 1 := one_mul _
                      _ ≥ 2 := by omega
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
                  have h_prod_dvd : (∏ q ∈ fiber, q ^ m.factorization q) ∣ d := by
                    -- Product of coprime divisors divides d
                    -- Use suffices to abstract over the finset and its properties
                    suffices h : ∀ (T : Finset ℕ),
                        (∀ q ∈ T, q ^ m.factorization q ∣ d) →
                        (∀ q₁ ∈ T, ∀ q₂ ∈ T, q₁ ≠ q₂ →
                          (q₁ ^ m.factorization q₁).Coprime (q₂ ^ m.factorization q₂)) →
                        (∏ q ∈ T, q ^ m.factorization q) ∣ d by
                      exact h fiber h_fiber_dvd h_coprime
                    intro T hT_dvd hT_coprime
                    induction T using Finset.induction with
                    | empty => simp
                    | @insert q s' hq_notin IH =>
                      rw [Finset.prod_insert hq_notin]
                      have hq_dvd : q ^ m.factorization q ∣ d :=
                        hT_dvd q (Finset.mem_insert_self q s')
                      have hs'_dvd : (∏ r ∈ s', r ^ m.factorization r) ∣ d := by
                        apply IH
                        · intro r hr; exact hT_dvd r (Finset.mem_insert_of_mem hr)
                        · intro q₁ hq₁ q₂ hq₂ hne
                          exact hT_coprime q₁ (Finset.mem_insert_of_mem hq₁) q₂
                            (Finset.mem_insert_of_mem hq₂) hne
                      -- q^k and ∏ r^{k_r} are coprime
                      have h_cop : (q ^ m.factorization q).Coprime
                          (∏ r ∈ s', r ^ m.factorization r) := by
                        apply Nat.Coprime.prod_right
                        intro r hr
                        have hne : q ≠ r := fun heq => hq_notin (heq ▸ hr)
                        exact hT_coprime q (Finset.mem_insert_self q s') r
                          (Finset.mem_insert_of_mem hr) hne
                      exact h_cop.mul_dvd_of_dvd_of_dvd hq_dvd hs'_dvd
                  -- φ(d) ≥ φ(∏_{q∈fiber} q^{ord_q(m)})
                  -- First show: φ(∏ q^k) = ∏ φ(q^k) by induction using coprimality
                  have h_totient_prod : Nat.totient (∏ q ∈ fiber, q ^ m.factorization q) =
                      ∏ q ∈ fiber, Nat.totient (q ^ m.factorization q) := by
                    suffices h : ∀ (T : Finset ℕ),
                        (∀ q₁ ∈ T, ∀ q₂ ∈ T, q₁ ≠ q₂ →
                          (q₁ ^ m.factorization q₁).Coprime (q₂ ^ m.factorization q₂)) →
                        Nat.totient (∏ q ∈ T, q ^ m.factorization q) =
                          ∏ q ∈ T, Nat.totient (q ^ m.factorization q) by
                      exact h fiber h_coprime
                    intro T hT_coprime
                    induction T using Finset.induction with
                    | empty => simp
                    | @insert q s' hq_notin IH =>
                      rw [Finset.prod_insert hq_notin, Finset.prod_insert hq_notin]
                      have h_cop_q_s : (q ^ m.factorization q).Coprime
                          (∏ r ∈ s', r ^ m.factorization r) := by
                        apply Nat.Coprime.prod_right
                        intro r hr
                        have hne : q ≠ r := fun heq => hq_notin (heq ▸ hr)
                        exact hT_coprime q (Finset.mem_insert_self q s') r
                          (Finset.mem_insert_of_mem hr) hne
                      rw [Nat.totient_mul h_cop_q_s]
                      congr 1
                      apply IH
                      intro q₁ hq₁ q₂ hq₂ hne
                      exact hT_coprime q₁ (Finset.mem_insert_of_mem hq₁) q₂
                        (Finset.mem_insert_of_mem hq₂) hne
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
                      ∏ q ∈ fiber, Nat.totient (q ^ m.factorization q) := by
                    -- Use suffices to abstract the ge2 property
                    suffices h : ∀ (T : Finset ℕ),
                        (∀ q ∈ T, 2 ≤ Nat.totient (q ^ m.factorization q)) →
                        ∑ q ∈ T, Nat.totient (q ^ m.factorization q) ≤
                          ∏ q ∈ T, Nat.totient (q ^ m.factorization q) by
                      exact h fiber h_fiber_ge2
                    intro T hT_ge2
                    induction T using Finset.induction with
                    | empty => simp
                    | @insert a s' ha IH =>
                      rw [Finset.sum_insert ha, Finset.prod_insert ha]
                      have h2_a : 2 ≤ Nat.totient (a ^ m.factorization a) :=
                        hT_ge2 a (Finset.mem_insert_self a s')
                      by_cases hs_empty : s' = ∅
                      · simp [hs_empty]
                      · have hs_nonempty : s'.Nonempty := Finset.nonempty_of_ne_empty hs_empty
                        have hs'_ge2 : ∀ q ∈ s', 2 ≤ Nat.totient (q ^ m.factorization q) :=
                          fun q hq => hT_ge2 q (Finset.mem_insert_of_mem hq)
                        have h2_prod : 2 ≤ ∏ q ∈ s', Nat.totient (q ^ m.factorization q) := by
                          obtain ⟨b, hb⟩ := hs_nonempty
                          have h1 : ∀ q ∈ s', 1 ≤ Nat.totient (q ^ m.factorization q) :=
                            fun q hq => Nat.one_le_of_lt (hs'_ge2 q hq)
                          calc ∏ q ∈ s', Nat.totient (q ^ m.factorization q)
                              ≥ Nat.totient (b ^ m.factorization b) :=
                                Finset.single_le_prod' h1 hb
                            _ ≥ 2 := hs'_ge2 b hb
                        have IH' := IH hs'_ge2
                        calc Nat.totient (a ^ m.factorization a) +
                              ∑ q ∈ s', Nat.totient (q ^ m.factorization q)
                            ≤ Nat.totient (a ^ m.factorization a) +
                              ∏ q ∈ s', Nat.totient (q ^ m.factorization q) := by omega
                          _ ≤ Nat.totient (a ^ m.factorization a) *
                              ∏ q ∈ s', Nat.totient (q ^ m.factorization q) :=
                              Nat.add_le_mul h2_a h2_prod
                  exact le_trans h_prod_ge_sum h_totient_ge_prod


end Crystallographic
