/-
Copyright (c) 2026 Eric Vergo. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Eric Vergo
-/
import WallpaperGroups.Crystallographic.General.MainTheorem

/-!
# The 2D Crystallographic Restriction Theorem

This file specializes the general crystallographic restriction theorem to dimension 2,
proving that for 2x2 integer matrices, the achievable orders are exactly {1, 2, 3, 4, 6}.

## Main results

* `integerMatrixOrders_two` - The achievable orders for 2x2 integer matrices are {1, 2, 3, 4, 6}.
* `crystallographic_restriction_2D` - A rotation order m is achievable iff m in {1, 2, 3, 4, 6}.
* `rotation_matrix_*` - Explicit constructions of integer rotation matrices.

## Proof Strategy

### Showing {1,2,3,4,6} in integerMatrixOrders 2

Construct explicit 2x2 integer matrices for each order:
- Order 1: Identity matrix I
- Order 2: -I (rotation by 180 degrees)
- Order 3: Rotation by 120 degrees in hexagonal basis: !![0, -1; 1, -1]
- Order 4: Rotation by 90 degrees: !![0, -1; 1, 0]
- Order 6: Rotation by 60 degrees in hexagonal basis: !![1, -1; 1, 0]

### Showing integerMatrixOrders 2 subset {1,2,3,4,6}

Use the psi function: psi(m) <= 2 implies m in {1,2,3,4,6}.
- psi(5) = 4 > 2
- psi(7) = 6 > 2
- psi(8) = 4 > 2
- etc.

## References

* Sasse, R. (2020). "Crystallographic Groups"
-/

namespace WallpaperGroups.Crystallographic

open Matrix Polynomial

-- Note: Rotation matrix definitions and order proofs are in RotationMatrices.lean,
-- imported via MainTheorem.lean. This includes:
-- - rotationMatrix1, rotationMatrix2, rotationMatrix3, rotationMatrix4, rotationMatrix6
-- - orderOf_rotationMatrix*, three/four/six_mem_integerMatrixOrders_two

/-! ## Lower bounds on psi for large m -/

/-- psi(11) = 10 -/
lemma psi_eleven : Crystallographic.psi 11 = 10 := by
  have hp : Nat.Prime 11 := by decide
  have h := Crystallographic.psi_prime_pow 11 1 hp (by norm_num : 0 < 1)
  simp only [pow_one] at h
  rw [h]
  simp only [show (11 : ℕ) ≠ 2 by decide, false_and, ite_false]
  rw [Nat.totient_prime hp]

/-- psi(13) = 12 -/
lemma psi_thirteen : Crystallographic.psi 13 = 12 := by
  have hp : Nat.Prime 13 := by decide
  have h := Crystallographic.psi_prime_pow 13 1 hp (by norm_num : 0 < 1)
  simp only [pow_one] at h
  rw [h]
  simp only [show (13 : ℕ) ≠ 2 by decide, false_and, ite_false]
  rw [Nat.totient_prime hp]

/-- psi(14) = psi(2) + psi(7) = 0 + 6 = 6 -/
lemma psi_fourteen : Crystallographic.psi 14 = 6 := by
  have h14 : (14 : ℕ) = 2 * 7 := by norm_num
  rw [h14, Crystallographic.psi_coprime_add 2 7 (by norm_num) (by norm_num) (by decide)]
  simp [Crystallographic.psi_seven]

/-- psi(15) = psi(3) + psi(5) = 2 + 4 = 6 -/
lemma psi_fifteen : Crystallographic.psi 15 = 6 := by
  have h15 : (15 : ℕ) = 3 * 5 := by norm_num
  rw [h15, Crystallographic.psi_coprime_add 3 5 (by norm_num) (by norm_num) (by decide)]
  simp [Crystallographic.psi_five]

/-- psi(16) = psi(2^4) = phi(2^4) = 8 -/
lemma psi_sixteen : Crystallographic.psi 16 = 8 := by
  have h := Crystallographic.psi_prime_pow 2 4 Nat.prime_two (by norm_num : 0 < 4)
  simp only [show (16 : ℕ) = 2 ^ 4 by norm_num] at h ⊢
  rw [h]
  simp only [show (4 : ℕ) ≠ 1 by decide, and_false, ite_false]
  rw [Nat.totient_prime_pow Nat.prime_two (by norm_num : 0 < 4)]
  norm_num

/-- psi(17) = 16 -/
lemma psi_seventeen : Crystallographic.psi 17 = 16 := by
  have hp : Nat.Prime 17 := by decide
  have h := Crystallographic.psi_prime_pow 17 1 hp (by norm_num : 0 < 1)
  simp only [pow_one] at h
  rw [h]
  simp only [show (17 : ℕ) ≠ 2 by decide, false_and, ite_false]
  rw [Nat.totient_prime hp]

/-- psi(18) = psi(2) + psi(9) = 0 + 6 = 6 -/
lemma psi_eighteen : Crystallographic.psi 18 = 6 := by
  have h18 : (18 : ℕ) = 2 * 9 := by norm_num
  rw [h18, Crystallographic.psi_coprime_add 2 9 (by norm_num) (by norm_num) (by decide)]
  simp [Crystallographic.psi_nine]

/-- psi(19) = 18 -/
lemma psi_nineteen : Crystallographic.psi 19 = 18 := by
  have hp : Nat.Prime 19 := by decide
  have h := Crystallographic.psi_prime_pow 19 1 hp (by norm_num : 0 < 1)
  simp only [pow_one] at h
  rw [h]
  simp only [show (19 : ℕ) ≠ 2 by decide, false_and, ite_false]
  rw [Nat.totient_prime hp]

/-- psi(20) = psi(4) + psi(5) = 2 + 4 = 6 -/
lemma psi_twenty : Crystallographic.psi 20 = 6 := by
  have h20 : (20 : ℕ) = 4 * 5 := by norm_num
  rw [h20, Crystallographic.psi_coprime_add 4 5 (by norm_num) (by norm_num) (by decide)]
  simp [Crystallographic.psi_five]

/-- psi(21) = psi(3) + psi(7) = 2 + 6 = 8 -/
lemma psi_twentyone : Crystallographic.psi 21 = 8 := by
  have h21 : (21 : ℕ) = 3 * 7 := by norm_num
  rw [h21, Crystallographic.psi_coprime_add 3 7 (by norm_num) (by norm_num) (by decide)]
  simp [Crystallographic.psi_seven]

/-- psi(22) = psi(2) + psi(11) = 0 + 10 = 10 -/
lemma psi_twentytwo : Crystallographic.psi 22 = 10 := by
  have h22 : (22 : ℕ) = 2 * 11 := by norm_num
  rw [h22, Crystallographic.psi_coprime_add 2 11 (by norm_num) (by norm_num) (by decide)]
  simp [psi_eleven]

/-- psi(23) = 22 -/
lemma psi_twentythree : Crystallographic.psi 23 = 22 := by
  have hp : Nat.Prime 23 := by decide
  have h := Crystallographic.psi_prime_pow 23 1 hp (by norm_num : 0 < 1)
  simp only [pow_one] at h
  rw [h]
  simp only [show (23 : ℕ) ≠ 2 by decide, false_and, ite_false]
  rw [Nat.totient_prime hp]

/-- psi(24) = psi(8) + psi(3) = 4 + 2 = 6 -/
lemma psi_twentyfour : Crystallographic.psi 24 = 6 := by
  have h24 : (24 : ℕ) = 8 * 3 := by norm_num
  rw [h24, Crystallographic.psi_coprime_add 8 3 (by norm_num) (by norm_num) (by decide)]
  simp [Crystallographic.psi_eight]

/-- psi(25) = psi(5^2) = phi(25) = 20 -/
lemma psi_twentyfive : Crystallographic.psi 25 = 20 := by
  have hp : Nat.Prime 5 := by decide
  have h := Crystallographic.psi_prime_pow 5 2 hp (by norm_num : 0 < 2)
  simp only [show (25 : ℕ) = 5 ^ 2 by norm_num] at h ⊢
  rw [h]
  simp only [show (5 : ℕ) ≠ 2 by decide, false_and, ite_false]
  rw [Nat.totient_prime_pow hp (by norm_num : 0 < 2)]
  norm_num

/-- psi(26) = psi(2) + psi(13) = 0 + 12 = 12 -/
lemma psi_twentysix : Crystallographic.psi 26 = 12 := by
  have h26 : (26 : ℕ) = 2 * 13 := by norm_num
  rw [h26, Crystallographic.psi_coprime_add 2 13 (by norm_num) (by norm_num) (by decide)]
  simp [psi_thirteen]

/-- psi(27) = psi(3^3) = phi(27) = 18 -/
lemma psi_twentyseven : Crystallographic.psi 27 = 18 := by
  have h := Crystallographic.psi_prime_pow 3 3 Nat.prime_three (by norm_num : 0 < 3)
  simp only [show (27 : ℕ) = 3 ^ 3 by norm_num] at h ⊢
  rw [h]
  simp only [show (3 : ℕ) ≠ 2 by decide, false_and, ite_false]
  rw [Nat.totient_prime_pow Nat.prime_three (by norm_num : 0 < 3)]
  norm_num

/-- psi(32) = psi(2^5) = phi(32) = 16 -/
lemma psi_thirtytwo : Crystallographic.psi 32 = 16 := by
  have h := Crystallographic.psi_prime_pow 2 5 Nat.prime_two (by norm_num : 0 < 5)
  simp only [show (32 : ℕ) = 2 ^ 5 by norm_num] at h ⊢
  rw [h]
  simp only [show (5 : ℕ) ≠ 1 by decide, and_false, ite_false]
  rw [Nat.totient_prime_pow Nat.prime_two (by norm_num : 0 < 5)]
  norm_num

/-- psi(36) = psi(4) + psi(9) = 2 + 6 = 8 -/
lemma psi_thirtysix : Crystallographic.psi 36 = 8 := by
  have h36 : (36 : ℕ) = 4 * 9 := by norm_num
  rw [h36, Crystallographic.psi_coprime_add 4 9 (by norm_num) (by norm_num) (by decide)]
  simp [Crystallographic.psi_nine]

/-- psi(48) = psi(16) + psi(3) = 8 + 2 = 10 -/
lemma psi_fortyeight : Crystallographic.psi 48 = 10 := by
  have h48 : (48 : ℕ) = 16 * 3 := by norm_num
  rw [h48, Crystallographic.psi_coprime_add 16 3 (by norm_num) (by norm_num) (by decide)]
  simp [psi_sixteen]

/-- For any prime p >= 5, psi(p) = phi(p) = p - 1 >= 4 -/
lemma psi_prime_ge_five {p : ℕ} (hp : Nat.Prime p) (hp5 : 5 ≤ p) :
    4 ≤ Crystallographic.psi p := by
  have h := Crystallographic.psi_prime_pow p 1 hp (by norm_num : 0 < 1)
  simp only [pow_one] at h
  rw [h]
  have hp2 : p ≠ 2 := by
    intro h
    subst h
    omega
  simp only [hp2, false_and, ite_false]
  rw [Nat.totient_prime hp]
  omega

/-- For m in a given finite range, psi(m) > 2 -/
lemma psi_gt_two_of_mem_range : ∀ m, 7 ≤ m → m ≤ 24 → 2 < Crystallographic.psi m := by
  intro m hm_low hm_high
  interval_cases m
  · simp [Crystallographic.psi_seven]
  · simp [Crystallographic.psi_eight]
  · simp [Crystallographic.psi_nine]
  · simp [Crystallographic.psi_ten]
  · simp [psi_eleven]
  · simp [Crystallographic.psi_twelve]
  · simp [psi_thirteen]
  · simp [psi_fourteen]
  · simp [psi_fifteen]
  · simp [psi_sixteen]
  · simp [psi_seventeen]
  · simp [psi_eighteen]
  · simp [psi_nineteen]
  · simp [psi_twenty]
  · simp [psi_twentyone]
  · simp [psi_twentytwo]
  · simp [psi_twentythree]
  · simp [psi_twentyfour]

/-- m = 2^a * 3^b exactly when only prime factors are 2 and 3 -/
lemma eq_pow_two_mul_pow_three_of_only_23 {m : ℕ} (hm : 0 < m)
    (h_only_23 : ∀ p, p ∈ m.factorization.support → p = 2 ∨ p = 3) :
    m = 2 ^ (m.factorization 2) * 3 ^ (m.factorization 3) := by
  have hprod := Nat.factorization_prod_pow_eq_self (Nat.ne_of_gt hm)
  have hsub : m.factorization.support ⊆ {2, 3} := by
    intro p hp
    rcases h_only_23 p hp with rfl | rfl <;> simp
  by_cases h2 : 2 ∈ m.factorization.support <;> by_cases h3 : 3 ∈ m.factorization.support
  · -- Both 2 and 3 in support
    have heq' : m.factorization.support = {2, 3} := by
      apply Finset.Subset.antisymm hsub
      intro p hp
      simp only [Finset.mem_insert, Finset.mem_singleton] at hp
      rcases hp with rfl | rfl <;> assumption
    calc m = m.factorization.prod (· ^ ·) := hprod.symm
      _ = ∏ p ∈ m.factorization.support, p ^ m.factorization p := Finsupp.prod.eq_1 _ _
      _ = ∏ p ∈ ({2, 3} : Finset ℕ), p ^ m.factorization p := by rw [heq']
      _ = 2 ^ m.factorization 2 * 3 ^ m.factorization 3 := by
          rw [Finset.prod_insert (by simp : (2 : ℕ) ∉ ({3} : Finset ℕ)),
            Finset.prod_singleton]
  · -- Only 2 in support
    have h3_zero : m.factorization 3 = 0 := Finsupp.notMem_support_iff.mp h3
    have heq' : m.factorization.support = {2} := by
      apply Finset.Subset.antisymm
      · intro p hp
        rcases h_only_23 p hp with rfl | rfl
        · simp
        · exact absurd hp h3
      · intro p hp
        simp only [Finset.mem_singleton] at hp
        rw [hp]
        exact h2
    calc m = m.factorization.prod (· ^ ·) := hprod.symm
      _ = ∏ p ∈ m.factorization.support, p ^ m.factorization p := Finsupp.prod.eq_1 _ _
      _ = ∏ p ∈ ({2} : Finset ℕ), p ^ m.factorization p := by rw [heq']
      _ = 2 ^ m.factorization 2 := by rw [Finset.prod_singleton]
      _ = 2 ^ m.factorization 2 * 3 ^ m.factorization 3 := by simp [h3_zero]
  · -- Only 3 in support
    have h2_zero : m.factorization 2 = 0 := Finsupp.notMem_support_iff.mp h2
    have heq' : m.factorization.support = {3} := by
      apply Finset.Subset.antisymm
      · intro p hp
        rcases h_only_23 p hp with rfl | rfl
        · exact absurd hp h2
        · simp
      · intro p hp
        simp only [Finset.mem_singleton] at hp
        rw [hp]
        exact h3
    calc m = m.factorization.prod (· ^ ·) := hprod.symm
      _ = ∏ p ∈ m.factorization.support, p ^ m.factorization p := Finsupp.prod.eq_1 _ _
      _ = ∏ p ∈ ({3} : Finset ℕ), p ^ m.factorization p := by rw [heq']
      _ = 3 ^ m.factorization 3 := by rw [Finset.prod_singleton]
      _ = 2 ^ m.factorization 2 * 3 ^ m.factorization 3 := by simp [h2_zero]
  · -- Neither in support (m = 1)
    have h2_zero : m.factorization 2 = 0 := Finsupp.notMem_support_iff.mp h2
    have h3_zero : m.factorization 3 = 0 := Finsupp.notMem_support_iff.mp h3
    have hsup : m.factorization.support = ∅ := by
      apply Finset.eq_empty_of_forall_notMem
      intro p hp
      rcases h_only_23 p hp with rfl | rfl
      · exact h2 hp
      · exact h3 hp
    calc m = m.factorization.prod (· ^ ·) := hprod.symm
      _ = ∏ p ∈ m.factorization.support, p ^ m.factorization p := Finsupp.prod.eq_1 _ _
      _ = ∏ p ∈ (∅ : Finset ℕ), p ^ m.factorization p := by rw [hsup]
      _ = 1 := by rw [Finset.prod_empty]
      _ = 2 ^ m.factorization 2 * 3 ^ m.factorization 3 := by simp [h2_zero, h3_zero]

/-- For m >= 7, psi(m) > 2. This is because:
    - Pure powers of 2: 2^k for k >= 3 gives psi = phi(2^k) = 2^{k-1} >= 4
    - Has odd prime factor p >= 5: psi >= phi(p) = p - 1 >= 4
    - m = 2^a * 3 with a >= 2: psi >= phi(2^2) + phi(3) = 2 + 2 = 4
    - m = 2 * 3^b with b >= 2: psi >= phi(3^2) = 6
    - m = 3 * (something odd >= 3): at minimum 3 * 3 = 9 gives psi = 6 -/
lemma psi_gt_two_of_ge_seven {m : ℕ} (hm : 7 ≤ m) : 2 < Crystallographic.psi m := by
  -- The key observation: psi(m) <= 2 requires:
  -- - Only prime factors in {2, 3}
  -- - Power of 2 is 0, 1, or 2 (since 2^3 gives psi contribution phi(8) = 4)
  -- - Power of 3 is 0 or 1 (since 3^2 gives psi contribution phi(9) = 6)
  -- - Cannot have both 2^2 and 3 (since psi(12) = 4)
  -- This constrains m to {1, 2, 3, 4, 6}, all < 7
  -- So for m >= 7, we must have psi(m) > 2
  --
  -- For now, use explicit enumeration for small cases and general bound for large
  rcases Nat.lt_or_ge m 25 with hm_lt | hm_ge
  · -- m in [7, 24], use explicit computation
    exact psi_gt_two_of_mem_range m hm (by omega)
  · -- m >= 25, need general argument
    have hm_pos : 0 < m := by omega
    -- Case split: does m have a prime factor >= 5?
    by_cases h_has_large_prime : ∃ p ∈ m.factorization.support, 5 ≤ p
    · -- Case 1: m has a prime factor p >= 5
      obtain ⟨p, hp_mem, hp5⟩ := h_has_large_prime
      have hp_prime : p.Prime := by
        rw [Nat.support_factorization] at hp_mem
        exact Nat.prime_of_mem_primeFactors hp_mem
      have hk_pos : 0 < m.factorization p := Finsupp.mem_support_iff.mp hp_mem |> Nat.pos_of_ne_zero
      calc Crystallographic.psi m ≥ Crystallographic.psiPrimePow p (m.factorization p) :=
             Crystallographic.psi_ge_psiPrimePow_of_mem_support hm_pos hp_mem
        _ ≥ 4 := Crystallographic.psiPrimePow_ge_four_of_prime_ge_five hp_prime hp5 hk_pos
        _ > 2 := by norm_num
    · -- Case 2: all prime factors are in {2, 3}
      push_neg at h_has_large_prime
      have h_only_23 : ∀ p, p ∈ m.factorization.support → p = 2 ∨ p = 3 := by
        intro p hp
        have hp_prime : p.Prime := by
          rw [Nat.support_factorization] at hp
          exact Nat.prime_of_mem_primeFactors hp
        have hp_lt5 := h_has_large_prime p hp
        have hp_ge2 := hp_prime.two_le
        interval_cases p
        · left; rfl
        · right; rfl
        · exact absurd hp_prime (by decide : ¬Nat.Prime 4)
      -- m = 2^a * 3^b with a = m.factorization 2, b = m.factorization 3
      set a := m.factorization 2 with ha
      set b := m.factorization 3 with hb
      have heq := eq_pow_two_mul_pow_three_of_only_23 hm_pos h_only_23
      -- Case 2a: a >= 3 (power of 2 is at least 8)
      by_cases ha3 : 3 ≤ a
      · have h2_mem : 2 ∈ m.factorization.support := by
          rw [Finsupp.mem_support_iff]
          omega
        calc Crystallographic.psi m ≥ Crystallographic.psiPrimePow 2 a :=
               Crystallographic.psi_ge_psiPrimePow_of_mem_support hm_pos h2_mem
          _ ≥ 4 := Crystallographic.psiPrimePow_ge_four_of_two_pow_ge_three ha3
          _ > 2 := by norm_num
      · -- a <= 2
        -- Case 2b: b >= 2 (power of 3 is at least 9)
        by_cases hb2 : 2 ≤ b
        · have h3_mem : 3 ∈ m.factorization.support := by
            rw [Finsupp.mem_support_iff]
            omega
          calc Crystallographic.psi m ≥ Crystallographic.psiPrimePow 3 b :=
                 Crystallographic.psi_ge_psiPrimePow_of_mem_support hm_pos h3_mem
            _ ≥ 6 := Crystallographic.psiPrimePow_ge_six_of_three_pow_ge_two hb2
            _ > 2 := by norm_num
        · -- a <= 2 and b <= 1
          -- Then m = 2^a * 3^b <= 2^2 * 3^1 = 12 < 25
          push_neg at ha3 hb2
          have ha2 : a ≤ 2 := by omega
          have hb1 : b ≤ 1 := by omega
          have hm_le : m ≤ 12 := by
            rw [heq]
            have h1 : 2^a ≤ 2^2 := Nat.pow_le_pow_right (by omega) ha2
            have h2 : 3^b ≤ 3^1 := Nat.pow_le_pow_right (by omega) hb1
            calc 2^a * 3^b ≤ 2^2 * 3^1 := Nat.mul_le_mul h1 h2
              _ = 12 := by norm_num
          omega

/-! ## Main 2D Theorems -/

/-- Orders 1, 2, 3, 4, 6 are all achievable by 2x2 integer matrices -/
theorem crystallographic_orders_achievable :
    ({1, 2, 3, 4, 6} : Set ℕ) ⊆ integerMatrixOrders 2 := by
  intro m hm
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl
  · exact one_mem_integerMatrixOrders 2
  · exact two_mem_integerMatrixOrders 2
  · exact three_mem_integerMatrixOrders_two
  · exact four_mem_integerMatrixOrders_two
  · exact six_mem_integerMatrixOrders_two

/-- Any order achievable by a 2x2 integer matrix must be in {1, 2, 3, 4, 6} -/
theorem integerMatrixOrders_two_subset_crystallographic :
    ∀ m, m ∈ integerMatrixOrders 2 → 0 < m → m ∈ ({1, 2, 3, 4, 6} : Set ℕ) := by
  intro m hm_ord hm_pos
  -- Use the crystallographic restriction theorem
  have hpsi := psi_le_of_mem_integerMatrixOrders 2 m hm_pos hm_ord
  -- psi(m) <= 2 means m in {1, 2, 3, 4, 6}
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  by_contra h
  push_neg at h
  obtain ⟨h1, h2, h3, h4, h6⟩ := h
  -- m not in {1, 2, 3, 4, 6}, so m = 0 or m >= 5 with m != 6
  -- Use that psi(m) > 2 for m not in {1, 2, 3, 4, 6}
  -- For m = 5: psi(5) = 4 > 2
  -- For m >= 7: psi(m) >= psi(7) = 6 > 2
  -- We'll prove this by showing a contradiction for each case
  rcases Nat.lt_or_ge m 7 with hm_lt7 | hm_ge7
  · -- m < 7, so m in {0, 1, 2, 3, 4, 5, 6}
    -- We've excluded 1, 2, 3, 4, 6, and m > 0, so m = 5
    interval_cases m <;> try omega
    · simp [Crystallographic.psi_five] at hpsi
  · -- m >= 7, need to show psi(m) > 2
    have hpsi_gt := psi_gt_two_of_ge_seven hm_ge7
    omega

/-- The achievable orders for 2x2 integer matrices are exactly {1, 2, 3, 4, 6} -/
theorem integerMatrixOrders_two :
    integerMatrixOrders 2 ∩ {m | 0 < m} = {1, 2, 3, 4, 6} := by
  ext m
  simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · intro ⟨hm_ord, hm_pos⟩
    exact integerMatrixOrders_two_subset_crystallographic m hm_ord hm_pos
  · intro hm
    rcases hm with rfl | rfl | rfl | rfl | rfl
    all_goals constructor
    · exact one_mem_integerMatrixOrders 2
    · norm_num
    · exact two_mem_integerMatrixOrders 2
    · norm_num
    · exact three_mem_integerMatrixOrders_two
    · norm_num
    · exact four_mem_integerMatrixOrders_two
    · norm_num
    · exact six_mem_integerMatrixOrders_two
    · norm_num

/-- 2D crystallographic restriction: lattice-preserving rotations have order in {1,2,3,4,6} -/
theorem crystallographic_restriction_2D (m : ℕ) (hm : 0 < m) :
    m ∈ integerMatrixOrders 2 ↔ m ∈ ({1, 2, 3, 4, 6} : Set ℕ) := by
  constructor
  · exact fun h => integerMatrixOrders_two_subset_crystallographic m h hm
  · intro h
    exact crystallographic_orders_achievable h

end WallpaperGroups.Crystallographic
