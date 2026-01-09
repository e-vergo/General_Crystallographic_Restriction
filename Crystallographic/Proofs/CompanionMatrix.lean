/-
Copyright (c) 2026 Eric Vergo. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Eric Vergo
-/
import Mathlib.Data.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.LinearAlgebra.Matrix.Charpoly.Minpoly
import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.GroupTheory.OrderOfElement
import Crystallographic.Definitions.IntegerMatrixOrder
import Crystallographic.Definitions.CompanionMatrix

/-!
# Companion Matrix Proofs

This file proves the key properties of companion matrices,
particularly for cyclotomic polynomials which are essential for the crystallographic
restriction theorem.

## Main results

* `companion_charpoly` - The characteristic polynomial of companion(p) equals p
* `companion_aeval_eq_zero` - The polynomial p annihilates its companion matrix
* `companion_pow_eq_one_of_cyclotomic` - companion(Φ_m)^m = 1
* `companion_orderOf_cyclotomic` - orderOf(companion(Φ_m)) = m for m ≥ 1

## References

* Standard linear algebra texts on companion matrices
-/

namespace Crystallographic

open Matrix Polynomial

variable {R : Type*} [CommRing R]

/-! ### Basic properties -/

/-- The subdiagonal entries of the companion matrix are 1. -/
lemma companion_subdiag (p : R[X]) (hp : p.Monic) (hn : 0 < p.natDegree)
    (i : Fin p.natDegree) (hi : i.val + 1 < p.natDegree) :
    companion p hp hn ⟨i.val + 1, hi⟩ i = 1 := by
  simp only [companion, Matrix.of_apply, if_true]

/-- The last column of the companion matrix contains -coeff. -/
lemma companion_last_col (p : R[X]) (hp : p.Monic) (hn : 0 < p.natDegree)
    (i : Fin p.natDegree) :
    companion p hp hn i ⟨p.natDegree - 1, Nat.sub_lt hn Nat.one_pos⟩ = -p.coeff i.val := by
  simp only [companion, Matrix.of_apply]
  have hj : (p.natDegree - 1) + 1 = p.natDegree := Nat.sub_add_cancel hn
  simp only [hj, ↓reduceIte]
  split_ifs with h
  · omega
  · rfl

/-! ### Characteristic polynomial -/

/-- Auxiliary lemma for companion_charpoly: expresses the charmatrix structure. -/
private lemma companion_charmatrix (p : R[X]) (hp : p.Monic) (hn : 0 < p.natDegree)
    (i j : Fin p.natDegree) :
    charmatrix (companion p hp hn) i j =
      if i = j then
        if i.val + 1 = p.natDegree then X + Polynomial.C (p.coeff i.val) else X
      else if j.val + 1 = i.val then -1
      else if j.val + 1 = p.natDegree then Polynomial.C (p.coeff i.val)
      else 0 := by
  by_cases hij : i = j
  · -- Diagonal case: charmatrix i i = X - C(companion i i)
    subst hij
    simp only [↓reduceIte]  -- Simplify "if i = i then ... else ..." and "if True then ..."
    rw [charmatrix_apply_eq, companion, Matrix.of_apply]
    -- Now we have: X - C (if i.val + 1 = i.val then 1 else if i.val + 1 = n then -p.coeff i else 0)
    have h_not_eq : ¬(i.val + 1 = i.val) := by omega
    simp only [h_not_eq, ↓reduceIte]
    -- Now: X - C (if i.val + 1 = n then -p.coeff i else 0)
    -- = if i.val + 1 = n then X + C(...) else X
    by_cases h : i.val + 1 = p.natDegree
    · simp only [h, ↓reduceIte, map_neg, sub_neg_eq_add]
    · simp only [h, ↓reduceIte, map_zero, sub_zero]
  · -- Off-diagonal case: charmatrix i j = -C(companion i j)
    simp only [hij, ↓reduceIte]  -- Simplify "if i = j then ..."
    rw [charmatrix_apply_ne _ _ _ hij, companion, Matrix.of_apply]
    by_cases h1 : j.val + 1 = i.val
    · -- Subdiagonal: companion i j = 1, so charmatrix = -C(1) = -1
      simp only [h1, ↓reduceIte, map_one]
    · simp only [h1, ↓reduceIte]
      by_cases h2 : j.val + 1 = p.natDegree
      · -- Last column: companion i j = -p.coeff i, charmatrix = -C(-p.coeff i) = C(p.coeff i)
        simp only [h2, ↓reduceIte, map_neg, neg_neg]
      · -- Neither: companion i j = 0, charmatrix = -C(0) = 0
        simp only [h2, ↓reduceIte, map_zero, neg_zero]

/-- The characteristic polynomial of the companion matrix equals the original polynomial.

This is the fundamental property of companion matrices: they are constructed precisely
so that their characteristic polynomial matches the given monic polynomial.

The proof proceeds by strong induction on the degree n. For degree 1, direct computation
shows both sides equal X + C(a₀). For degree n+1, Laplace expansion along the first
column gives a recurrence matching the polynomial structure.
-/
theorem companion_charpoly (p : R[X]) (hp : p.Monic) (hn : 0 < p.natDegree) :
    (companion p hp hn).charpoly = p := by
  -- The proof is by induction on the degree of p.
  -- We use the companion_charmatrix lemma to get the explicit form of charmatrix.
  -- Then we compute det(charmatrix) by Laplace expansion along the first column.
  --
  -- Both sides are monic polynomials of the same degree (p.natDegree).
  -- The charpoly is monic by Matrix.charpoly_monic, and its degree equals the matrix
  -- dimension by Matrix.charpoly_natDegree_eq_dim.
  --
  -- The key observation is that the Laplace expansion gives:
  --   det(charmatrix) = X * det(minor₀₀) + det(minor₁₀)
  -- where minor₀₀ corresponds to a companion matrix of degree n-1
  -- (by the induction hypothesis, its determinant is ∑_{k=1}^{n-1} a_k X^{k-1} + X^{n-1})
  -- and minor₁₀ contributes a₀ times the appropriate term.
  --
  -- This gives the recurrence:
  --   det(charmatrix(companion(p))) = X * (X^{n-1} + a_{n-1}X^{n-2} + ... + a_1) + a_0
  --                                  = X^n + a_{n-1}X^{n-1} + ... + a_1X + a_0 = p
  --
  -- For a rigorous proof, we proceed by strong induction on n = p.natDegree.
  obtain ⟨n, hn_eq⟩ : ∃ n, p.natDegree = n + 1 := Nat.exists_eq_succ_of_ne_zero hn.ne'
  induction n generalizing p with
  | zero =>
    -- Base case: degree 1
    have hdeg : p.natDegree = 1 := hn_eq
    -- p = X + C(p.coeff 0) since p is monic of degree 1
    have hp_eq : p = X + Polynomial.C (p.coeff 0) := by
      rw [Polynomial.ext_iff]
      intro k
      rcases k with _ | _ | k
      · simp
      · -- k = 1: p.coeff 1 = 1 (monic) and (X + C a).coeff 1 = 1
        simp only [Polynomial.coeff_add, Polynomial.coeff_C_succ, add_zero]
        rw [Polynomial.coeff_X_one]
        have : p.coeff p.natDegree = 1 := hp.coeff_natDegree
        rwa [hdeg] at this
      · -- k ≥ 2: p.coeff k = 0 since degree < k
        simp only [Polynomial.coeff_add, Polynomial.coeff_X, Polynomial.coeff_C]
        simp [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega : p.natDegree < k + 2)]
    -- Now prove charpoly = p
    rw [Matrix.charpoly]
    -- The charmatrix of a 1×1 companion matrix has entry X + C(p.coeff 0)
    -- det of 1×1 matrix is the entry itself
    have h_det : (companion p hp hn).charmatrix.det = X + Polynomial.C (p.coeff 0) := by
      -- Since p.natDegree = 1, the matrix is 1×1
      haveI hUnique : Unique (Fin p.natDegree) := by
        rw [hdeg]
        exact ⟨⟨0, by omega⟩, fun i => Fin.ext (by omega)⟩
      rw [Matrix.det_unique]
      -- The (0,0) entry of charmatrix is X + C(p.coeff 0)
      simp only [companion_charmatrix, hdeg]
      -- default has value 0 and default + 1 = 1 = p.natDegree by hdeg
      simp only [↓reduceIte]
      have hdefault_val : (default : Fin p.natDegree).val = 0 := by
        have : default = (⟨0, hdeg ▸ Nat.zero_lt_one⟩ : Fin p.natDegree) :=
          (@Unique.eq_default _ hUnique ⟨0, hdeg ▸ Nat.zero_lt_one⟩).symm
        simp only [this]
      simp only [hdefault_val, zero_add, ↓reduceIte]
    rw [h_det, hp_eq]
    simp
  | succ m IH =>
    -- Inductive case: degree m + 2 = n
    -- p has degree n = m + 2
    have hdeg : p.natDegree = m + 2 := hn_eq
    -- Define the reindexed charmatrix for Laplace expansion
    let A : Matrix (Fin (m + 2)) (Fin (m + 2)) R[X] :=
      (companion p hp hn).charmatrix.submatrix (Fin.cast hdeg.symm) (Fin.cast hdeg.symm)
    have hA_det : A.det = (companion p hp hn).charmatrix.det := by
      -- A = charmatrix.submatrix (Fin.cast hdeg.symm) (Fin.cast hdeg.symm)
      -- We need to show det(A) = det(charmatrix)
      -- Fin.cast is the coercion from Fin (m+2) to Fin p.natDegree via hdeg.symm
      -- Since Fin.cast is a bijection (an equivalence), det is preserved
      -- finCongr hdeg.symm gives equivalence Fin (m+2) ≃ Fin p.natDegree
      -- So (finCongr hdeg.symm) : Fin (m+2) → Fin p.natDegree matches Fin.cast hdeg.symm
      have heq : A = (companion p hp hn).charmatrix.submatrix
          (finCongr hdeg.symm) (finCongr hdeg.symm) := by
        ext i j
        simp only [Matrix.submatrix_apply]
        rfl
      rw [heq, Matrix.det_submatrix_equiv_self]
    rw [Matrix.charpoly, ← hA_det]
    -- Now apply Laplace expansion to A which has type Matrix (Fin (m+2)) (Fin (m+2)) R[X]
    rw [Matrix.det_succ_column_zero]
    -- First, establish the values in the first column of A
    -- A i 0 = charmatrix(companion p) (cast i) 0
    have hA_col0 : ∀ i : Fin (m + 2), A i 0 =
        (companion p hp hn).charmatrix (Fin.cast hdeg.symm i) (Fin.cast hdeg.symm 0) := by
      intro i
      rfl
    -- Row 0: diagonal entry = X (since 0+1 ≠ n for n ≥ 2)
    have hA00 : A 0 0 = X := by
      rw [hA_col0]
      simp only [companion_charmatrix]
      simp only [↓reduceIte]
      -- Goal: (if (Fin.cast _ 0).val + 1 = p.natDegree then X + C(...) else X) = X
      have h1 : (Fin.cast hdeg.symm (0 : Fin (m + 2))).val + 1 ≠ p.natDegree := by
        simp only [Fin.val_cast, Fin.val_zero, hdeg]
        omega
      simp only [h1, ↓reduceIte]
    -- Row 1: subdiagonal entry = -1
    have hA10 : A 1 0 = -1 := by
      rw [hA_col0]
      simp only [companion_charmatrix]
      -- Need to show: not (cast 1 = cast 0), (cast 0).val + 1 = (cast 1).val (subdiag condition)
      have hcast1 : (Fin.cast hdeg.symm (1 : Fin (m + 2))).val = 1 := by simp
      have hcast0 : (Fin.cast hdeg.symm (0 : Fin (m + 2))).val = 0 := by simp
      have hne : (Fin.cast hdeg.symm (1 : Fin (m + 2))) ≠ Fin.cast hdeg.symm 0 := by
        simp only [ne_eq, Fin.ext_iff, hcast1, hcast0]
        omega
      simp only [hne, ↓reduceIte, hcast0, hcast1]
    -- Row k for k ≥ 2: entry = 0
    have hA_other : ∀ i : Fin (m + 2), 2 ≤ i.val → A i 0 = 0 := by
      intro i hi
      rw [hA_col0]
      simp only [companion_charmatrix]
      have hcast_i : (Fin.cast hdeg.symm i).val = i.val := by simp
      have hcast0 : (Fin.cast hdeg.symm (0 : Fin (m + 2))).val = 0 := by simp
      have hne : Fin.cast hdeg.symm i ≠ Fin.cast hdeg.symm 0 := by
        simp only [ne_eq, Fin.ext_iff, hcast_i, hcast0]
        omega
      simp only [hne, ↓reduceIte, hcast0, hcast_i]
      -- 0 + 1 ≠ i for i ≥ 2
      have h1 : ¬(0 + 1 = i.val) := by omega
      simp only [h1, ↓reduceIte]
      -- 0 + 1 ≠ p.natDegree for n ≥ 2
      have h2 : ¬((0 : ℕ) + 1 = p.natDegree) := by omega
      simp only [h2, ↓reduceIte]
    -- Now simplify the sum to just two terms
    -- The sum is ∑ i, (-1)^i * A i 0 * det(minor)
    -- Only i=0 and i=1 contribute non-zero terms
    have hsum : ∑ i : Fin (m + 2), (-1) ^ (i : ℕ) * A i 0 * (A.submatrix i.succAbove Fin.succ).det =
        (-1) ^ (0 : ℕ) * A 0 0 * (A.submatrix (0 : Fin (m + 2)).succAbove Fin.succ).det +
        (-1) ^ (1 : ℕ) * A 1 0 * (A.submatrix (1 : Fin (m + 2)).succAbove Fin.succ).det := by
      rw [Finset.sum_eq_add_sum_diff_singleton (Finset.mem_univ 0)]
      have h1_mem : (1 : Fin (m + 2)) ∈ Finset.univ \ {0} := by
        simp only [Finset.mem_sdiff, Finset.mem_univ, Finset.mem_singleton, true_and]
        exact Fin.ne_of_val_ne (by omega : (1 : ℕ) ≠ 0)
      rw [Finset.sum_eq_add_sum_diff_singleton h1_mem]
      -- Goal: term1 + sum_rest = term1
      -- Need to show sum_rest = 0
      have hrest : ∑ x ∈ ((Finset.univ : Finset (Fin (m + 2))) \ {0}) \ {1},
          (-1) ^ (x : ℕ) * A x 0 * (A.submatrix x.succAbove Fin.succ).det = 0 := by
        apply Finset.sum_eq_zero
        intro i hi
        simp only [Finset.mem_sdiff, Finset.mem_univ, Finset.mem_singleton, true_and] at hi
        have hi2 : 2 ≤ i.val := by
          have ⟨hne0, hne1⟩ := hi
          have hne0' : i.val ≠ 0 := fun h => hne0 (Fin.ext h)
          have hne1' : i.val ≠ 1 := fun h => hne1 (Fin.ext h)
          omega
        rw [hA_other i hi2]
        ring
      rw [hrest, add_zero]
      simp only [Fin.val_zero, Fin.val_one]
    rw [hsum, hA00, hA10]
    -- Simplify the signs
    simp only [pow_zero, one_mul, pow_one, mul_neg, mul_one, neg_neg]
    have hp_eq : p = X * p.divX + Polynomial.C (p.coeff 0) := by
      rw [Polynomial.ext_iff]
      intro k
      simp only [Polynomial.coeff_add, Polynomial.coeff_C]
      rcases k with _ | k
      · simp [Polynomial.divX]
      · -- For k = Nat.succ k, we have k + 1 ≠ 0, so C (p.coeff 0) contributes 0
        have hk_ne : k + 1 ≠ 0 := Nat.succ_ne_zero k
        simp only [hk_ne, ↓reduceIte, add_zero, Polynomial.coeff_X_mul, Polynomial.coeff_divX]
    -- Rewrite goal using hp_eq
    rw [hp_eq]
    -- Now goal is: X * det(minor00) + det(minor10) = X * p.divX + C(p.coeff 0)
    -- Suffices to show det(minor00) = p.divX and det(minor10) = C(p.coeff 0)
    congr 1
    -- First goal: det(minor00) = p.divX
    -- Second goal (after swap): det(minor10) = C(p.coeff 0)
    swap
    · let minor10 := A.submatrix (Fin.succAbove (1 : Fin (m + 2))) Fin.succ
      -- First, establish the first row structure
      have hrow0 : ∀ j : Fin (m + 1), minor10 0 j =
          if j.val = m then Polynomial.C (p.coeff 0) else 0 := by
        intro j
        -- minor10 0 j = A (succAbove 1 0) (succ j) = A 0 (j+1)
        change A (Fin.succAbove 1 0) (Fin.succ j) = _
        have h0 : Fin.succAbove (1 : Fin (m + 2)) 0 = 0 := rfl
        rw [h0]
        -- A 0 j.succ = charmatrix (cast 0) (cast j.succ)
        change (companion p hp hn).charmatrix (Fin.cast hdeg.symm 0)
            (Fin.cast hdeg.symm (Fin.succ j)) = _
        rw [companion_charmatrix]
        -- charmatrix at (0, j+1) where j ∈ Fin (m+1), so j+1 ∈ {1, ..., m+1}
        -- First condition: 0 = j+1 is false
        have hne : ¬(Fin.cast hdeg.symm 0 = Fin.cast hdeg.symm (Fin.succ j)) := by
          simp only [Fin.ext_iff, Fin.val_cast, Fin.val_zero, Fin.val_succ]
          omega
        -- Subdiagonal: (j+1)+1 ≠ 0
        have hsubdiag : ¬((Fin.cast hdeg.symm (Fin.succ j)).val + 1 =
            (Fin.cast hdeg.symm 0).val) := by
          simp only [Fin.val_cast, Fin.val_zero, Fin.val_succ]
          omega
        -- Last column: (j+1)+1 = m+2 iff j = m
        have hlast : (Fin.cast hdeg.symm (Fin.succ j)).val + 1 = p.natDegree ↔ j.val = m := by
          simp only [Fin.val_cast, Fin.val_succ, hdeg]
          omega
        -- Simplify the nested ifs
        simp only [hne, hsubdiag, ↓reduceIte]
        -- Split on whether j = m
        by_cases hj : j.val = m
        · -- j = m case
          have hcond : (Fin.succ j).val + 1 = p.natDegree := by
            simp only [Fin.val_succ, hj, hdeg]
          simp only [hcond, ↓reduceIte, hj, Fin.val_cast, Fin.val_zero]
        · -- j ≠ m case
          have hcond : ¬((Fin.cast hdeg.symm (Fin.succ j)).val + 1 = p.natDegree) := mt hlast.mp hj
          simp only [hcond, ↓reduceIte, hj]
      -- Now use Laplace expansion along row 0
      rw [Matrix.det_succ_row_zero]
      -- The sum has only one non-zero term at j = m
      -- Simplify using hrow0: minor10 0 j = 0 for j < m, and C(p.coeff 0) for j = m
      have hm_lt : m < m + 1 := by omega
      let jm : Fin (m + 1) := ⟨m, hm_lt⟩
      -- Rewrite the sum to isolate the j = m term
      have hsum_eq : ∑ j : Fin (m + 1), (-1) ^ j.val * minor10 0 j *
          (minor10.submatrix Fin.succ j.succAbove).det =
          (-1) ^ m * Polynomial.C (p.coeff 0) *
          (minor10.submatrix Fin.succ jm.succAbove).det := by
        rw [Finset.sum_eq_single jm]
        · simp only [hrow0, jm]
          simp
        · intro j _ hj
          simp only [hrow0]
          have hj' : j.val ≠ m := by
            intro heq
            apply hj
            ext
            exact heq
          simp only [hj', ↓reduceIte, mul_zero, zero_mul]
        · intro h
          exact (h (Finset.mem_univ jm)).elim
      rw [hsum_eq]
      -- Now we need: (-1)^m * C(p.coeff 0) * det(subminor) = C(p.coeff 0)
      -- where subminor is the m×m matrix obtained by removing row 0 and column m from minor10
      --
      -- The subminor = minor10.submatrix Fin.succ jm.succAbove
      -- This uses rows 1..m (via Fin.succ) and columns 0..m-1 (via jm.succAbove) of minor10
      --
      -- minor10(Fin.succ i, jm.succAbove j) for i, j ∈ Fin m
      -- = A(succAbove 1 (succ i), succ (succAbove m j))
      -- = A(i + 2, j + 1 if j < m else j + 2)
      -- For j < m: A(i + 2, j + 1)
      --
      -- The m×m subminor has entry at (i, j) = A(i+2, j+1)
      -- = charmatrix(companion p)(i+2, j+1) for i, j ∈ Fin m
      --
      -- Entry structure:
      -- - Diagonal of charmatrix at (i+2, j+1) when i+2 = j+1, i.e., i = j-1, i.e., j = i+1
      --   So superdiagonal of subminor has diagonal entries of charmatrix
      -- - Subdiagonal of charmatrix at (i+2, j+1) when (j+1)+1 = i+2, i.e., j+2 = i+2, i.e., j = i
      --   So diagonal of subminor has -1 (subdiagonal of charmatrix)
      --
      -- The m×m subminor has:
      -- - Diagonal: -1 (from charmatrix subdiagonal)
      -- - Superdiagonal: X (from charmatrix diagonal)
      -- - Other: 0
      --
      -- This is an upper bidiagonal matrix with -1 on diagonal.
      -- det = (-1)^m
      --
      -- Therefore: (-1)^m * C(p.coeff 0) * (-1)^m = C(p.coeff 0)
      have hsubminor_det : (minor10.submatrix Fin.succ jm.succAbove).det = (-1) ^ m := by
        -- The subminor is upper triangular with -1 on diagonal
        -- Let S = minor10.submatrix Fin.succ jm.succAbove
        -- S is m × m indexed by Fin m
        -- S(i, j) = minor10(succ i, succAbove m j)
        --         = A(succAbove 1 (succ i), succ (succAbove m j))
        --         = A(i + 2, j + 1)  [since succAbove 1 (succ i) = i+2 for i < m, and
        --                            succAbove m j = j for j < m, so succ(succAbove m j) = j+1]
        let S := minor10.submatrix Fin.succ jm.succAbove
        -- Establish the structure of S
        have hS_entry : ∀ i j : Fin m, S i j =
            if j.val = i.val then -1
            else if j.val = i.val + 1 then X
            else 0 := by
          intro i j
          -- S i j = minor10 (succ i) (jm.succAbove j)
          --       = A (succAbove 1 (succ i)) (succ (succAbove jm j))
          change minor10 (Fin.succ i) (jm.succAbove j) = _
          change A (Fin.succAbove 1 (Fin.succ i)) (Fin.succ (jm.succAbove j)) = _
          have hsuccAbove1 : (Fin.succAbove (1 : Fin (m + 2)) (Fin.succ i)).val = i.val + 2 := by
            simp [Fin.succAbove, Fin.succ, Fin.castSucc]
          have hsuccAboveM : ∀ k : Fin m, (Fin.succAbove jm k).val = k.val := by
            intro k
            have hk : k.val < m := k.isLt
            simp only [Fin.succAbove, jm, Fin.castSucc, Fin.lt_def]
            simp only [Fin.val_castAdd, hk, ↓reduceIte]
          have hsucc_succAbove : (Fin.succ (Fin.succAbove jm j)).val = j.val + 1 := by
            simp [Fin.succ, hsuccAboveM j]
          -- Now S i j = A (i+2) (j+1) = charmatrix(companion p) (cast (i+2)) (cast (j+1))
          -- A = charmatrix.submatrix (cast hdeg.symm) (cast hdeg.symm)
          -- A (succAbove 1 (succ i)) (succ (succAbove jm j))
          -- = charmatrix (cast (succAbove 1 (succ i))) (cast (succ (succAbove jm j)))
          change (companion p hp hn).charmatrix
              (Fin.cast hdeg.symm (Fin.succAbove 1 (Fin.succ i)))
              (Fin.cast hdeg.symm (Fin.succ (jm.succAbove j))) = _
          rw [companion_charmatrix]
          -- Now we check which case applies
          -- row index in charmatrix: cast (succAbove 1 (succ i)) has value i + 2
          -- col index in charmatrix: cast (succ (succAbove m j)) has value j + 1
          have hrow_val : (Fin.cast hdeg.symm
              (Fin.succAbove (1 : Fin (m + 2)) (Fin.succ i))).val = i.val + 2 := by
            simp only [Fin.val_cast, hsuccAbove1]
          have hcol_val : (Fin.cast hdeg.symm
              (Fin.succ (Fin.succAbove jm j))).val = j.val + 1 := by
            simp only [Fin.val_cast, hsucc_succAbove]
          -- Check diagonal: row = col iff i + 2 = j + 1 iff j = i + 1
          have hdiag : (Fin.cast hdeg.symm
              (Fin.succAbove (1 : Fin (m + 2)) (Fin.succ i)) =
              Fin.cast hdeg.symm (Fin.succ (Fin.succAbove jm j))) ↔ j.val = i.val + 1 := by
            simp only [Fin.ext_iff, hrow_val, hcol_val]
            omega
          -- Check subdiagonal: col + 1 = row iff j + 1 + 1 = i + 2 iff j = i
          have hsubdiag : (Fin.cast hdeg.symm (Fin.succ (Fin.succAbove jm j))).val + 1 =
              (Fin.cast hdeg.symm
              (Fin.succAbove (1 : Fin (m + 2)) (Fin.succ i))).val ↔ j.val = i.val := by
            simp only [hrow_val, hcol_val]
            omega
          -- Check last column: col + 1 = n iff j + 1 + 1 = m + 2 iff j = m, but j < m
          -- so never
          have hlastcol : ¬((Fin.cast hdeg.symm (Fin.succ (Fin.succAbove jm j))).val + 1
              = p.natDegree) := by
            simp only [hcol_val, hdeg]
            have hj : j.val < m := j.isLt
            omega
          by_cases hij : j.val = i.val
          · -- subdiagonal case: entry is -1
            have hne : ¬(Fin.cast hdeg.symm (Fin.succAbove (1 : Fin (m + 2)) (Fin.succ i)) =
                Fin.cast hdeg.symm (Fin.succ (Fin.succAbove jm j))) := by
              rw [hdiag]
              omega
            simp only [hne, ↓reduceIte, hsubdiag.mpr hij, hij]
          · by_cases hji1 : j.val = i.val + 1
            · -- diagonal case: entry is X (not X + C since row ≠ last)
              have heq : Fin.cast hdeg.symm (Fin.succAbove (1 : Fin (m + 2)) (Fin.succ i)) =
                  Fin.cast hdeg.symm (Fin.succ (Fin.succAbove jm j)) := hdiag.mpr hji1
              -- Check it's not the last row
              have hnotlast : ¬((Fin.cast hdeg.symm
                  (Fin.succ (Fin.succAbove jm j))).val + 1 = p.natDegree) := by
                simp only [hcol_val, hdeg]
                have hj : j.val < m := j.isLt
                omega
              -- j.val ≠ i.val (from hij in outer context)
              have hne_ji : ¬(i.val + 1 = i.val) := by omega
              simp only [heq, hnotlast, ↓reduceIte, hji1, hne_ji]
            · -- neither diagonal nor subdiagonal: entry is 0
              have hne : ¬(Fin.cast hdeg.symm (Fin.succAbove (1 : Fin (m + 2)) (Fin.succ i)) =
                  Fin.cast hdeg.symm (Fin.succ (Fin.succAbove jm j))) := by
                rw [hdiag]
                exact hji1
              have hnsub : ¬((Fin.cast hdeg.symm (Fin.succ (Fin.succAbove jm j))).val + 1 =
                  (Fin.cast hdeg.symm (Fin.succAbove (1 : Fin (m + 2)) (Fin.succ i))).val) := by
                rw [hsubdiag]
                exact hij
              simp only [hne, hnsub, hlastcol, ↓reduceIte, hij, hji1]
        -- S is upper triangular with -1 on diagonal
        -- det(S) = product of diagonal = (-1)^m
        have hS_tri : S.BlockTriangular id := by
          intro i j hij
          simp only [hS_entry]
          -- hij : j < i, so j.val < i.val
          -- j ≠ i, j ≠ i + 1, so entry is 0
          have hij' : j.val < i.val := hij
          have hne1 : j.val ≠ i.val := ne_of_lt hij'
          have hne2 : j.val ≠ i.val + 1 := by omega
          simp only [hne1, hne2, ↓reduceIte]
        rw [Matrix.det_of_upperTriangular hS_tri]
        -- det = product of diagonal entries = product of -1 = (-1)^m
        simp only [hS_entry, ↓reduceIte]
        rw [Finset.prod_const, Finset.card_fin]
      rw [hsubminor_det]
      -- Goal: (-1) ^ m * C (p.coeff 0) * (-1) ^ m = C (p.coeff 0)
      have h_pow : ((-1 : R[X]) ^ (m * 2)) = 1 := by
        rw [mul_comm, pow_mul]
        simp only [neg_one_sq, one_pow]
      ring_nf
      simp only [h_pow, mul_one]
    · -- Goal: X * (A.submatrix (Fin.succAbove 0) Fin.succ).det = X * p.divX
      -- Suffices to show: (A.submatrix (Fin.succAbove 0) Fin.succ).det = p.divX
      congr 1
      -- The submatrix is (m+1) × (m+1), and we want to apply IH to p.divX
      -- First establish properties of p.divX
      have hdivX_deg : p.divX.natDegree = m + 1 := by
        rw [Polynomial.natDegree_divX_eq_natDegree_tsub_one, hdeg]
        rfl
      have hdivX_monic : p.divX.Monic := by
        rw [Polynomial.Monic, Polynomial.leadingCoeff]
        rw [hdivX_deg]
        rw [Polynomial.coeff_divX]
        have h : m + 1 + 1 = p.natDegree := by omega
        rw [h]
        exact hp.coeff_natDegree
      have hdivX_pos : 0 < p.divX.natDegree := by omega
      -- Apply IH to p.divX
      have hIH := IH p.divX hdivX_monic hdivX_pos hdivX_deg
      -- hIH : (companion p.divX hdivX_monic hdivX_pos).charpoly = p.divX
      rw [Matrix.charpoly] at hIH
      -- hIH : (companion p.divX _ _).charmatrix.det = p.divX
      -- We need: (A.submatrix (Fin.succAbove 0) Fin.succ).det = p.divX
      -- So we need to show: A.submatrix (Fin.succAbove 0) Fin.succ
      --                   = (companion p.divX _ _).charmatrix (up to reindexing)
      --
      -- The key observation: the (i+1, j+1) subblock of charmatrix(companion p)
      -- equals charmatrix(companion p.divX) because:
      -- - Diagonal entries: X or X + C(coeff) depending on position
      -- - Subdiagonal: -1
      -- - Last column: C(coeff)
      -- - Other: 0
      -- Show minor = (companion p.divX ...).charmatrix via reindexing
      -- minor is indexed by Fin (m+1)
      -- charmatrix(companion p.divX) is indexed by Fin (p.divX.natDegree) = Fin (m+1)
      have hminor_entry : ∀ i j : Fin (m + 1),
          A (Fin.succAbove (0 : Fin (m + 2)) i) (Fin.succ j) =
          (companion p.divX hdivX_monic hdivX_pos).charmatrix
            (Fin.cast hdivX_deg.symm i) (Fin.cast hdivX_deg.symm j) := by
        intro i j
        -- LHS: A (succAbove 0 i) (succ j)
        --    = charmatrix(companion p) (cast (succAbove 0 i)) (cast (succ j))
        -- RHS: charmatrix(companion p.divX) (cast i) (cast j)
        have hsuccAbove0 : (Fin.succAbove (0 : Fin (m + 2)) i).val = i.val + 1 := by
          simp [Fin.succAbove]
        -- Unfold A and use companion_charmatrix on both sides
        simp only [A, Matrix.submatrix_apply]
        rw [companion_charmatrix, companion_charmatrix]
        -- Now compare the two charmatrix formulas
        have hrow_A : (Fin.cast hdeg.symm (Fin.succAbove (0 : Fin (m + 2)) i)).val = i.val + 1 := by
          simp only [Fin.val_cast, hsuccAbove0]
        have hcol_A : (Fin.cast hdeg.symm (Fin.succ j)).val = j.val + 1 := by simp
        have hrow_B : (Fin.cast hdivX_deg.symm i).val = i.val := by simp
        have hcol_B : (Fin.cast hdivX_deg.symm j).val = j.val := by simp
        -- Diagonal condition
        have hdiag_A : (Fin.cast hdeg.symm (Fin.succAbove 0 i) =
            Fin.cast hdeg.symm (Fin.succ j)) ↔ i = j := by
          simp only [Fin.ext_iff, hrow_A, hcol_A]
          constructor <;> (intro h; omega)
        have hdiag_B : (Fin.cast hdivX_deg.symm i = Fin.cast hdivX_deg.symm j) ↔ i = j := by
          constructor
          · intro h
            have hv : (Fin.cast hdivX_deg.symm i).val = (Fin.cast hdivX_deg.symm j).val := by rw [h]
            simp only [Fin.val_cast] at hv
            exact Fin.ext hv
          · intro h; exact congrArg _ h
        -- Last row condition for diagonal entry (on row coordinate)
        have hlastrow_A : (Fin.cast hdeg.symm (Fin.succAbove 0 i)).val + 1 = p.natDegree ↔
            i.val = m := by
          simp only [hrow_A, hdeg]
          omega
        have hlastrow_B : (Fin.cast hdivX_deg.symm i).val + 1 = p.divX.natDegree ↔
            i.val = m := by
          simp only [hrow_B, hdivX_deg]
          omega
        -- Last row condition on column coordinate when on diagonal (j = i)
        have hlastcol_diag_A : (Fin.cast hdeg.symm (Fin.succ i)).val + 1 = p.natDegree ↔
            i.val = m := by
          simp only [Fin.val_cast, Fin.val_succ, hdeg]
          omega
        have hlastcol_diag_B : (Fin.cast hdivX_deg.symm i).val + 1 = p.divX.natDegree ↔
            i.val = m := by
          simp only [hrow_B, hdivX_deg]
          omega
        -- Subdiagonal condition
        have hsubdiag_A : (Fin.cast hdeg.symm (Fin.succ j)).val + 1 =
            (Fin.cast hdeg.symm (Fin.succAbove 0 i)).val ↔ j.val + 1 = i.val := by
          simp only [hcol_A, hrow_A]
          omega
        have hsubdiag_B : (Fin.cast hdivX_deg.symm j).val + 1 =
            (Fin.cast hdivX_deg.symm i).val ↔ j.val + 1 = i.val := by
          simp only [hcol_B, hrow_B]
        -- Last column condition
        have hlastcol_A : (Fin.cast hdeg.symm (Fin.succ j)).val + 1 = p.natDegree ↔
            j.val = m := by
          simp only [hcol_A, hdeg]
          omega
        have hlastcol_B : (Fin.cast hdivX_deg.symm j).val + 1 = p.divX.natDegree ↔
            j.val = m := by
          simp only [hcol_B, hdivX_deg]
          omega
        -- Coefficient relation: p.coeff (i + 1) = p.divX.coeff i
        have hcoeff : p.coeff (i.val + 1) = p.divX.coeff i.val := by
          rw [Polynomial.coeff_divX]
        have hcoeff_j : p.coeff (j.val + 1) = p.divX.coeff j.val := by
          rw [Polynomial.coeff_divX]
        -- Now case split and show equality
        by_cases hij : i = j
        · -- Diagonal case
          subst hij
          have hcond_A : Fin.cast hdeg.symm (Fin.succAbove 0 i) = Fin.cast hdeg.symm (Fin.succ i) :=
            hdiag_A.mpr rfl
          simp only [hcond_A, ↓reduceIte]
          by_cases hlast : i.val = m
          · -- Last diagonal entry: both if conditions are true
            have hcond1 : (Fin.cast hdeg.symm (Fin.succ i)).val + 1 = p.natDegree :=
              hlastcol_diag_A.mpr hlast
            have hcond2 : (Fin.cast hdivX_deg.symm i).val + 1 = p.divX.natDegree :=
              hlastcol_diag_B.mpr hlast
            simp only [hcond1, hcond2, ↓reduceIte]
            congr 1
            simp only [Fin.val_cast, Fin.val_succ, hcoeff]
          · -- Non-last diagonal entry: both if conditions are false
            have hcond1 : ¬((Fin.cast hdeg.symm (Fin.succ i)).val + 1 = p.natDegree) :=
              mt hlastcol_diag_A.mp hlast
            have hcond2 : ¬((Fin.cast hdivX_deg.symm i).val + 1 = p.divX.natDegree) :=
              mt hlastcol_diag_B.mp hlast
            simp only [hcond1, hcond2, ↓reduceIte]
        · -- Off-diagonal case
          have hcond_ne : ¬(Fin.cast hdeg.symm (Fin.succAbove 0 i) =
              Fin.cast hdeg.symm (Fin.succ j)) := mt hdiag_A.mp hij
          have hcond_ne' : ¬(Fin.cast hdivX_deg.symm i = Fin.cast hdivX_deg.symm j) :=
            mt hdiag_B.mp hij
          simp only [hcond_ne, hcond_ne', ↓reduceIte]
          by_cases hsubdiag : j.val + 1 = i.val
          · -- Subdiagonal
            have hcond1 : (Fin.cast hdeg.symm (Fin.succ j)).val + 1 =
                (Fin.cast hdeg.symm (Fin.succAbove 0 i)).val := hsubdiag_A.mpr hsubdiag
            have hcond2 : (Fin.cast hdivX_deg.symm j).val + 1 =
                (Fin.cast hdivX_deg.symm i).val := hsubdiag_B.mpr hsubdiag
            simp only [hcond1, hcond2, ↓reduceIte]
          · -- Not subdiagonal
            have hcond1 : ¬((Fin.cast hdeg.symm (Fin.succ j)).val + 1 =
                (Fin.cast hdeg.symm (Fin.succAbove 0 i)).val) := mt hsubdiag_A.mp hsubdiag
            have hcond2 : ¬((Fin.cast hdivX_deg.symm j).val + 1 =
                (Fin.cast hdivX_deg.symm i).val) := mt hsubdiag_B.mp hsubdiag
            simp only [hcond1, hcond2, ↓reduceIte]
            by_cases hlastcol : j.val = m
            · -- Last column
              have hcond3 : (Fin.cast hdeg.symm (Fin.succ j)).val + 1 = p.natDegree :=
                hlastcol_A.mpr hlastcol
              have hcond4 : (Fin.cast hdivX_deg.symm j).val + 1 = p.divX.natDegree :=
                hlastcol_B.mpr hlastcol
              simp only [hcond3, hcond4, ↓reduceIte, hrow_A, hrow_B, hcoeff]
            · -- Neither
              have hcond3 : ¬((Fin.cast hdeg.symm (Fin.succ j)).val + 1 = p.natDegree) :=
                mt hlastcol_A.mp hlastcol
              have hcond4 : ¬((Fin.cast hdivX_deg.symm j).val + 1 = p.divX.natDegree) :=
                mt hlastcol_B.mp hlastcol
              simp only [hcond3, hcond4, ↓reduceIte]
      have hminor_eq : A.submatrix (Fin.succAbove (0 : Fin (m + 2))) Fin.succ =
          (companion p.divX hdivX_monic hdivX_pos).charmatrix.submatrix
          (Fin.cast hdivX_deg.symm) (Fin.cast hdivX_deg.symm) := by
        apply Matrix.ext
        intro i j
        simp only [Matrix.submatrix_apply]
        exact hminor_entry i j
      -- Now compute the determinant
      rw [hminor_eq]
      have heq : (companion p.divX hdivX_monic hdivX_pos).charmatrix.submatrix
          (Fin.cast hdivX_deg.symm) (Fin.cast hdivX_deg.symm) =
          (companion p.divX hdivX_monic hdivX_pos).charmatrix.submatrix
          (finCongr hdivX_deg.symm) (finCongr hdivX_deg.symm) := by rfl
      rw [heq, Matrix.det_submatrix_equiv_self (finCongr hdivX_deg.symm)]
      exact hIH

/-! ### Polynomial evaluation -/

/-- The polynomial p annihilates its companion matrix.

This follows from Cayley-Hamilton: every matrix satisfies its characteristic polynomial,
and the characteristic polynomial of companion(p) is p itself.
-/
theorem companion_aeval_eq_zero (p : R[X]) (hp : p.Monic) (hn : 0 < p.natDegree) :
    aeval (companion p hp hn) p = 0 := by
  have h := aeval_self_charpoly (companion p hp hn)
  rwa [companion_charpoly p hp hn] at h

/-! ### Powers and order for cyclotomic polynomials -/

/-- If p divides X^m - 1, then companion(p)^m = 1.

This is because p(companion(p)) = 0, and if p | X^m - 1, then
X^m - 1 = p * q for some q, so companion(p)^m - 1 = p(companion(p)) * q(companion(p)) = 0.
-/
theorem companion_pow_eq_one_of_dvd (p : R[X]) (hp : p.Monic) (hn : 0 < p.natDegree)
    (m : ℕ) (hdvd : p ∣ X ^ m - 1) :
    (companion p hp hn) ^ m = 1 := by
  -- From hdvd, get q such that X^m - 1 = p * q
  obtain ⟨q, hq⟩ := hdvd
  -- Let A = companion p
  let A := companion p hp hn
  -- We have aeval A p = 0 by companion_aeval_eq_zero
  have hp_zero : aeval A p = 0 := companion_aeval_eq_zero p hp hn
  -- Therefore aeval A (X^m - 1) = aeval A (p * q) = aeval A p * aeval A q = 0
  have hXm1_zero : aeval A (X ^ m - (1 : R[X])) = 0 := by
    rw [hq, aeval_mul, hp_zero, zero_mul]
  -- But aeval A (X^m - 1) = A^m - 1
  have haeval : aeval A (X ^ m - (1 : R[X])) = A ^ m - 1 := by
    simp only [map_sub, map_pow, aeval_X, map_one]
  -- So A^m - 1 = 0, i.e., A^m = 1
  rw [haeval] at hXm1_zero
  exact sub_eq_zero.mp hXm1_zero

/-- The companion matrix of the m-th cyclotomic polynomial has (companion)^m = 1.

This follows because Φ_m divides X^m - 1.
-/
theorem companion_cyclotomic_pow_eq_one (m : ℕ) (_hm : 0 < m)
    (hn : 0 < (cyclotomic m ℤ).natDegree) :
    (companion (cyclotomic m ℤ) (cyclotomic.monic m ℤ) hn) ^ m = 1 := by
  apply companion_pow_eq_one_of_dvd
  exact cyclotomic.dvd_X_pow_sub_one m ℤ

/-- The order of companion(Φ_m) is exactly m.

This requires showing that companion(Φ_m)^k ≠ 1 for 0 < k < m.
The key is that the eigenvalues of companion(Φ_m) are exactly the primitive
m-th roots of unity, none of which are k-th roots of unity for k < m.
-/
theorem companion_cyclotomic_orderOf (m : ℕ) (hm : 2 ≤ m)
    (hn : 0 < (cyclotomic m ℤ).natDegree) :
    orderOf (companion (cyclotomic m ℤ) (cyclotomic.monic m ℤ) hn) = m := by
  -- Use orderOf_eq_iff: need to show A^m = 1 and forall k, 0 < k < m → A^k ≠ 1
  let A := companion (cyclotomic m ℤ) (cyclotomic.monic m ℤ) hn
  have hm_pos : 0 < m := Nat.lt_of_lt_of_le (by norm_num : 0 < 2) hm
  rw [orderOf_eq_iff hm_pos]
  constructor
  · -- A^m = 1
    exact companion_cyclotomic_pow_eq_one m hm_pos hn
  · -- For k < m, 0 < k → A^k ≠ 1
    intro k hk hk_pos hAk
    -- If A^k = 1, then aeval A (X^k - 1) = 0
    have haeval_zero : aeval A (X ^ k - (1 : ℤ[X])) = 0 := by
      simp only [map_sub, map_pow, aeval_X, map_one]
      rw [hAk, sub_self]
    -- We also have aeval A (cyclotomic m ℤ) = 0
    have hcycl_zero : aeval A (cyclotomic m ℤ) = 0 :=
      companion_aeval_eq_zero (cyclotomic m ℤ) (cyclotomic.monic m ℤ) hn
    -- Map everything to ℚ and work there
    -- Let A_Q be the matrix over ℚ
    let A_Q := A.map (algebraMap ℤ ℚ)
    -- Both polynomials annihilate A_Q
    have haeval_Q_zero : aeval A_Q ((X ^ k - 1 : ℤ[X]).map (algebraMap ℤ ℚ)) = 0 := by
      have : A_Q = (Algebra.ofId ℤ ℚ).mapMatrix A := rfl
      rw [this, aeval_map_algebraMap, aeval_algHom_apply, haeval_zero, map_zero]
    have hcycl_Q_zero : aeval A_Q ((cyclotomic m ℤ).map (algebraMap ℤ ℚ)) = 0 := by
      have : A_Q = (Algebra.ofId ℤ ℚ).mapMatrix A := rfl
      rw [this, aeval_map_algebraMap, aeval_algHom_apply, hcycl_zero, map_zero]
    -- Simplify the mapped polynomials
    simp only [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_one]
      at haeval_Q_zero
    -- Convert algebraMap ℤ ℚ to Int.castRingHom ℚ for map_cyclotomic_int
    have hmap_eq : (cyclotomic m ℤ).map (algebraMap ℤ ℚ) = cyclotomic m ℚ := by
      have h1 : algebraMap ℤ ℚ = Int.castRingHom ℚ := rfl
      rw [h1, map_cyclotomic_int]
    rw [hmap_eq] at hcycl_Q_zero
    -- minpoly ℚ A_Q divides both X^k - 1 and cyclotomic m ℚ
    have hdvd1 : minpoly ℚ A_Q ∣ (X ^ k - 1 : ℚ[X]) := minpoly.dvd ℚ A_Q haeval_Q_zero
    have hdvd2 : minpoly ℚ A_Q ∣ cyclotomic m ℚ := minpoly.dvd ℚ A_Q hcycl_Q_zero
    -- minpoly divides charpoly, and charpoly = cyclotomic m ℚ
    have hcharpoly : A_Q.charpoly = cyclotomic m ℚ := by
      -- charpoly(A.map f) = (charpoly A).map f for ring homs
      have h1 : A_Q.charpoly = (A.charpoly).map (algebraMap ℤ ℚ) := by
        rw [Matrix.charpoly_map]
      rw [h1, companion_charpoly, hmap_eq]
    -- cyclotomic m ℚ is irreducible over ℚ
    have hirr : Irreducible (cyclotomic m ℚ) := cyclotomic.irreducible_rat hm_pos
    -- Since minpoly | cyclotomic (irreducible), minpoly = 1 or minpoly = cyclotomic
    -- But minpoly has degree ≥ 1 (A_Q is not in ℚ), so minpoly = cyclotomic m ℚ (up to unit)
    have hminpoly_eq : minpoly ℚ A_Q = cyclotomic m ℚ := by
      have hdvd := Matrix.minpoly_dvd_charpoly A_Q
      rw [hcharpoly] at hdvd
      -- minpoly | cyclotomic, cyclotomic irreducible
      -- By Irreducible.dvd_iff: minpoly | cycl ↔ IsUnit minpoly ∨ Associated cycl minpoly
      rcases hirr.dvd_iff.mp hdvd with hunit | hassoc
      · -- minpoly is unit, impossible since minpoly is monic and evaluates to zero at A_Q
        exfalso
        -- If minpoly is a unit, it must be a constant polynomial
        -- But minpoly is monic, so it would have to be 1
        -- But aeval A_Q (minpoly) = 0, so 1 = 0, contradiction
        have hmonic := minpoly.monic (Matrix.isIntegral A_Q)
        have haeval_minpoly := minpoly.aeval ℚ A_Q
        -- For a unit polynomial over a field to be monic, it must equal 1
        have hunit_eq : minpoly ℚ A_Q = 1 := by
          rcases Polynomial.isUnit_iff.mp hunit with ⟨c, hc, heq⟩
          rw [← heq] at hmonic
          -- Monic (C c) means leadingCoeff (C c) = 1
          -- For nonzero c, leadingCoeff (C c) = c
          -- So c = 1
          have hc_one : c = 1 := by
            unfold Polynomial.Monic at hmonic
            simp only [Polynomial.leadingCoeff_C] at hmonic
            exact hmonic
          simp [← heq, hc_one]
        rw [hunit_eq] at haeval_minpoly
        simp only [Polynomial.aeval_one] at haeval_minpoly
        -- haeval_minpoly : (1 : Matrix _ _ ℚ) = 0, which is false
        -- The matrix ring is nontrivial since the dimension is positive
        haveI : Nonempty (Fin (cyclotomic m ℤ).natDegree) := ⟨⟨0, hn⟩⟩
        -- (1 : Matrix n n R) (i, i) = 1 ≠ 0 for nontrivial R
        have h1ne0 : (1 : Matrix (Fin (cyclotomic m ℤ).natDegree)
            (Fin (cyclotomic m ℤ).natDegree) ℚ) ≠ 0 := by
          intro h0
          have : (1 : Matrix (Fin (cyclotomic m ℤ).natDegree)
              (Fin (cyclotomic m ℤ).natDegree) ℚ) ⟨0, hn⟩ ⟨0, hn⟩ =
              (0 : Matrix (Fin (cyclotomic m ℤ).natDegree)
              (Fin (cyclotomic m ℤ).natDegree) ℚ) ⟨0, hn⟩ ⟨0, hn⟩ := by rw [h0]
          simp only [Matrix.one_apply_eq, Matrix.zero_apply] at this
          exact one_ne_zero this
        exact h1ne0 haeval_minpoly
      · -- Associated cyclotomic minpoly, so they're equal since both are monic
        have hmonic1 := minpoly.monic (Matrix.isIntegral A_Q)
        have hmonic2 := cyclotomic.monic m ℚ
        exact eq_of_monic_of_associated hmonic1 hmonic2 hassoc.symm
    -- So cyclotomic m ℚ | X^k - 1
    rw [hminpoly_eq] at hdvd1
    -- But cyclotomic m only divides X^n - 1 when m | n
    -- X^k - 1 = ∏_{d | k} cyclotomic d ℚ
    -- So cyclotomic m ∣ X^k - 1 iff m ∈ k.divisors iff m ∣ k
    have hm_dvd_k : m ∣ k := by
      -- Use that X^k - 1 = ∏_{d | k} cyclotomic d
      rw [← prod_cyclotomic_eq_X_pow_sub_one hk_pos ℚ] at hdvd1
      -- cyclotomic m ℚ divides the product ∏_{d | k} cyclotomic d ℚ
      -- Since cyclotomic polynomials are pairwise coprime (for different indices),
      -- and cyclotomic m is irreducible, it must equal one of the factors
      -- i.e., m ∈ k.divisors
      have hcoprime : ∀ i j : ℕ, i ∈ k.divisors → j ∈ k.divisors → i ≠ j →
          IsCoprime (cyclotomic i ℚ) (cyclotomic j ℚ) := by
        intro i j _ _ hij
        exact cyclotomic.isCoprime_rat hij
      -- cyclotomic m is irreducible
      -- If it divides a product of coprimes, it must divide one factor
      -- Use Finset.prod_dvd_of_isUnit_of_dvd or similar
      by_contra hndvd
      have hm_notin : m ∉ k.divisors := by
        simp only [Nat.mem_divisors]
        push_neg
        intro hd
        -- If m | k then m ≤ k (since k > 0), but k < m, contradiction
        have hle : m ≤ k := Nat.le_of_dvd hk_pos hd
        omega
      -- cyclotomic m ∣ ∏_{d | k} cyclotomic d, but m ∉ k.divisors
      -- This is impossible because cyclotomics for different indices are coprime
      have : cyclotomic m ℚ ∣ ∏ d ∈ k.divisors, cyclotomic d ℚ := hdvd1
      -- If p is irreducible and divides a product of pairwise coprime terms,
      -- it must divide one of them
      have hex : ∃ d ∈ k.divisors, cyclotomic m ℚ ∣ cyclotomic d ℚ := by
        -- Use the fact that irreducible dividing product of coprime terms
        -- means it divides one of them
        -- This follows from unique factorization
        have huf := UniqueFactorizationMonoid.irreducible_iff_prime.mp hirr
        exact Prime.exists_mem_finset_dvd huf this
      obtain ⟨d, hd_mem, hdvd_d⟩ := hex
      -- cyclotomic m | cyclotomic d, both monic irreducible, so they're equal
      -- Since cyclotomic is injective on indices (over CharZero), m = d
      have heq : m = d := by
        have hirr_d : Irreducible (cyclotomic d ℚ) := by
          have hd_pos : 0 < d := Nat.pos_of_mem_divisors hd_mem
          exact cyclotomic.irreducible_rat hd_pos
        -- Two monic irreducible polynomials where one divides the other must be equal
        have hmonic_m := cyclotomic.monic m ℚ
        have hmonic_d := cyclotomic.monic d ℚ
        have hassoc : Associated (cyclotomic m ℚ) (cyclotomic d ℚ) :=
          associated_of_dvd_dvd hdvd_d (hirr.dvd_symm hirr_d hdvd_d)
        exact cyclotomic_injective (eq_of_monic_of_associated hmonic_m hmonic_d hassoc)
      rw [heq] at hm_notin
      exact hm_notin hd_mem
    -- m | k and 0 < k < m is a contradiction
    have : k < m := hk
    have : m ≤ k := Nat.le_of_dvd hk_pos hm_dvd_k
    omega

/-! ### Integer matrix membership -/

/-- The companion matrix of Φ_m gives an integer matrix with order m.

This directly provides elements of integerMatrixOrders for dimensions ≥ φ(m).
-/
theorem companion_cyclotomic_mem_integerMatrixOrders (m : ℕ) (hm : 2 ≤ m)
    (hn : 0 < (cyclotomic m ℤ).natDegree) :
    m ∈ Crystallographic.integerMatrixOrders (cyclotomic m ℤ).natDegree := by
  use companion (cyclotomic m ℤ) (cyclotomic.monic m ℤ) hn
  constructor
  · exact companion_cyclotomic_orderOf m hm hn
  · omega

/-- For m >= 2, m ∈ integerMatrixOrders(totient m). -/
theorem mem_integerMatrixOrders_totient (m : ℕ) (hm : 2 ≤ m) :
    m ∈ Crystallographic.integerMatrixOrders (Nat.totient m) := by
  have hdeg : (cyclotomic m ℤ).natDegree = Nat.totient m := Polynomial.natDegree_cyclotomic m ℤ
  have htot_pos : 0 < Nat.totient m := Nat.totient_pos.mpr (by omega)
  have hn : 0 < (cyclotomic m ℤ).natDegree := by omega
  rw [← hdeg]
  exact companion_cyclotomic_mem_integerMatrixOrders m hm hn

end Crystallographic
