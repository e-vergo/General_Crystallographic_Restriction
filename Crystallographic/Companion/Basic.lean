/-
Copyright (c) 2026 Eric Vergo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo
-/
import Dress
import Mathlib.Algebra.Polynomial.Degree.Definitions
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Block
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.LinearAlgebra.Matrix.Charpoly.Minpoly

/-!
# Companion Matrices

This file defines the companion matrix of a monic polynomial and proves its key properties.

## Main definitions

* `companion` - The companion matrix of a monic polynomial

## Main results

* `companion_charpoly` - The characteristic polynomial of companion(p) equals p
* `companion_aeval_eq_zero` - The polynomial p annihilates its companion matrix
* `companion_pow_eq_one_of_dvd` - If p divides X^m - 1, then companion(p)^m = 1

## References

* Standard linear algebra texts on companion matrices
* Sasse, R. (2020). "Crystallographic Groups"

## Tags

companion matrix, characteristic polynomial, monic polynomial, matrix order
-/

namespace Crystallographic

open Matrix Polynomial

variable {R : Type*} [CommRing R]

/-- The companion matrix of a monic polynomial p of degree n.

For p = X^n + a_{n-1}X^{n-1} + ... + a_1 X + a_0, the companion matrix is:
```
[0  0  0  ...  0  -a_0    ]
[1  0  0  ...  0  -a_1    ]
[0  1  0  ...  0  -a_2    ]
[        ...              ]
[0  0  0  ...  1  -a_{n-1}]
```

The matrix has 1s on the subdiagonal and the negatives of the polynomial
coefficients in the last column.
-/
@[blueprint
  "companion-def"
  (statement := /-- The companion matrix $C(p)$ of a monic polynomial
  $p = X^n + a_{n-1}X^{n-1} + \cdots + a_0$ is the $n \times n$ matrix with $1$s
  on the subdiagonal and $-a_i$ in the last column:
  $$C(p) = \begin{pmatrix} 0 & 0 & \cdots & -a_0 \\ 1 & 0 & \cdots & -a_1 \\
  \vdots & \ddots & & \vdots \\ 0 & \cdots & 1 & -a_{n-1} \end{pmatrix}$$
  This construction produces a matrix whose characteristic polynomial equals $p$, providing
  a canonical matrix realization for any monic polynomial. -/)]
def companion (p : R[X]) (_hp : p.Monic) (_hn : 0 < p.natDegree) :
    Matrix (Fin p.natDegree) (Fin p.natDegree) R :=
  Matrix.of fun i j =>
    if j.val + 1 = i.val then 1
    else if j.val + 1 = p.natDegree then -p.coeff i.val
    else 0

/-! ### Characteristic polynomial -/

/-- The charmatrix of a companion matrix has a specific structure: diagonal entries are
`X` (or `X + C(p.coeff i)` in the last column), subdiagonal entries are `-1`,
last column entries are `C(p.coeff i)`, and all other entries are `0`. -/
lemma companion_charmatrix_apply (p : R[X]) (hp : p.Monic) (hn : 0 < p.natDegree)
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
    -- Now we have: X - C (if i.val + 1 = i.val then 1 else if i.val + 1 = n then -p.coeff i ...)
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

/-! ### Helper lemmas for companion_charpoly -/

/-- For a monic polynomial of degree 1, the characteristic polynomial of its companion
matrix equals the polynomial. Both sides equal `X + C(p.coeff 0)`. -/
lemma companion_charpoly_of_natDegree_one (p : R[X]) (hp : p.Monic) (hn : 0 < p.natDegree)
    (hdeg : p.natDegree = 1) : (companion p hp hn).charpoly = p := by
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
    haveI hUnique : Unique (Fin p.natDegree) := by rw [hdeg]; exact Fin.instUnique
    rw [Matrix.det_unique, companion_charmatrix_apply]
    have hdefault : (default : Fin p.natDegree).val = 0 := by
      have : default = (⟨0, hdeg ▸ Nat.zero_lt_one⟩ : Fin p.natDegree) :=
        (@Unique.eq_default _ hUnique ⟨0, hdeg ▸ Nat.zero_lt_one⟩).symm
      simp only [this]
    simp only [hdefault, hdeg, zero_add, ↓reduceIte]
  rw [h_det, hp_eq]
  simp

/-- The first column of the charmatrix of a companion matrix has `X` at position `(0,0)`,
`-1` at position `(1,0)`, and `0` at all positions `(i,0)` for `i >= 2`. -/
lemma companion_charmatrix_col_zero (p : R[X]) (hp : p.Monic) (hn : 0 < p.natDegree)
    (m : ℕ) (hdeg : p.natDegree = m + 2)
    (A : Matrix (Fin (m + 2)) (Fin (m + 2)) R[X])
    (hA_def : A = (companion p hp hn).charmatrix.submatrix
        (Fin.cast hdeg.symm) (Fin.cast hdeg.symm)) :
    (A 0 0 = X) ∧
    (A 1 0 = -1) ∧
    (∀ i : Fin (m + 2), 2 ≤ i.val → A i 0 = 0) := by
  have hA_col0 : ∀ i : Fin (m + 2), A i 0 =
      (companion p hp hn).charmatrix (Fin.cast hdeg.symm i) (Fin.cast hdeg.symm 0) := by
    intro i; rw [hA_def]; rfl
  constructor
  · -- A 0 0 = X
    rw [hA_col0]
    simp only [companion_charmatrix_apply]
    simp only [↓reduceIte]
    have h1 : (Fin.cast hdeg.symm (0 : Fin (m + 2))).val + 1 ≠ p.natDegree := by
      simp only [Fin.val_cast, Fin.val_zero, hdeg]; omega
    simp only [h1, ↓reduceIte]
  constructor
  · -- A 1 0 = -1
    rw [hA_col0]
    simp only [companion_charmatrix_apply]
    have hcast1 : (Fin.cast hdeg.symm (1 : Fin (m + 2))).val = 1 := by simp
    have hcast0 : (Fin.cast hdeg.symm (0 : Fin (m + 2))).val = 0 := by simp
    have hne : (Fin.cast hdeg.symm (1 : Fin (m + 2))) ≠ Fin.cast hdeg.symm 0 := by
      simp only [ne_eq, Fin.ext_iff, hcast1, hcast0]; omega
    simp only [hne, ↓reduceIte, hcast0, hcast1]
  · -- A i 0 = 0 for i ≥ 2
    intro i hi
    rw [hA_col0]
    simp only [companion_charmatrix_apply]
    have hcast_i : (Fin.cast hdeg.symm i).val = i.val := by simp
    have hcast0 : (Fin.cast hdeg.symm (0 : Fin (m + 2))).val = 0 := by simp
    have hne : Fin.cast hdeg.symm i ≠ Fin.cast hdeg.symm 0 := by
      simp only [ne_eq, Fin.ext_iff, hcast_i, hcast0]; omega
    simp only [hne, ↓reduceIte, hcast0, hcast_i]
    have h1 : ¬(0 + 1 = i.val) := by omega
    simp only [h1, ↓reduceIte]
    have h2 : ¬((0 : ℕ) + 1 = p.natDegree) := by omega
    simp only [h2, ↓reduceIte]

/-- In the minor obtained by deleting row 1 and column 0 from the charmatrix,
row 0 is zero except at the last position, where it equals `C(p.coeff 0)`. -/
lemma companion_charmatrix_minor10_row0 (p : R[X]) (hp : p.Monic) (hn : 0 < p.natDegree)
    (m : ℕ) (hdeg : p.natDegree = m + 2)
    (A : Matrix (Fin (m + 2)) (Fin (m + 2)) R[X])
    (hA_def : A = (companion p hp hn).charmatrix.submatrix
        (Fin.cast hdeg.symm) (Fin.cast hdeg.symm))
    (j : Fin (m + 1)) :
    A.submatrix (Fin.succAbove (1 : Fin (m + 2))) Fin.succ 0 j =
      if j.val = m then Polynomial.C (p.coeff 0) else 0 := by
  change A (Fin.succAbove 1 0) (Fin.succ j) = _
  have h0 : Fin.succAbove (1 : Fin (m + 2)) 0 = 0 := rfl
  rw [h0, hA_def]
  change (companion p hp hn).charmatrix (Fin.cast hdeg.symm 0)
      (Fin.cast hdeg.symm (Fin.succ j)) = _
  rw [companion_charmatrix_apply]
  have hne : ¬(Fin.cast hdeg.symm 0 = Fin.cast hdeg.symm (Fin.succ j)) := by
    simp only [Fin.ext_iff, Fin.val_cast, Fin.val_zero, Fin.val_succ]; omega
  have hsubdiag : ¬((Fin.cast hdeg.symm (Fin.succ j)).val + 1 = (Fin.cast hdeg.symm 0).val) := by
    simp only [Fin.val_cast, Fin.val_zero, Fin.val_succ]; omega
  have hlast : (Fin.cast hdeg.symm (Fin.succ j)).val + 1 = p.natDegree ↔ j.val = m := by
    simp only [Fin.val_cast, Fin.val_succ, hdeg]; omega
  simp only [hne, hsubdiag, ↓reduceIte]
  by_cases hj : j.val = m
  · have hcond : (Fin.succ j).val + 1 = p.natDegree := by simp only [Fin.val_succ, hj, hdeg]
    simp only [hcond, ↓reduceIte, hj, Fin.val_cast, Fin.val_zero]
  · have hcond : ¬((Fin.cast hdeg.symm (Fin.succ j)).val + 1 = p.natDegree) := mt hlast.mp hj
    simp only [hcond, ↓reduceIte, hj]

/-- The subminor obtained by further deleting row 0 and column m from the (1,0)-minor
has entries `-1` on the diagonal, `X` on the superdiagonal, and `0` elsewhere. -/
lemma companion_charmatrix_subminor_apply (p : R[X]) (hp : p.Monic) (hn : 0 < p.natDegree)
    (m : ℕ) (hdeg : p.natDegree = m + 2)
    (A : Matrix (Fin (m + 2)) (Fin (m + 2)) R[X])
    (hA_def : A = (companion p hp hn).charmatrix.submatrix
        (Fin.cast hdeg.symm) (Fin.cast hdeg.symm))
    (jm : Fin (m + 1)) (hjm : jm = ⟨m, by omega⟩)
    (i j : Fin m) :
    (A.submatrix (Fin.succAbove (1 : Fin (m + 2))) Fin.succ).submatrix Fin.succ jm.succAbove i j =
      if j.val = i.val then -1 else if j.val = i.val + 1 then X else 0 := by
  change A (Fin.succAbove 1 (Fin.succ i)) (Fin.succ (jm.succAbove j)) = _
  rw [hA_def]
  have hsuccAbove1 : (Fin.succAbove (1 : Fin (m + 2)) (Fin.succ i)).val = i.val + 2 := by
    simp [Fin.succAbove, Fin.succ, Fin.castSucc]
  have hsuccAboveM : (jm.succAbove j).val = j.val := by
    have hj : j.val < m := j.isLt
    simp only [Fin.succAbove, hjm, Fin.castSucc, Fin.lt_def, Fin.val_castAdd, hj, ↓reduceIte]
  have hsucc_succAbove : (Fin.succ (jm.succAbove j)).val = j.val + 1 := by
    simp [Fin.succ, hsuccAboveM]
  change (companion p hp hn).charmatrix
      (Fin.cast hdeg.symm (Fin.succAbove 1 (Fin.succ i)))
      (Fin.cast hdeg.symm (Fin.succ (jm.succAbove j))) = _
  rw [companion_charmatrix_apply]
  have hrow_val : (Fin.cast hdeg.symm (Fin.succAbove (1 : Fin (m + 2)) (Fin.succ i))).val =
      i.val + 2 := by simp only [Fin.val_cast, hsuccAbove1]
  have hcol_val : (Fin.cast hdeg.symm (Fin.succ (jm.succAbove j))).val = j.val + 1 := by
    simp only [Fin.val_cast, hsucc_succAbove]
  have hdiag : (Fin.cast hdeg.symm (Fin.succAbove (1 : Fin (m + 2)) (Fin.succ i)) =
      Fin.cast hdeg.symm (Fin.succ (jm.succAbove j))) ↔ j.val = i.val + 1 := by
    simp only [Fin.ext_iff, hrow_val, hcol_val]; omega
  have hsubdiag : (Fin.cast hdeg.symm (Fin.succ (jm.succAbove j))).val + 1 =
      (Fin.cast hdeg.symm (Fin.succAbove (1 : Fin (m + 2)) (Fin.succ i))).val ↔
      j.val = i.val := by simp only [hrow_val, hcol_val]; omega
  have hlastcol : ¬((Fin.cast hdeg.symm (Fin.succ (jm.succAbove j))).val + 1 = p.natDegree) := by
    simp only [hcol_val, hdeg]; have hj : j.val < m := j.isLt; omega
  by_cases hij : j.val = i.val
  · have hne : ¬(Fin.cast hdeg.symm (Fin.succAbove (1 : Fin (m + 2)) (Fin.succ i)) =
        Fin.cast hdeg.symm (Fin.succ (jm.succAbove j))) := by rw [hdiag]; omega
    simp only [hne, ↓reduceIte, hsubdiag.mpr hij, hij]
  · by_cases hji1 : j.val = i.val + 1
    · have heq : Fin.cast hdeg.symm (Fin.succAbove (1 : Fin (m + 2)) (Fin.succ i)) =
          Fin.cast hdeg.symm (Fin.succ (jm.succAbove j)) := hdiag.mpr hji1
      have hne_ji : ¬(i.val + 1 = i.val) := by omega
      simp only [heq, hlastcol, ↓reduceIte, hji1, hne_ji]
    · have hne : ¬(Fin.cast hdeg.symm (Fin.succAbove (1 : Fin (m + 2)) (Fin.succ i)) =
          Fin.cast hdeg.symm (Fin.succ (jm.succAbove j))) := by rw [hdiag]; exact hji1
      have hnsub : ¬((Fin.cast hdeg.symm (Fin.succ (jm.succAbove j))).val + 1 =
          (Fin.cast hdeg.symm (Fin.succAbove (1 : Fin (m + 2)) (Fin.succ i))).val) := by
        rw [hsubdiag]; exact hij
      simp only [hne, hnsub, hlastcol, ↓reduceIte, hij, hji1]

/-- The subminor (obtained by deleting row 0 and column m from the (1,0)-minor) is upper
triangular with `-1` on the diagonal, so its determinant equals `(-1)^m`. -/
lemma companion_charmatrix_subminor_det (p : R[X]) (hp : p.Monic) (hn : 0 < p.natDegree)
    (m : ℕ) (hdeg : p.natDegree = m + 2)
    (A : Matrix (Fin (m + 2)) (Fin (m + 2)) R[X])
    (hA_def : A = (companion p hp hn).charmatrix.submatrix
        (Fin.cast hdeg.symm) (Fin.cast hdeg.symm))
    (jm : Fin (m + 1)) (hjm : jm = ⟨m, by omega⟩) :
    ((A.submatrix (Fin.succAbove (1 : Fin (m + 2))) Fin.succ).submatrix Fin.succ jm.succAbove).det =
      (-1) ^ m := by
  let S := (A.submatrix (Fin.succAbove (1 : Fin (m + 2))) Fin.succ).submatrix Fin.succ jm.succAbove
  have hS_entry : ∀ i j : Fin m, S i j =
      if j.val = i.val then -1 else if j.val = i.val + 1 then X else 0 :=
    companion_charmatrix_subminor_apply p hp hn m hdeg A hA_def jm hjm
  have hS_tri : S.BlockTriangular id := by
    intro i j hij
    simp only [hS_entry]
    have hij' : j.val < i.val := hij
    have hne1 : j.val ≠ i.val := ne_of_lt hij'
    have hne2 : j.val ≠ i.val + 1 := by omega
    simp only [hne1, hne2, ↓reduceIte]
  rw [Matrix.det_of_upperTriangular hS_tri]
  simp only [hS_entry, ↓reduceIte, Finset.prod_const, Finset.card_fin]

/-- The determinant of the (1,0)-minor of the charmatrix equals `C(p.coeff 0)`.
This follows from Laplace expansion along row 0, where only the last column entry is nonzero. -/
lemma companion_charmatrix_minor10_det (p : R[X]) (hp : p.Monic) (hn : 0 < p.natDegree)
    (m : ℕ) (hdeg : p.natDegree = m + 2)
    (A : Matrix (Fin (m + 2)) (Fin (m + 2)) R[X])
    (hA_def : A = (companion p hp hn).charmatrix.submatrix
        (Fin.cast hdeg.symm) (Fin.cast hdeg.symm)) :
    (A.submatrix (1 : Fin (m + 2)).succAbove Fin.succ).det = Polynomial.C (p.coeff 0) := by
  let minor10 := A.submatrix (Fin.succAbove (1 : Fin (m + 2))) Fin.succ
  have hrow0 : ∀ j : Fin (m + 1), minor10 0 j =
      if j.val = m then Polynomial.C (p.coeff 0) else 0 :=
    companion_charmatrix_minor10_row0 p hp hn m hdeg A hA_def
  -- Laplace expansion along row 0 reduces to single term at j = m
  rw [Matrix.det_succ_row_zero]
  let jm : Fin (m + 1) := ⟨m, by omega⟩
  have hsum_eq : ∑ j : Fin (m + 1), (-1) ^ j.val * minor10 0 j *
      (minor10.submatrix Fin.succ j.succAbove).det =
      (-1) ^ m * Polynomial.C (p.coeff 0) * (minor10.submatrix Fin.succ jm.succAbove).det := by
    rw [Finset.sum_eq_single jm]
    · simp only [hrow0, jm]; simp
    · intro j _ hj
      have hj' : j.val ≠ m := fun heq => hj (Fin.ext heq)
      simp only [hrow0, hj', ↓reduceIte, mul_zero, zero_mul]
    · intro h; exact (h (Finset.mem_univ jm)).elim
  rw [hsum_eq, companion_charmatrix_subminor_det p hp hn m hdeg A hA_def jm rfl]
  -- Simplify (-1)^m * C(p.coeff 0) * (-1)^m = C(p.coeff 0)
  have h_pow : ((-1 : R[X]) ^ (m * 2)) = 1 := by
    rw [mul_comm, pow_mul]; simp only [neg_one_sq, one_pow]
  ring_nf; simp only [h_pow, mul_one]

/-- Auxiliary structure bundling index condition equivalences for the (0,0)-minor entry lemma.
These conditions relate entries of the charmatrix of companion(p) to those of companion(p.divX). -/
structure CompanionMinor00IndexConds (m : ℕ) (p : R[X]) (hdeg : p.natDegree = m + 2)
    (hdivX_deg : p.divX.natDegree = m + 1) (i j : Fin (m + 1)) where
  /-- Row index in A -/
  row_A : (Fin.cast hdeg.symm (Fin.succAbove (0 : Fin (m + 2)) i)).val = i.val + 1
  /-- Column index in A -/
  col_A : (Fin.cast hdeg.symm (Fin.succ j)).val = j.val + 1
  /-- Row index in B -/
  row_B : (Fin.cast hdivX_deg.symm i).val = i.val
  /-- Column index in B -/
  col_B : (Fin.cast hdivX_deg.symm j).val = j.val
  /-- Diagonal condition for A -/
  diag_A : (Fin.cast hdeg.symm (Fin.succAbove 0 i) = Fin.cast hdeg.symm (Fin.succ j)) ↔ i = j
  /-- Diagonal condition for B -/
  diag_B : (Fin.cast hdivX_deg.symm i = Fin.cast hdivX_deg.symm j) ↔ i = j
  /-- Last column condition for diagonal in A -/
  lastcol_diag_A : (Fin.cast hdeg.symm (Fin.succ i)).val + 1 = p.natDegree ↔ i.val = m
  /-- Last column condition for diagonal in B -/
  lastcol_diag_B : (Fin.cast hdivX_deg.symm i).val + 1 = p.divX.natDegree ↔ i.val = m
  /-- Subdiagonal condition for A -/
  subdiag_A : (Fin.cast hdeg.symm (Fin.succ j)).val + 1 =
      (Fin.cast hdeg.symm (Fin.succAbove 0 i)).val ↔ j.val + 1 = i.val
  /-- Subdiagonal condition for B -/
  subdiag_B : (Fin.cast hdivX_deg.symm j).val + 1 = (Fin.cast hdivX_deg.symm i).val ↔
      j.val + 1 = i.val
  /-- Last column condition for A -/
  lastcol_A : (Fin.cast hdeg.symm (Fin.succ j)).val + 1 = p.natDegree ↔ j.val = m
  /-- Last column condition for B -/
  lastcol_B : (Fin.cast hdivX_deg.symm j).val + 1 = p.divX.natDegree ↔ j.val = m

/-- Constructs the index condition bundle for the (0,0)-minor entry lemma. -/
def mkCompanionMinor00IndexConds (m : ℕ) (p : R[X]) (hdeg : p.natDegree = m + 2)
    (hdivX_deg : p.divX.natDegree = m + 1) (i j : Fin (m + 1)) :
    CompanionMinor00IndexConds m p hdeg hdivX_deg i j where
  row_A := by simp [Fin.succAbove]
  col_A := by simp
  row_B := by simp
  col_B := by simp
  diag_A := by
    have hrow : (Fin.cast hdeg.symm (Fin.succAbove (0 : Fin (m + 2)) i)).val = i.val + 1 := by
      simp [Fin.succAbove]
    have hcol : (Fin.cast hdeg.symm (Fin.succ j)).val = j.val + 1 := by simp
    simp only [Fin.ext_iff, hrow, hcol]; omega
  diag_B := by simp only [Fin.ext_iff, Fin.val_cast]
  lastcol_diag_A := by simp only [Fin.val_cast, Fin.val_succ, hdeg]; omega
  lastcol_diag_B := by simp only [Fin.val_cast, hdivX_deg]; omega
  subdiag_A := by
    have hrow : (Fin.cast hdeg.symm (Fin.succAbove (0 : Fin (m + 2)) i)).val = i.val + 1 := by
      simp [Fin.succAbove]
    have hcol : (Fin.cast hdeg.symm (Fin.succ j)).val = j.val + 1 := by simp
    simp only [hcol, hrow]; omega
  subdiag_B := by simp only [Fin.val_cast]
  lastcol_A := by simp only [Fin.val_cast, Fin.val_succ, hdeg]; omega
  lastcol_B := by simp only [Fin.val_cast, hdivX_deg]; omega

/-- The (0,0)-minor of the charmatrix of companion(p) equals the charmatrix of companion(p.divX),
entry by entry (after appropriate index translations). This enables the inductive step
in proving that the characteristic polynomial of a companion matrix equals the original polynomial. -/
lemma companion_charmatrix_minor00_apply (p : R[X]) (hp : p.Monic) (hn : 0 < p.natDegree)
    (m : ℕ) (hdeg : p.natDegree = m + 2)
    (A : Matrix (Fin (m + 2)) (Fin (m + 2)) R[X])
    (hA_def : A = (companion p hp hn).charmatrix.submatrix
        (Fin.cast hdeg.symm) (Fin.cast hdeg.symm))
    (hdivX_deg : p.divX.natDegree = m + 1)
    (hdivX_monic : p.divX.Monic)
    (hdivX_pos : 0 < p.divX.natDegree) :
    ∀ i j : Fin (m + 1),
      A (Fin.succAbove (0 : Fin (m + 2)) i) (Fin.succ j) =
      (companion p.divX hdivX_monic hdivX_pos).charmatrix
        (Fin.cast hdivX_deg.symm i) (Fin.cast hdivX_deg.symm j) := by
  intro i j
  rw [hA_def, Matrix.submatrix_apply, companion_charmatrix_apply, companion_charmatrix_apply]
  -- Get all index conditions from the bundle
  let c := mkCompanionMinor00IndexConds m p hdeg hdivX_deg i j
  -- Coefficient relation
  have hcoeff : p.coeff (i.val + 1) = p.divX.coeff i.val := by rw [Polynomial.coeff_divX]
  -- Case analysis using bundled conditions
  by_cases hij : i = j
  · -- Diagonal case
    subst hij
    have hcond_A : Fin.cast hdeg.symm (Fin.succAbove 0 i) = Fin.cast hdeg.symm (Fin.succ i) :=
      c.diag_A.mpr rfl
    simp only [hcond_A, ↓reduceIte]
    by_cases hlast : i.val = m
    · simp only [c.lastcol_diag_A.mpr hlast, c.lastcol_diag_B.mpr hlast, ↓reduceIte]
      congr 1; simp only [Fin.val_cast, Fin.val_succ, hcoeff]
    · simp only [mt c.lastcol_diag_A.mp hlast, mt c.lastcol_diag_B.mp hlast, ↓reduceIte]
  · -- Off-diagonal case
    simp only [mt c.diag_A.mp hij, mt c.diag_B.mp hij, ↓reduceIte]
    by_cases hsubdiag : j.val + 1 = i.val
    · simp only [c.subdiag_A.mpr hsubdiag, c.subdiag_B.mpr hsubdiag, ↓reduceIte]
    · simp only [mt c.subdiag_A.mp hsubdiag, mt c.subdiag_B.mp hsubdiag, ↓reduceIte]
      by_cases hlastcol : j.val = m
      · simp only [c.lastcol_A.mpr hlastcol, c.lastcol_B.mpr hlastcol, ↓reduceIte, c.row_A,
          c.row_B, hcoeff]
      · simp only [mt c.lastcol_A.mp hlastcol, mt c.lastcol_B.mp hlastcol, ↓reduceIte]

/-- The determinant of the (0,0)-minor of the charmatrix equals `p.divX`.
This follows because the minor equals the charmatrix of companion(p.divX), and we
apply the induction hypothesis for the characteristic polynomial theorem. -/
lemma companion_charmatrix_minor00_det (p : R[X]) (hp : p.Monic) (hn : 0 < p.natDegree)
    (m : ℕ) (hdeg : p.natDegree = m + 2)
    (A : Matrix (Fin (m + 2)) (Fin (m + 2)) R[X])
    (hA_def : A = (companion p hp hn).charmatrix.submatrix
        (Fin.cast hdeg.symm) (Fin.cast hdeg.symm))
    (IH : ∀ (q : R[X]) (hq : q.Monic) (hq_pos : 0 < q.natDegree), q.natDegree = m + 1 →
      (companion q hq hq_pos).charpoly = q) :
    (A.submatrix (0 : Fin (m + 2)).succAbove Fin.succ).det = p.divX := by
  -- Establish facts about p.divX
  have hdivX_deg : p.divX.natDegree = m + 1 := by
    rw [Polynomial.natDegree_divX_eq_natDegree_tsub_one, hdeg]; rfl
  have hdivX_monic : p.divX.Monic := by
    rw [Polynomial.Monic, Polynomial.leadingCoeff]
    rw [hdivX_deg]
    rw [Polynomial.coeff_divX]
    have h : m + 1 + 1 = p.natDegree := by omega
    rw [h]
    exact hp.coeff_natDegree
  have hdivX_pos : 0 < p.divX.natDegree := by omega
  -- Apply the induction hypothesis
  have hIH := IH p.divX hdivX_monic hdivX_pos hdivX_deg
  rw [Matrix.charpoly] at hIH
  -- Use the entry equality lemma to establish matrix equality
  have hminor_entry := companion_charmatrix_minor00_apply p hp hn m hdeg A hA_def
      hdivX_deg hdivX_monic hdivX_pos
  have hminor_eq : A.submatrix (Fin.succAbove (0 : Fin (m + 2))) Fin.succ =
      (companion p.divX hdivX_monic hdivX_pos).charmatrix.submatrix
      (Fin.cast hdivX_deg.symm) (Fin.cast hdivX_deg.symm) := by
    apply Matrix.ext
    intro i j
    simp only [Matrix.submatrix_apply]
    exact hminor_entry i j
  rw [hminor_eq]
  -- Show the submatrix determinant equals the full determinant
  have heq : (companion p.divX hdivX_monic hdivX_pos).charmatrix.submatrix
      (Fin.cast hdivX_deg.symm) (Fin.cast hdivX_deg.symm) =
      (companion p.divX hdivX_monic hdivX_pos).charmatrix.submatrix
      (finCongr hdivX_deg.symm) (finCongr hdivX_deg.symm) := by rfl
  rw [heq, Matrix.det_submatrix_equiv_self (finCongr hdivX_deg.symm)]
  exact hIH

/-- The Laplace expansion of a matrix along column 0 reduces to two terms when only
entries at rows 0 and 1 are nonzero. This applies to the charmatrix of companion matrices
because entries `A i 0 = 0` for all `i >= 2`. -/
lemma companion_charmatrix_laplace_col_zero (m : ℕ)
    (A : Matrix (Fin (m + 2)) (Fin (m + 2)) R[X])
    (hA00 : A 0 0 = X) (hA10 : A 1 0 = -1)
    (hA_other : ∀ i : Fin (m + 2), 2 ≤ i.val → A i 0 = 0) :
    ∑ i : Fin (m + 2), (-1) ^ (i : ℕ) * A i 0 * (A.submatrix i.succAbove Fin.succ).det =
    X * (A.submatrix (0 : Fin (m + 2)).succAbove Fin.succ).det +
    (A.submatrix (1 : Fin (m + 2)).succAbove Fin.succ).det := by
  rw [Finset.sum_eq_add_sum_diff_singleton (Finset.mem_univ 0)]
  have h1_mem : (1 : Fin (m + 2)) ∈ Finset.univ \ {0} := by
    simp only [Finset.mem_sdiff, Finset.mem_univ, Finset.mem_singleton, true_and]
    exact Fin.ne_of_val_ne (by omega : (1 : ℕ) ≠ 0)
  rw [Finset.sum_eq_add_sum_diff_singleton h1_mem]
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
    rw [hA_other i hi2]; ring
  rw [hrest, add_zero]
  simp only [Fin.val_zero, Fin.val_one, hA00, hA10, pow_zero, one_mul, pow_one, mul_neg, mul_one,
    neg_neg]

/-- The characteristic polynomial of the companion matrix equals the original polynomial.

This is the fundamental property of companion matrices: they are constructed precisely
so that their characteristic polynomial matches the given monic polynomial.

The proof proceeds by strong induction on the degree n. For degree 1, direct computation
shows both sides equal X + C(a_0). For degree n+1, Laplace expansion along the first
column gives a recurrence matching the polynomial structure.
-/
@[blueprint
  "thm:companion-charpoly"
  (statement := /-- The characteristic polynomial of the companion matrix $C(p)$ equals $p$:
  $\chi_{C(p)} = p$. The proof proceeds by induction on the degree, using cofactor expansion
  along the first column. The key insight is that the minor structure reduces to smaller
  companion matrices, and the base case (degree 1) follows by direct computation.
  \uses{companion-def} -/)
  (proof := /-- By induction on the degree $n$. For the base case $n = 1$, direct computation gives
  $\det(XI - C) = X + a_0$. For $n > 1$, expand along the first column: the $(1,1)$ minor
  is the companion matrix of lower degree, and the $(2,1)$ minor contributes the constant
  term. The recurrence matches the polynomial coefficients. -/)]
theorem companion_charpoly (p : R[X]) (hp : p.Monic) (hn : 0 < p.natDegree) :
    (companion p hp hn).charpoly = p := by
  obtain ⟨n, hn_eq⟩ : ∃ n, p.natDegree = n + 1 := Nat.exists_eq_succ_of_ne_zero hn.ne'
  induction n generalizing p with
  | zero => exact companion_charpoly_of_natDegree_one p hp hn hn_eq
  | succ m IH =>
    have hdeg : p.natDegree = m + 2 := hn_eq
    let A : Matrix (Fin (m + 2)) (Fin (m + 2)) R[X] :=
      (companion p hp hn).charmatrix.submatrix (Fin.cast hdeg.symm) (Fin.cast hdeg.symm)
    have hA_def : A = (companion p hp hn).charmatrix.submatrix
        (Fin.cast hdeg.symm) (Fin.cast hdeg.symm) := rfl
    have hA_det : A.det = (companion p hp hn).charmatrix.det := by
      have heq : A = (companion p hp hn).charmatrix.submatrix
          (finCongr hdeg.symm) (finCongr hdeg.symm) := by
        ext i j; simp only [Matrix.submatrix_apply]; rfl
      rw [heq, Matrix.det_submatrix_equiv_self]
    rw [Matrix.charpoly, ← hA_det, Matrix.det_succ_column_zero]
    -- Get column structure and apply Laplace simplification
    obtain ⟨hA00, hA10, hA_other⟩ := companion_charmatrix_col_zero p hp hn m hdeg A hA_def
    rw [companion_charmatrix_laplace_col_zero m A hA00 hA10 hA_other, ← Polynomial.X_mul_divX_add p,
      companion_charmatrix_minor00_det p hp hn m hdeg A hA_def IH,
      companion_charmatrix_minor10_det p hp hn m hdeg A hA_def]

/-! ### Polynomial evaluation -/

@[simp, blueprint "lem:companion-aeval-zero"
  (statement := /-- $p(C(p)) = 0$ (Cayley-Hamilton). By the Cayley-Hamilton theorem, every
  matrix satisfies its characteristic polynomial. Since the characteristic polynomial of
  $C(p)$ is exactly $p$ (by \texttt{companion\_charpoly}), we have $p(C(p)) = 0$.
  \uses{thm:companion-charpoly} -/)
  (proof := /-- By Cayley-Hamilton, every matrix satisfies its characteristic polynomial.
  Since $\chi_{C(p)} = p$ by the companion characteristic polynomial theorem,
  we have $p(C(p)) = 0$. -/)]
theorem companion_aeval_eq_zero (p : R[X]) (hp : p.Monic) (hn : 0 < p.natDegree) :
    aeval (companion p hp hn) p = 0 := by
  have h := aeval_self_charpoly (companion p hp hn)
  rwa [companion_charpoly p hp hn] at h

/-! ### Powers and order -/

@[blueprint "thm:companion-pow-dvd"
  (statement := /-- If $p \mid X^m - 1$, then $C(p)^m = I$. If $p \mid X^m - 1$, write
  $X^m - 1 = p \cdot q$ for some $q$. Since $p(C(p)) = 0$, evaluating at $C(p)$ gives
  $(X^m - 1)(C(p)) = p(C(p)) \cdot q(C(p)) = 0$, so $C(p)^m - I = 0$.
  \uses{lem:companion-aeval-zero} -/)
  (proof := /-- If $p \mid X^m - 1$, write $X^m - 1 = p \cdot q$ for some polynomial $q$.
  Evaluating at $C(p)$: $(X^m - 1)(C(p)) = p(C(p)) \cdot q(C(p)) = 0 \cdot q(C(p)) = 0$,
  so $C(p)^m = I$. -/)]
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

end Crystallographic

