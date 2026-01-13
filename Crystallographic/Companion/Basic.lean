/-
Copyright (c) 2026 Eric Vergo. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Eric Vergo
-/
import Architect
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
  $$C(p) = \begin{pmatrix} 0 & 0 & \cdots & -a_0 \\ 1 & 0 & \cdots & -a_1 \\ \vdots & \ddots & & \vdots \\ 0 & \cdots & 1 & -a_{n-1} \end{pmatrix}$$
  This construction produces a matrix whose characteristic polynomial equals $p$, providing
  a canonical matrix realization for any monic polynomial. -/)]
def companion (p : R[X]) (_hp : p.Monic) (_hn : 0 < p.natDegree) :
    Matrix (Fin p.natDegree) (Fin p.natDegree) R :=
  Matrix.of fun i j =>
    if j.val + 1 = i.val then 1
    else if j.val + 1 = p.natDegree then -p.coeff i.val
    else 0



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

/-- Base case for companion_charpoly: For a monic polynomial of degree 1,
the characteristic polynomial of its companion matrix equals the polynomial.

For degree 1, both p and charpoly are X + C(p.coeff 0). -/
private lemma companion_charpoly_base_case (p : R[X]) (hp : p.Monic) (hn : 0 < p.natDegree)
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

/-- Column structure of the charmatrix for Laplace expansion.

For the charmatrix A of companion(p) where p has degree m+2:
- A 0 0 = X (first diagonal entry)
- A 1 0 = -1 (subdiagonal entry)
- A i 0 = 0 for i ≥ 2 (zeros below subdiagonal) -/
private lemma companion_charmatrix_col_structure (p : R[X]) (hp : p.Monic) (hn : 0 < p.natDegree)
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
    simp only [companion_charmatrix]
    simp only [↓reduceIte]
    have h1 : (Fin.cast hdeg.symm (0 : Fin (m + 2))).val + 1 ≠ p.natDegree := by
      simp only [Fin.val_cast, Fin.val_zero, hdeg]; omega
    simp only [h1, ↓reduceIte]
  constructor
  · -- A 1 0 = -1
    rw [hA_col0]
    simp only [companion_charmatrix]
    have hcast1 : (Fin.cast hdeg.symm (1 : Fin (m + 2))).val = 1 := by simp
    have hcast0 : (Fin.cast hdeg.symm (0 : Fin (m + 2))).val = 0 := by simp
    have hne : (Fin.cast hdeg.symm (1 : Fin (m + 2))) ≠ Fin.cast hdeg.symm 0 := by
      simp only [ne_eq, Fin.ext_iff, hcast1, hcast0]; omega
    simp only [hne, ↓reduceIte, hcast0, hcast1]
  · -- A i 0 = 0 for i ≥ 2
    intro i hi
    rw [hA_col0]
    simp only [companion_charmatrix]
    have hcast_i : (Fin.cast hdeg.symm i).val = i.val := by simp
    have hcast0 : (Fin.cast hdeg.symm (0 : Fin (m + 2))).val = 0 := by simp
    have hne : Fin.cast hdeg.symm i ≠ Fin.cast hdeg.symm 0 := by
      simp only [ne_eq, Fin.ext_iff, hcast_i, hcast0]; omega
    simp only [hne, ↓reduceIte, hcast0, hcast_i]
    have h1 : ¬(0 + 1 = i.val) := by omega
    simp only [h1, ↓reduceIte]
    have h2 : ¬((0 : ℕ) + 1 = p.natDegree) := by omega
    simp only [h2, ↓reduceIte]

/-- Determinant of minor10 equals C(p.coeff 0).

In the Laplace expansion of charmatrix(companion p), the minor obtained by
deleting row 1 and column 0 has determinant (-1)^m * C(p.coeff 0) * (-1)^m = C(p.coeff 0).
This minor is an upper triangular matrix with -1 on the diagonal (except row 0). -/
private lemma companion_charpoly_minor10_det (p : R[X]) (hp : p.Monic) (hn : 0 < p.natDegree)
    (m : ℕ) (hdeg : p.natDegree = m + 2)
    (A : Matrix (Fin (m + 2)) (Fin (m + 2)) R[X])
    (hA_def : A = (companion p hp hn).charmatrix.submatrix
        (Fin.cast hdeg.symm) (Fin.cast hdeg.symm)) :
    (A.submatrix (1 : Fin (m + 2)).succAbove Fin.succ).det = Polynomial.C (p.coeff 0) := by
  let minor10 := A.submatrix (Fin.succAbove (1 : Fin (m + 2))) Fin.succ
  -- First, establish the first row structure
  have hrow0 : ∀ j : Fin (m + 1), minor10 0 j =
      if j.val = m then Polynomial.C (p.coeff 0) else 0 := by
    intro j
    change A (Fin.succAbove 1 0) (Fin.succ j) = _
    have h0 : Fin.succAbove (1 : Fin (m + 2)) 0 = 0 := rfl
    rw [h0, hA_def]
    change (companion p hp hn).charmatrix (Fin.cast hdeg.symm 0)
        (Fin.cast hdeg.symm (Fin.succ j)) = _
    rw [companion_charmatrix]
    have hne : ¬(Fin.cast hdeg.symm 0 = Fin.cast hdeg.symm (Fin.succ j)) := by
      simp only [Fin.ext_iff, Fin.val_cast, Fin.val_zero, Fin.val_succ]; omega
    have hsubdiag : ¬((Fin.cast hdeg.symm (Fin.succ j)).val + 1 =
        (Fin.cast hdeg.symm 0).val) := by
      simp only [Fin.val_cast, Fin.val_zero, Fin.val_succ]; omega
    have hlast : (Fin.cast hdeg.symm (Fin.succ j)).val + 1 = p.natDegree ↔ j.val = m := by
      simp only [Fin.val_cast, Fin.val_succ, hdeg]; omega
    simp only [hne, hsubdiag, ↓reduceIte]
    by_cases hj : j.val = m
    · have hcond : (Fin.succ j).val + 1 = p.natDegree := by
        simp only [Fin.val_succ, hj, hdeg]
      simp only [hcond, ↓reduceIte, hj, Fin.val_cast, Fin.val_zero]
    · have hcond : ¬((Fin.cast hdeg.symm (Fin.succ j)).val + 1 = p.natDegree) := mt hlast.mp hj
      simp only [hcond, ↓reduceIte, hj]
  -- Now use Laplace expansion along row 0
  rw [Matrix.det_succ_row_zero]
  have hm_lt : m < m + 1 := by omega
  let jm : Fin (m + 1) := ⟨m, hm_lt⟩
  have hsum_eq : ∑ j : Fin (m + 1), (-1) ^ j.val * minor10 0 j *
      (minor10.submatrix Fin.succ j.succAbove).det =
      (-1) ^ m * Polynomial.C (p.coeff 0) *
      (minor10.submatrix Fin.succ jm.succAbove).det := by
    rw [Finset.sum_eq_single jm]
    · simp only [hrow0, jm]; simp
    · intro j _ hj
      simp only [hrow0]
      have hj' : j.val ≠ m := by intro heq; apply hj; ext; exact heq
      simp only [hj', ↓reduceIte, mul_zero, zero_mul]
    · intro h; exact (h (Finset.mem_univ jm)).elim
  rw [hsum_eq]
  have hsubminor_det : (minor10.submatrix Fin.succ jm.succAbove).det = (-1) ^ m := by
    let S := minor10.submatrix Fin.succ jm.succAbove
    have hS_entry : ∀ i j : Fin m, S i j =
        if j.val = i.val then -1
        else if j.val = i.val + 1 then X
        else 0 := by
      intro i j
      change minor10 (Fin.succ i) (jm.succAbove j) = _
      change A (Fin.succAbove 1 (Fin.succ i)) (Fin.succ (jm.succAbove j)) = _
      rw [hA_def]
      have hsuccAbove1 : (Fin.succAbove (1 : Fin (m + 2)) (Fin.succ i)).val = i.val + 2 := by
        simp [Fin.succAbove, Fin.succ, Fin.castSucc]
      have hsuccAboveM : ∀ k : Fin m, (Fin.succAbove jm k).val = k.val := by
        intro k
        have hk : k.val < m := k.isLt
        simp only [Fin.succAbove, jm, Fin.castSucc, Fin.lt_def]
        simp only [Fin.val_castAdd, hk, ↓reduceIte]
      have hsucc_succAbove : (Fin.succ (Fin.succAbove jm j)).val = j.val + 1 := by
        simp [Fin.succ, hsuccAboveM j]
      change (companion p hp hn).charmatrix
          (Fin.cast hdeg.symm (Fin.succAbove 1 (Fin.succ i)))
          (Fin.cast hdeg.symm (Fin.succ (jm.succAbove j))) = _
      rw [companion_charmatrix]
      have hrow_val : (Fin.cast hdeg.symm
          (Fin.succAbove (1 : Fin (m + 2)) (Fin.succ i))).val = i.val + 2 := by
        simp only [Fin.val_cast, hsuccAbove1]
      have hcol_val : (Fin.cast hdeg.symm
          (Fin.succ (Fin.succAbove jm j))).val = j.val + 1 := by
        simp only [Fin.val_cast, hsucc_succAbove]
      have hdiag : (Fin.cast hdeg.symm
          (Fin.succAbove (1 : Fin (m + 2)) (Fin.succ i)) =
          Fin.cast hdeg.symm (Fin.succ (Fin.succAbove jm j))) ↔ j.val = i.val + 1 := by
        simp only [Fin.ext_iff, hrow_val, hcol_val]; omega
      have hsubdiag : (Fin.cast hdeg.symm (Fin.succ (Fin.succAbove jm j))).val + 1 =
          (Fin.cast hdeg.symm
          (Fin.succAbove (1 : Fin (m + 2)) (Fin.succ i))).val ↔ j.val = i.val := by
        simp only [hrow_val, hcol_val]; omega
      have hlastcol : ¬((Fin.cast hdeg.symm (Fin.succ (Fin.succAbove jm j))).val + 1
          = p.natDegree) := by
        simp only [hcol_val, hdeg]
        have hj : j.val < m := j.isLt
        omega
      by_cases hij : j.val = i.val
      · have hne : ¬(Fin.cast hdeg.symm (Fin.succAbove (1 : Fin (m + 2)) (Fin.succ i)) =
            Fin.cast hdeg.symm (Fin.succ (Fin.succAbove jm j))) := by
          rw [hdiag]; omega
        simp only [hne, ↓reduceIte, hsubdiag.mpr hij, hij]
      · by_cases hji1 : j.val = i.val + 1
        · have heq : Fin.cast hdeg.symm (Fin.succAbove (1 : Fin (m + 2)) (Fin.succ i)) =
              Fin.cast hdeg.symm (Fin.succ (Fin.succAbove jm j)) := hdiag.mpr hji1
          have hnotlast : ¬((Fin.cast hdeg.symm
              (Fin.succ (Fin.succAbove jm j))).val + 1 = p.natDegree) := by
            simp only [hcol_val, hdeg]
            have hj : j.val < m := j.isLt
            omega
          have hne_ji : ¬(i.val + 1 = i.val) := by omega
          simp only [heq, hnotlast, ↓reduceIte, hji1, hne_ji]
        · have hne : ¬(Fin.cast hdeg.symm (Fin.succAbove (1 : Fin (m + 2)) (Fin.succ i)) =
              Fin.cast hdeg.symm (Fin.succ (Fin.succAbove jm j))) := by
            rw [hdiag]; exact hji1
          have hnsub : ¬((Fin.cast hdeg.symm (Fin.succ (Fin.succAbove jm j))).val + 1 =
              (Fin.cast hdeg.symm (Fin.succAbove (1 : Fin (m + 2)) (Fin.succ i))).val) := by
            rw [hsubdiag]; exact hij
          simp only [hne, hnsub, hlastcol, ↓reduceIte, hij, hji1]
    have hS_tri : S.BlockTriangular id := by
      intro i j hij
      simp only [hS_entry]
      have hij' : j.val < i.val := hij
      have hne1 : j.val ≠ i.val := ne_of_lt hij'
      have hne2 : j.val ≠ i.val + 1 := by omega
      simp only [hne1, hne2, ↓reduceIte]
    rw [Matrix.det_of_upperTriangular hS_tri]
    simp only [hS_entry, ↓reduceIte]
    rw [Finset.prod_const, Finset.card_fin]
  rw [hsubminor_det]
  have h_pow : ((-1 : R[X]) ^ (m * 2)) = 1 := by
    rw [mul_comm, pow_mul]
    simp only [neg_one_sq, one_pow]
  ring_nf
  simp only [h_pow, mul_one]

/-- Determinant of minor00 equals p.divX via the induction hypothesis.

In the Laplace expansion, the minor obtained by deleting row 0 and column 0
has determinant equal to p.divX, because it equals charmatrix(companion(p.divX)). -/
private lemma companion_charpoly_minor00_det (p : R[X]) (hp : p.Monic) (hn : 0 < p.natDegree)
    (m : ℕ) (hdeg : p.natDegree = m + 2)
    (A : Matrix (Fin (m + 2)) (Fin (m + 2)) R[X])
    (hA_def : A = (companion p hp hn).charmatrix.submatrix
        (Fin.cast hdeg.symm) (Fin.cast hdeg.symm))
    (IH : ∀ (q : R[X]) (hq : q.Monic) (hq_pos : 0 < q.natDegree), q.natDegree = m + 1 →
      (companion q hq hq_pos).charpoly = q) :
    (A.submatrix (0 : Fin (m + 2)).succAbove Fin.succ).det = p.divX := by
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
  have hIH := IH p.divX hdivX_monic hdivX_pos hdivX_deg
  rw [Matrix.charpoly] at hIH
  have hminor_entry : ∀ i j : Fin (m + 1),
      A (Fin.succAbove (0 : Fin (m + 2)) i) (Fin.succ j) =
      (companion p.divX hdivX_monic hdivX_pos).charmatrix
        (Fin.cast hdivX_deg.symm i) (Fin.cast hdivX_deg.symm j) := by
    intro i j
    have hsuccAbove0 : (Fin.succAbove (0 : Fin (m + 2)) i).val = i.val + 1 := by
      simp [Fin.succAbove]
    rw [hA_def]
    simp only [Matrix.submatrix_apply]
    rw [companion_charmatrix, companion_charmatrix]
    have hrow_A : (Fin.cast hdeg.symm (Fin.succAbove (0 : Fin (m + 2)) i)).val = i.val + 1 := by
      simp only [Fin.val_cast, hsuccAbove0]
    have hcol_A : (Fin.cast hdeg.symm (Fin.succ j)).val = j.val + 1 := by simp
    have hrow_B : (Fin.cast hdivX_deg.symm i).val = i.val := by simp
    have hcol_B : (Fin.cast hdivX_deg.symm j).val = j.val := by simp
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
    have hlastrow_A : (Fin.cast hdeg.symm (Fin.succAbove 0 i)).val + 1 = p.natDegree ↔
        i.val = m := by
      simp only [hrow_A, hdeg]; omega
    have hlastrow_B : (Fin.cast hdivX_deg.symm i).val + 1 = p.divX.natDegree ↔
        i.val = m := by
      simp only [hrow_B, hdivX_deg]; omega
    have hlastcol_diag_A : (Fin.cast hdeg.symm (Fin.succ i)).val + 1 = p.natDegree ↔
        i.val = m := by
      simp only [Fin.val_cast, Fin.val_succ, hdeg]; omega
    have hlastcol_diag_B : (Fin.cast hdivX_deg.symm i).val + 1 = p.divX.natDegree ↔
        i.val = m := by
      simp only [hrow_B, hdivX_deg]; omega
    have hsubdiag_A : (Fin.cast hdeg.symm (Fin.succ j)).val + 1 =
        (Fin.cast hdeg.symm (Fin.succAbove 0 i)).val ↔ j.val + 1 = i.val := by
      simp only [hcol_A, hrow_A]; omega
    have hsubdiag_B : (Fin.cast hdivX_deg.symm j).val + 1 =
        (Fin.cast hdivX_deg.symm i).val ↔ j.val + 1 = i.val := by
      simp only [hcol_B, hrow_B]
    have hlastcol_A : (Fin.cast hdeg.symm (Fin.succ j)).val + 1 = p.natDegree ↔
        j.val = m := by
      simp only [hcol_A, hdeg]; omega
    have hlastcol_B : (Fin.cast hdivX_deg.symm j).val + 1 = p.divX.natDegree ↔
        j.val = m := by
      simp only [hcol_B, hdivX_deg]; omega
    have hcoeff : p.coeff (i.val + 1) = p.divX.coeff i.val := by
      rw [Polynomial.coeff_divX]
    have hcoeff_j : p.coeff (j.val + 1) = p.divX.coeff j.val := by
      rw [Polynomial.coeff_divX]
    by_cases hij : i = j
    · subst hij
      have hcond_A : Fin.cast hdeg.symm (Fin.succAbove 0 i) = Fin.cast hdeg.symm (Fin.succ i) :=
        hdiag_A.mpr rfl
      simp only [hcond_A, ↓reduceIte]
      by_cases hlast : i.val = m
      · have hcond1 : (Fin.cast hdeg.symm (Fin.succ i)).val + 1 = p.natDegree :=
          hlastcol_diag_A.mpr hlast
        have hcond2 : (Fin.cast hdivX_deg.symm i).val + 1 = p.divX.natDegree :=
          hlastcol_diag_B.mpr hlast
        simp only [hcond1, hcond2, ↓reduceIte]
        congr 1
        simp only [Fin.val_cast, Fin.val_succ, hcoeff]
      · have hcond1 : ¬((Fin.cast hdeg.symm (Fin.succ i)).val + 1 = p.natDegree) :=
          mt hlastcol_diag_A.mp hlast
        have hcond2 : ¬((Fin.cast hdivX_deg.symm i).val + 1 = p.divX.natDegree) :=
          mt hlastcol_diag_B.mp hlast
        simp only [hcond1, hcond2, ↓reduceIte]
    · have hcond_ne : ¬(Fin.cast hdeg.symm (Fin.succAbove 0 i) =
          Fin.cast hdeg.symm (Fin.succ j)) := mt hdiag_A.mp hij
      have hcond_ne' : ¬(Fin.cast hdivX_deg.symm i = Fin.cast hdivX_deg.symm j) :=
        mt hdiag_B.mp hij
      simp only [hcond_ne, hcond_ne', ↓reduceIte]
      by_cases hsubdiag : j.val + 1 = i.val
      · have hcond1 : (Fin.cast hdeg.symm (Fin.succ j)).val + 1 =
            (Fin.cast hdeg.symm (Fin.succAbove 0 i)).val := hsubdiag_A.mpr hsubdiag
        have hcond2 : (Fin.cast hdivX_deg.symm j).val + 1 =
            (Fin.cast hdivX_deg.symm i).val := hsubdiag_B.mpr hsubdiag
        simp only [hcond1, hcond2, ↓reduceIte]
      · have hcond1 : ¬((Fin.cast hdeg.symm (Fin.succ j)).val + 1 =
            (Fin.cast hdeg.symm (Fin.succAbove 0 i)).val) := mt hsubdiag_A.mp hsubdiag
        have hcond2 : ¬((Fin.cast hdivX_deg.symm j).val + 1 =
            (Fin.cast hdivX_deg.symm i).val) := mt hsubdiag_B.mp hsubdiag
        simp only [hcond1, hcond2, ↓reduceIte]
        by_cases hlastcol : j.val = m
        · have hcond3 : (Fin.cast hdeg.symm (Fin.succ j)).val + 1 = p.natDegree :=
            hlastcol_A.mpr hlastcol
          have hcond4 : (Fin.cast hdivX_deg.symm j).val + 1 = p.divX.natDegree :=
            hlastcol_B.mpr hlastcol
          simp only [hcond3, hcond4, ↓reduceIte, hrow_A, hrow_B, hcoeff]
        · have hcond3 : ¬((Fin.cast hdeg.symm (Fin.succ j)).val + 1 = p.natDegree) :=
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
  rw [hminor_eq]
  have heq : (companion p.divX hdivX_monic hdivX_pos).charmatrix.submatrix
      (Fin.cast hdivX_deg.symm) (Fin.cast hdivX_deg.symm) =
      (companion p.divX hdivX_monic hdivX_pos).charmatrix.submatrix
      (finCongr hdivX_deg.symm) (finCongr hdivX_deg.symm) := by rfl
  rw [heq, Matrix.det_submatrix_equiv_self (finCongr hdivX_deg.symm)]
  exact hIH

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
  | zero => exact companion_charpoly_base_case p hp hn hn_eq
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
    -- Get column structure from helper lemma
    obtain ⟨hA00, hA10, hA_other⟩ := companion_charmatrix_col_structure p hp hn m hdeg A hA_def
    -- Simplify the sum to just two terms
    have hsum :
        ∑ i : Fin (m + 2), (-1) ^ (i : ℕ) * A i 0 * (A.submatrix i.succAbove Fin.succ).det =
        (-1) ^ (0 : ℕ) * A 0 0 * (A.submatrix (0 : Fin (m + 2)).succAbove Fin.succ).det +
        (-1) ^ (1 : ℕ) * A 1 0 *
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
      simp only [Fin.val_zero, Fin.val_one]
    rw [hsum, hA00, hA10]
    simp only [pow_zero, one_mul, pow_one, mul_neg, mul_one, neg_neg]
    -- Express p in terms of divX
    have hp_eq : p = X * p.divX + Polynomial.C (p.coeff 0) := by
      rw [Polynomial.ext_iff]
      intro k
      simp only [Polynomial.coeff_add, Polynomial.coeff_C]
      rcases k with _ | k
      · simp [Polynomial.divX]
      · have hk_ne : k + 1 ≠ 0 := Nat.succ_ne_zero k
        simp only [hk_ne, ↓reduceIte, add_zero, Polynomial.coeff_X_mul, Polynomial.coeff_divX]
    rw [hp_eq]
    congr 1
    · -- X * det(minor00) = X * p.divX
      congr 1
      exact companion_charpoly_minor00_det p hp hn m hdeg A hA_def IH
    · -- det(minor10) = C(p.coeff 0)
      exact companion_charpoly_minor10_det p hp hn m hdeg A hA_def

/-! ### Polynomial evaluation -/

@[blueprint "lem:companion-aeval-zero"
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
