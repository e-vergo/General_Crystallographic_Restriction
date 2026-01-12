/-
Copyright (c) 2026 Eric Vergo. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Eric Vergo
-/
import Architect

import Crystallographic.Definitions.IntegerMatrixOrder
import Crystallographic.Definitions.RotationMatrices

/-!
# Rotation Matrix Order Proofs

This file proves that the rotation matrices defined in Definitions/RotationMatrices.lean
have their claimed orders, demonstrating that the crystallographic orders are achievable
by 2x2 integer matrices.

## Main results

* `orderOf_rotationMatrix1` - rotationMatrix1 has order 1
* `orderOf_rotationMatrix2` - rotationMatrix2 has order 2
* `orderOf_rotationMatrix3` - rotationMatrix3 has order 3
* `orderOf_rotationMatrix4` - rotationMatrix4 has order 4
* `orderOf_rotationMatrix6` - rotationMatrix6 has order 6
* `*_mem_integerMatrixOrders_two` - Orders 1, 2, 3, 4, 6 are achievable

## References

* Sasse, R. (2020). "Crystallographic Groups"
-/

namespace Crystallographic

open Matrix

/-! ## Order computations for rotationMatrix1 -/

/-- The identity matrix has order 1 -/
theorem orderOf_rotationMatrix1 : orderOf rotationMatrix1 = 1 := by
  simp [rotationMatrix1, orderOf_one]

/-! ## Order computations for rotationMatrix2 -/

/-- rotationMatrix2^2 = 1 -/
lemma rotationMatrix2_sq : rotationMatrix2 ^ 2 = 1 := by
  simp [rotationMatrix2, sq]

/-- The 180 degree rotation matrix has order 2 -/
theorem orderOf_rotationMatrix2 : orderOf rotationMatrix2 = 2 := by
  simp only [rotationMatrix2]
  rw [orderOf_neg_one, ringChar_matrix_int, if_neg (by norm_num : (0 : ℕ) ≠ 2)]

/-! ## Order computations for rotationMatrix4 -/

/-- rotationMatrix4^2 = -1 -/
lemma rotationMatrix4_sq : rotationMatrix4 ^ 2 = -1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> native_decide

/-- rotationMatrix4^4 = 1 -/
lemma rotationMatrix4_pow4 : rotationMatrix4 ^ 4 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> native_decide

/-- rotationMatrix4 is not the identity -/
lemma rotationMatrix4_ne_one : rotationMatrix4 ≠ 1 := by
  intro h
  have : rotationMatrix4 0 1 = (1 : Matrix (Fin 2) (Fin 2) ℤ) 0 1 := by rw [h]
  simp [rotationMatrix4] at this

/-- rotationMatrix4^2 is not the identity -/
lemma rotationMatrix4_sq_ne_one : rotationMatrix4 ^ 2 ≠ 1 := by
  rw [rotationMatrix4_sq]
  intro h
  have : (-1 : Matrix (Fin 2) (Fin 2) ℤ) 0 0 = (1 : Matrix (Fin 2) (Fin 2) ℤ) 0 0 := by rw [h]
  simp at this

/-- rotationMatrix4^3 is not the identity -/
lemma rotationMatrix4_pow3_ne_one : rotationMatrix4 ^ 3 ≠ 1 := by
  simp only [rotationMatrix4, Ne, ← Matrix.ext_iff]
  push_neg
  use 0, 1
  native_decide

/-- The 90 degree rotation matrix has order 4 -/
theorem orderOf_rotationMatrix4 : orderOf rotationMatrix4 = 4 := by
  rw [orderOf_eq_iff (by norm_num : 0 < 4)]
  constructor
  · exact rotationMatrix4_pow4
  · intro m hm hm_lt
    interval_cases m
    · simp only [pow_one]; exact rotationMatrix4_ne_one
    · exact rotationMatrix4_sq_ne_one
    · exact rotationMatrix4_pow3_ne_one

/-! ## Order computations for rotationMatrix3 -/

/-- rotationMatrix3^3 = 1 -/
lemma rotationMatrix3_pow3 : rotationMatrix3 ^ 3 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> native_decide

/-- rotationMatrix3 is not the identity -/
lemma rotationMatrix3_ne_one : rotationMatrix3 ≠ 1 := by
  intro h
  have : rotationMatrix3 0 1 = (1 : Matrix (Fin 2) (Fin 2) ℤ) 0 1 := by rw [h]
  simp [rotationMatrix3] at this

/-- rotationMatrix3^2 is not the identity -/
lemma rotationMatrix3_sq_ne_one : rotationMatrix3 ^ 2 ≠ 1 := by
  simp only [rotationMatrix3, Ne, ← Matrix.ext_iff]
  push_neg
  use 0, 1
  native_decide

/-- The 120 degree rotation matrix has order 3 -/
theorem orderOf_rotationMatrix3 : orderOf rotationMatrix3 = 3 := by
  rw [orderOf_eq_iff (by norm_num : 0 < 3)]
  constructor
  · exact rotationMatrix3_pow3
  · intro m hm hm_lt
    interval_cases m
    · simp only [pow_one]; exact rotationMatrix3_ne_one
    · exact rotationMatrix3_sq_ne_one

/-! ## Order computations for rotationMatrix6 -/

/-- rotationMatrix6^6 = 1 -/
lemma rotationMatrix6_pow6 : rotationMatrix6 ^ 6 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> native_decide

/-- rotationMatrix6 is not the identity -/
lemma rotationMatrix6_ne_one : rotationMatrix6 ≠ 1 := by
  intro h
  have : rotationMatrix6 0 1 = (1 : Matrix (Fin 2) (Fin 2) ℤ) 0 1 := by rw [h]
  simp [rotationMatrix6] at this

/-- rotationMatrix6^2 is not the identity -/
lemma rotationMatrix6_sq_ne_one : rotationMatrix6 ^ 2 ≠ 1 := by
  simp only [rotationMatrix6, Ne, ← Matrix.ext_iff]
  push_neg
  use 0, 1
  native_decide

/-- rotationMatrix6^3 is not the identity -/
lemma rotationMatrix6_pow3_ne_one : rotationMatrix6 ^ 3 ≠ 1 := by
  simp only [rotationMatrix6, Ne, ← Matrix.ext_iff]
  push_neg
  use 0, 0
  native_decide

/-- rotationMatrix6^4 is not the identity -/
lemma rotationMatrix6_pow4_ne_one : rotationMatrix6 ^ 4 ≠ 1 := by
  simp only [rotationMatrix6, Ne, ← Matrix.ext_iff]
  push_neg
  use 0, 1
  native_decide

/-- rotationMatrix6^5 is not the identity -/
lemma rotationMatrix6_pow5_ne_one : rotationMatrix6 ^ 5 ≠ 1 := by
  simp only [rotationMatrix6, Ne, ← Matrix.ext_iff]
  push_neg
  use 0, 0
  native_decide

/-- The 60 degree rotation matrix has order 6 -/
theorem orderOf_rotationMatrix6 : orderOf rotationMatrix6 = 6 := by
  rw [orderOf_eq_iff (by norm_num : 0 < 6)]
  constructor
  · exact rotationMatrix6_pow6
  · intro m hm hm_lt
    interval_cases m
    · simp only [pow_one]; exact rotationMatrix6_ne_one
    · exact rotationMatrix6_sq_ne_one
    · exact rotationMatrix6_pow3_ne_one
    · exact rotationMatrix6_pow4_ne_one
    · exact rotationMatrix6_pow5_ne_one

/-! ## Membership proofs -/

-- Note: `one_mem_integerMatrixOrders` and `two_mem_integerMatrixOrders`
-- are defined in IntegerMatrixOrder.lean

/-- Order 3 is achievable by a 2x2 integer matrix -/
@[blueprint "thm:order3-achievable"
  (statement := /-- Order $3$ is achievable by a $2 \times 2$ integer matrix.
  The witness is the rotation matrix $R_3$.
  \uses{def:rotation-matrix-3} --/)]
theorem three_mem_integerMatrixOrders_two : 3 ∈ integerMatrixOrders 2 := by
  use rotationMatrix3
  exact ⟨orderOf_rotationMatrix3, by norm_num⟩

/-- Order 4 is achievable by a 2x2 integer matrix -/
@[blueprint "thm:order4-achievable"
  (statement := /-- Order $4$ is achievable by a $2 \times 2$ integer matrix.
  The witness is the rotation matrix $R_4$.
  \uses{def:rotation-matrix-4} --/)]
theorem four_mem_integerMatrixOrders_two : 4 ∈ integerMatrixOrders 2 := by
  use rotationMatrix4
  exact ⟨orderOf_rotationMatrix4, by norm_num⟩

/-- Order 6 is achievable by a 2x2 integer matrix -/
@[blueprint "thm:order6-achievable"
  (statement := /-- Order $6$ is achievable by a $2 \times 2$ integer matrix.
  The witness is the rotation matrix $R_6$.
  \uses{def:rotation-matrix-6} --/)]
theorem six_mem_integerMatrixOrders_two : 6 ∈ integerMatrixOrders 2 := by
  use rotationMatrix6
  exact ⟨orderOf_rotationMatrix6, by norm_num⟩

end Crystallographic
