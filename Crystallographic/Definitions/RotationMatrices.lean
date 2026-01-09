/-
Copyright (c) 2026 Eric Vergo. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Eric Vergo
-/
import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# Rotation Matrix Definitions

This file defines explicit integer matrices that achieve the crystallographic orders.
The proofs that these matrices have the claimed orders are in Proofs/RotationMatrices.lean.

## Main definitions

* `rotationMatrix1` - The identity matrix (order 1)
* `rotationMatrix2` - The negative identity matrix (order 2)
* `rotationMatrix3` - A 2x2 integer matrix with order 3
* `rotationMatrix4` - A 2x2 integer matrix with order 4
* `rotationMatrix6` - A 2x2 integer matrix with order 6
-/

namespace Crystallographic

open Matrix

/-- The identity matrix (order 1) -/
def rotationMatrix1 : Matrix (Fin 2) (Fin 2) ℤ := 1

/-- Rotation by 180 degrees (order 2): -I -/
def rotationMatrix2 : Matrix (Fin 2) (Fin 2) ℤ := -1

/-- Rotation by 90 degrees (order 4): [[0, -1], [1, 0]] -/
def rotationMatrix4 : Matrix (Fin 2) (Fin 2) ℤ := !![0, -1; 1, 0]

/-- Rotation by 120 degrees in hexagonal basis (order 3): [[0, -1], [1, -1]] -/
def rotationMatrix3 : Matrix (Fin 2) (Fin 2) ℤ := !![0, -1; 1, -1]

/-- Rotation by 60 degrees in hexagonal basis (order 6): [[1, -1], [1, 0]] -/
def rotationMatrix6 : Matrix (Fin 2) (Fin 2) ℤ := !![1, -1; 1, 0]

end Crystallographic
