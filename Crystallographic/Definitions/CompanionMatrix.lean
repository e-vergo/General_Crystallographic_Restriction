/-
Copyright (c) 2026 Eric Vergo. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Eric Vergo
-/
import Mathlib.Algebra.Polynomial.Degree.Definitions
import Mathlib.Data.Matrix.Basic

/-!
# Companion Matrix Definition

This file defines the companion matrix of a monic polynomial.
The proofs of its properties are in Proofs/CompanionMatrix.lean.

## Main definitions

* `companion` - The companion matrix of a monic polynomial
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
def companion (p : R[X]) (_hp : p.Monic) (_hn : 0 < p.natDegree) :
    Matrix (Fin p.natDegree) (Fin p.natDegree) R :=
  Matrix.of fun i j =>
    if j.val + 1 = i.val then 1
    else if j.val + 1 = p.natDegree then -p.coeff i.val
    else 0

end Crystallographic
