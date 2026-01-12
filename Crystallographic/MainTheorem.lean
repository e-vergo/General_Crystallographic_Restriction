/-
Copyright (c) 2026 Eric Vergo. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Eric Vergo
-/
import Crystallographic.Definitions.IntegerMatrixOrder
import Crystallographic.Definitions.Psi
import Architect

/-!
# The Crystallographic Restriction Theorem - Statement

This file contains the statement of the crystallographic restriction theorem.

## Main Result

The crystallographic restriction theorem characterizes which orders are achievable
by N×N integer matrices: an order m is achievable if and only if psi(m) ≤ N.

The psi function is defined as:
- psi(1) = psi(2) = 0
- For other m, psi(m) = sum over prime power factors p^k of phi(p^k),
  except psi(2) = 0 contributes nothing.

## References

* Sasse, R. (2020). "Crystallographic Groups"
-/

namespace Crystallographic

blueprint_comment /--
\section{Main Theorem}
-/

/-- The crystallographic restriction theorem states that an N×N integer matrix
can have finite order m if and only if psi(m) ≤ N.

This characterizes exactly which rotation orders are possible in N-dimensional
crystallographic groups. -/
@[blueprint
  "thm:crystallographic-restriction"
  (statement := /-- The crystallographic restriction theorem: an $N \times N$ integer matrix
  can have finite order $m$ if and only if $\psi(m) \leq N$. -/)]
def StatementOfTheorem : Prop :=
  ∀ N m : ℕ, 0 < m → (m = 1 ∨ 0 < N) → (m ∈ integerMatrixOrders N ↔ psi m ≤ N)

end Crystallographic
