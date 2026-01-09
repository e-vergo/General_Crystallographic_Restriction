/-
Copyright (c) 2026 Eric Vergo. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Eric Vergo
-/
import Crystallographic.MainTheorem
import Crystallographic.Proofs.CrystallographicRestriction

/-!
# The Crystallographic Restriction Theorem - Proof

This file proves the crystallographic restriction theorem by combining:
- The forward direction: if m ∈ integerMatrixOrders N then psi(m) ≤ N
- The backward direction: if psi(m) ≤ N then m ∈ integerMatrixOrders N
-/

namespace Crystallographic

/-- The crystallographic restriction theorem: an N×N integer matrix can have
finite order m if and only if psi(m) ≤ N. -/
theorem mainTheorem : StatementOfTheorem :=
  fun N m hm hNm =>
    ⟨psi_le_of_mem_integerMatrixOrders N m hm,
     fun hpsi => mem_integerMatrixOrders_of_psi_le N m hm hpsi hNm⟩

end Crystallographic
