/-
Copyright (c) 2026 Eric Vergo. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Eric Vergo
-/
import Architect
import Crystallographic.FiniteOrder.Basic

/-!
# Order of Block Diagonal Matrices

This file proves that the order of a block diagonal matrix is the lcm of the orders
of the blocks, and uses this to prove closure properties of `integerMatrixOrders`.

## Main results

* `orderOf_blockDiag2` - Order of block diagonal is lcm of block orders.
* `lcm_mem_integerMatrixOrders` - If m₁ ∈ Ord_M and m₂ ∈ Ord_K, then lcm(m₁,m₂) ∈ Ord_{M+K}.
* `mul_mem_integerMatrixOrders_of_coprime` - For coprime orders, the product is in Ord_{M+K}.

## References

* Sasse, R. (2020). "Crystallographic Groups"
-/

namespace Crystallographic

open Matrix

/-- Order of block diagonal is lcm of orders.

Since blockDiag2 A B acts independently on the two blocks, it equals 1 iff both A^k = 1
and B^k = 1, which happens at k = lcm(orderOf A, orderOf B). -/
@[blueprint "thm:orderOf-blockDiag2"
  (statement := /-- The order of $\mathrm{diag}(A, B)$ equals $\mathrm{lcm}(\mathrm{ord}(A),
  \mathrm{ord}(B))$. \uses{def:blockDiag2, lem:blockDiag2-pow, lem:blockDiag2-eq-one} -/)
  (proof := /-- The order is the least $n$ such that $A^n = I$ and $B^n = I$, which is exactly
  $\mathrm{lcm}(\mathrm{ord}(A), \mathrm{ord}(B))$. -/)]
theorem orderOf_blockDiag2 {M K : ℕ}
    (A : Matrix (Fin M) (Fin M) ℤ) (B : Matrix (Fin K) (Fin K) ℤ) :
    orderOf (blockDiag2 A B) = Nat.lcm (orderOf A) (orderOf B) := by
  -- The order of (A, B) in the product monoid is lcm(orderOf A, orderOf B)
  -- We show blockDiag2 induces an injective monoid hom from the product
  let φ : Matrix (Fin M) (Fin M) ℤ × Matrix (Fin K) (Fin K) ℤ →*
      Matrix (Fin M ⊕ Fin K) (Fin M ⊕ Fin K) ℤ :=
    { toFun := fun p => blockDiag2 p.1 p.2
      map_one' := blockDiag2_one
      map_mul' := fun p q => blockDiag2_mul _ _ _ _ }
  have hinj : Function.Injective φ := by
    intro p q hpq
    have h1 := Matrix.fromBlocks_inj.mp hpq
    exact Prod.ext h1.1 h1.2.2.2
  have hφ : φ (A, B) = blockDiag2 A B := rfl
  rw [← hφ, orderOf_injective φ hinj (A, B), Prod.orderOf]

/-- Block diagonal construction for integer matrix orders.
    If m₁ ∈ integerMatrixOrders M and m₂ ∈ integerMatrixOrders K,
    then lcm(m₁, m₂) ∈ integerMatrixOrders (M + K). -/
@[blueprint "lem:lcm-mem-orders"
  (statement := /-- If $m, n \in \mathrm{Ord}_N$ are coprime, then $mn \in \mathrm{Ord}_{2N}$.
  \uses{thm:orderOf-blockDiag2} -/)
  (proof := /-- Given matrices $A, B$ achieving orders $m_1, m_2$ in dimensions $M, K$, the block
  diagonal $\mathrm{diag}(A, B)$ has order $\mathrm{lcm}(m_1, m_2)$ in dimension $M + K$. -/)]
theorem lcm_mem_integerMatrixOrders {M K m₁ m₂ : ℕ}
    (h₁ : m₁ ∈ integerMatrixOrders M) (h₂ : m₂ ∈ integerMatrixOrders K) :
    Nat.lcm m₁ m₂ ∈ integerMatrixOrders (M + K) := by
  obtain ⟨A, hA_ord, hA_pos⟩ := h₁
  obtain ⟨B, hB_ord, hB_pos⟩ := h₂
  -- Construct block diagonal matrix
  let C := blockDiag2 A B
  -- Reindex from Sum to Fin (M + K)
  let e : Fin (M + K) ≃ Fin M ⊕ Fin K := finSumFinEquiv.symm
  let C' : Matrix (Fin (M + K)) (Fin (M + K)) ℤ := (reindexMonoidEquiv e).symm C
  use C'
  constructor
  · have h1 : orderOf C' = orderOf C :=
      MulEquiv.orderOf_eq (reindexMonoidEquiv e).symm C
    rw [h1, orderOf_blockDiag2, hA_ord, hB_ord]
  · exact Nat.lcm_pos hA_pos hB_pos

/-- For coprime m₁, m₂, if m₁ ∈ integerMatrixOrders M and m₂ ∈ integerMatrixOrders K,
    then m₁ * m₂ ∈ integerMatrixOrders (M + K). -/
@[blueprint "lem:mul-mem-orders-coprime"
  (statement := /-- Product of coprime achievable orders is achievable.
  \uses{lem:lcm-mem-orders} -/)
  (proof := /-- For coprime $m_1, m_2$, we have $\mathrm{lcm}(m_1, m_2) = m_1 m_2$, so this
  follows from the lcm result. -/)]
theorem mul_mem_integerMatrixOrders_of_coprime {M K m₁ m₂ : ℕ}
    (h₁ : m₁ ∈ integerMatrixOrders M) (h₂ : m₂ ∈ integerMatrixOrders K)
    (hcop : Nat.Coprime m₁ m₂) :
    m₁ * m₂ ∈ integerMatrixOrders (M + K) := by
  rw [← hcop.lcm_eq_mul]
  exact lcm_mem_integerMatrixOrders h₁ h₂

end Crystallographic
