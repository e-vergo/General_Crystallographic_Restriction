/-
Copyright (c) 2026 Eric Vergo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo
-/
import Architect
import Mathlib.Algebra.CharP.Two
import Mathlib.Data.Matrix.Block

/-!
# Orders of Integer Matrices

This file defines the set of possible orders for N×N integer matrices with finite order,
and proves basic properties about this set.

## Main definitions

* `integerMatrixOrders N` - The set of orders achievable by N×N integer matrices with finite order.
* `embedMatrixSum` - Block diagonal embedding of an M×M matrix into (M+K)×(M+K).
* `blockDiag2` - Block diagonal of two matrices.

## Main results

* `one_mem_integerMatrixOrders` - The identity matrix has order 1.
* `two_mem_integerMatrixOrders` - Negation of identity has order 2 (for N ≥ 1).
* `integerMatrixOrders_mono` - Monotonicity: M ≤ N implies OrdM ⊆ OrdN.
* `divisor_mem_integerMatrixOrders` - Divisibility: if m ∈ OrdN and d ∣ m, then d ∈ OrdN.

## References

* Sasse, R. (2020). "Crystallographic Groups"

## Tags

integer matrix, finite order, matrix order, block diagonal, embedding
-/

namespace Crystallographic

open Matrix

/-- The set of possible orders for N×N integer matrices with finite order.
An integer `m` is in this set if there exists an N×N integer matrix `A` such that
`orderOf A = m` and `m > 0` (equivalently, `A` has finite order). -/
@[blueprint
  "integerMatrixOrders-def"
  (statement := /-- The set $\mathrm{Ord}_N$ of possible orders for $N \times N$ integer matrices
  with finite order. A natural number $m$ is in this set if there exists an $N \times N$ integer matrix
  $A$ with order $m$. -/)]
def integerMatrixOrders (N : ℕ) : Set ℕ :=
  {m | ∃ A : Matrix (Fin N) (Fin N) ℤ, orderOf A = m ∧ 0 < m}

/-- The identity matrix has order 1, so 1 ∈ integerMatrixOrders N for any N. -/
@[blueprint "lem:one-mem-orders"
  (statement := /-- Order $1$ is achievable in any dimension. -/)
  (proof := /-- The identity matrix $I$ has order $1$ in any dimension. -/)]
lemma one_mem_integerMatrixOrders (N : ℕ) : 1 ∈ integerMatrixOrders N :=
  ⟨1, orderOf_one, by norm_num⟩

/-- The ring characteristic of integer matrices is 0 for N ≥ 1. -/
lemma ringChar_matrix_int (N : ℕ) [NeZero N] : ringChar (Matrix (Fin N) (Fin N) ℤ) = 0 := by
  rw [ringChar.eq_iff]
  refine ⟨fun n => ⟨fun hn => ?_, fun h => by simp [Nat.zero_dvd.mp h]⟩⟩
  have := congrFun (congrFun hn ⟨0, NeZero.pos N⟩) ⟨0, NeZero.pos N⟩
  simp only [Matrix.natCast_apply] at this
  exact Nat.zero_dvd.mpr (Int.ofNat_eq_zero.mp this)

/-- For N ≥ 1, the negation of the identity matrix has order 2. -/
@[blueprint "lem:two-mem-orders"
  (statement := /-- Order $2$ is achievable for $N \geq 1$. -/)
  (proof := /-- The matrix $-I$ satisfies $(-I)^2 = I$ and $-I \neq I$ for $N \geq 1$,
  so it has order $2$. -/)]
lemma two_mem_integerMatrixOrders (N : ℕ) [NeZero N] : 2 ∈ integerMatrixOrders N := by
  use -1
  constructor
  · rw [orderOf_neg_one, ringChar_matrix_int, if_neg (by norm_num : (0 : ℕ) ≠ 2)]
  · norm_num

/-- The canonical block diagonal embedding of an M×M matrix into an (M+K)×(M+K) matrix
using Sum types. Places the matrix in the upper-left block and identity in the lower-right. -/
def embedMatrixSum {M K : ℕ} {R : Type*} [Zero R] [One R] (A : Matrix (Fin M) (Fin M) R) :
    Matrix (Fin M ⊕ Fin K) (Fin M ⊕ Fin K) R :=
  Matrix.fromBlocks A 0 0 1

/-- The embedded identity is identity. -/
@[simp]
lemma embedMatrixSum_one {M K : ℕ} {R : Type*} [Zero R] [One R] :
    embedMatrixSum (1 : Matrix (Fin M) (Fin M) R) =
    (1 : Matrix (Fin M ⊕ Fin K) (Fin M ⊕ Fin K) R) := by
  simp only [embedMatrixSum, fromBlocks_one]

/-- The embedding preserves multiplication. -/
@[simp]
lemma embedMatrixSum_mul {M K : ℕ} {R : Type*} [Semiring R] (A B : Matrix (Fin M) (Fin M) R) :
    embedMatrixSum (K := K) (A * B) = embedMatrixSum A * embedMatrixSum B := by
  simp only [embedMatrixSum]
  rw [fromBlocks_multiply]
  simp

/-- The embedding is a monoid homomorphism. -/
def embedMatrixSum.monoidHom (M K : ℕ) (R : Type*) [Semiring R] :
    Matrix (Fin M) (Fin M) R →* Matrix (Fin M ⊕ Fin K) (Fin M ⊕ Fin K) R where
  toFun := embedMatrixSum
  map_one' := embedMatrixSum_one
  map_mul' := embedMatrixSum_mul

/-- The embedding is injective. -/
lemma embedMatrixSum.monoidHom_injective (M K : ℕ) (R : Type*) [Semiring R] :
    Function.Injective (embedMatrixSum.monoidHom M K R) := by
  intro A B hAB
  simp only [embedMatrixSum.monoidHom, MonoidHom.coe_mk, OneHom.coe_mk] at hAB
  ext i j
  have h := congrFun (congrFun hAB (Sum.inl i)) (Sum.inl j)
  simp only [embedMatrixSum, fromBlocks_apply₁₁] at h
  exact h

/-- The embedding preserves order. -/
lemma orderOf_embedMatrixSum_eq {M K : ℕ} (A : Matrix (Fin M) (Fin M) ℤ) :
    orderOf (embedMatrixSum (K := K) A) = orderOf A :=
  orderOf_injective (embedMatrixSum.monoidHom M K ℤ) (embedMatrixSum.monoidHom_injective M K ℤ) A

/-- Alternative set of orders using Sum-indexed matrices for convenience.

This is equivalent to integerMatrixOrders (M + K) but uses Sum types for indexing,
which simplifies working with block diagonal matrices. -/
def integerMatrixOrdersSum (M K : ℕ) : Set ℕ :=
  {m | ∃ A : Matrix (Fin M ⊕ Fin K) (Fin M ⊕ Fin K) ℤ, orderOf A = m ∧ 0 < m}

/-- Orders achievable for M×M matrices are achievable for (M⊕K)-indexed matrices. -/
theorem integerMatrixOrders_subset_sum (M K : ℕ) :
    integerMatrixOrders M ⊆ integerMatrixOrdersSum M K :=
  fun _ ⟨A, hA_ord, hA_pos⟩ => ⟨embedMatrixSum A, by rw [orderOf_embedMatrixSum_eq, hA_ord], hA_pos⟩

/-- Reindexing defines a monoid isomorphism.

Given an equivalence e : m ≃ n between index types, this provides an isomorphism
between the corresponding matrix monoids that preserves multiplication.

Note: Mathlib has `Matrix.reindexAlgEquiv` which provides an algebra equivalence,
but we only need the multiplicative structure here. Using `MulEquiv` directly
avoids requiring unnecessary algebra instances and keeps the API minimal. -/
def reindexMonoidEquiv {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    {R : Type*} [Semiring R] (e : m ≃ n) : Matrix m m R ≃* Matrix n n R where
  toFun A := A.submatrix e.symm e.symm
  invFun A := A.submatrix e e
  left_inv A := by simp only [submatrix_submatrix, Equiv.symm_comp_self, submatrix_id_id]
  right_inv A := by simp only [submatrix_submatrix, Equiv.self_comp_symm, submatrix_id_id]
  map_mul' A B := by
    simp only [← submatrix_mul_equiv (M := A) (N := B) (e₁ := e.symm) (e₂ := e.symm)]

/-- Monotonicity: if M <= N, then any order achievable for M x M matrices is also achievable
for N x N matrices.

The construction pads the M x M matrix with an identity block in the lower-right corner. -/
@[blueprint "lem:orders-mono"
  (statement := /-- $\mathrm{Ord}_M \subseteq \mathrm{Ord}_N$ for $M \leq N$.
  \uses{integerMatrixOrders-def} -/)
  (proof := /-- Given $M \leq N$ and $A \in M_M(\mathbb{Z})$ with order $m$, embed $A$ as the
  top-left block of an $N \times N$ matrix with identity in the bottom-right. The order is
  preserved. -/)]
theorem integerMatrixOrders_mono {M N : ℕ} (hMN : M ≤ N) :
    integerMatrixOrders M ⊆ integerMatrixOrders N := by
  intro m hm
  simp only [integerMatrixOrders, Set.mem_setOf_eq] at hm ⊢
  obtain ⟨A, hA_ord, hA_pos⟩ := hm
  -- N = M + (N - M)
  let K := N - M
  have hN : N = M + K := (Nat.add_sub_cancel' hMN).symm
  -- First embed A into (Fin M ⊕ Fin K)-indexed matrix
  let A' : Matrix (Fin M ⊕ Fin K) (Fin M ⊕ Fin K) ℤ := embedMatrixSum A
  -- Then reindex to Fin N using the equivalence
  let e : Fin N ≃ Fin M ⊕ Fin K := hN ▸ finSumFinEquiv.symm
  let A'' : Matrix (Fin N) (Fin N) ℤ := (reindexMonoidEquiv e).symm A'
  use A''
  constructor
  · simp only [A'']
    have h1 : orderOf ((reindexMonoidEquiv e).symm A') = orderOf A' :=
      MulEquiv.orderOf_eq (reindexMonoidEquiv e).symm A'
    rw [h1, orderOf_embedMatrixSum_eq, hA_ord]
  · exact hA_pos

/-! ## Block diagonal matrix infrastructure -/

/-- Block diagonal of two matrices: places A in upper-left and B in lower-right. -/
@[blueprint "def:blockDiag2"
  (statement := /-- Block diagonal matrix $\mathrm{diag}(A, B)$ of dimension $M + N$. -/)]
def blockDiag2 {M K : ℕ} {R : Type*} [Zero R]
    (A : Matrix (Fin M) (Fin M) R) (B : Matrix (Fin K) (Fin K) R) :
    Matrix (Fin M ⊕ Fin K) (Fin M ⊕ Fin K) R :=
  Matrix.fromBlocks A 0 0 B

/-- Block diagonal of identity matrices is the identity. -/
@[simp]
lemma blockDiag2_one {M K : ℕ} {R : Type*} [Zero R] [One R] :
    blockDiag2 (1 : Matrix (Fin M) (Fin M) R) (1 : Matrix (Fin K) (Fin K) R) =
    (1 : Matrix (Fin M ⊕ Fin K) (Fin M ⊕ Fin K) R) :=
  Matrix.fromBlocks_one

/-- Block diagonal preserves multiplication. -/
@[simp]
lemma blockDiag2_mul {M K : ℕ} {R : Type*} [Semiring R]
    (A A' : Matrix (Fin M) (Fin M) R) (B B' : Matrix (Fin K) (Fin K) R) :
    blockDiag2 (A * A') (B * B') = blockDiag2 A B * blockDiag2 A' B' := by
  simp only [blockDiag2, Matrix.fromBlocks_multiply]
  congr 1 <;> simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]

/-- The monoid homomorphism that embeds a pair of block-diagonal matrices into a larger matrix. -/
def blockDiag2.prodMonoidHom (M K : ℕ) (R : Type*) [Semiring R] :
    Matrix (Fin M) (Fin M) R × Matrix (Fin K) (Fin K) R →*
    Matrix (Fin M ⊕ Fin K) (Fin M ⊕ Fin K) R where
  toFun := fun p => blockDiag2 p.1 p.2
  map_one' := blockDiag2_one
  map_mul' := fun _ _ => blockDiag2_mul _ _ _ _

/-- Block diagonal is one iff both components are one. -/
@[blueprint "lem:blockDiag2-eq-one"
  (statement := /-- $\mathrm{diag}(A, B) = 1 \iff A = 1 \land B = 1$. \uses{def:blockDiag2} -/)
  (proof := /-- The block diagonal matrix equals $I$ iff both diagonal blocks equal their
  respective identities. -/)]
lemma blockDiag2_eq_one_iff {M K : ℕ} {R : Type*} [Zero R] [One R]
    (A : Matrix (Fin M) (Fin M) R) (B : Matrix (Fin K) (Fin K) R) :
    blockDiag2 A B = 1 ↔ A = 1 ∧ B = 1 := by
  rw [← blockDiag2_one]
  simp only [blockDiag2, Matrix.fromBlocks_inj]
  tauto

/-- Power of block diagonal distributes to each block.

(blockDiag2 A B)^k = blockDiag2 (A^k) (B^k). -/
@[blueprint "lem:blockDiag2-pow"
  (statement := /-- $\mathrm{diag}(A, B)^n = \mathrm{diag}(A^n, B^n)$. \uses{def:blockDiag2} -/)
  (proof := /-- By induction on $n$: the block structure is preserved under multiplication, and
  $\mathrm{diag}(A, B) \cdot \mathrm{diag}(A', B') = \mathrm{diag}(AA', BB')$. -/)]
lemma blockDiag2_pow {M K : ℕ} {R : Type*} [Semiring R]
    (A : Matrix (Fin M) (Fin M) R) (B : Matrix (Fin K) (Fin K) R) (k : ℕ) :
    (blockDiag2 A B) ^ k = blockDiag2 (A ^ k) (B ^ k) := by
  simp only [blockDiag2]
  exact Matrix.fromBlocks_diagonal_pow A B k

end Crystallographic
