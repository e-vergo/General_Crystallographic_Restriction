/-
Copyright (c) 2026 Eric Vergo. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Eric Vergo
-/
import Mathlib.Algebra.CharP.Two
import Mathlib.Data.Matrix.Block
import Architect

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
-/

namespace Crystallographic

open Matrix

blueprint_comment /--
\section{Integer Matrix Orders}
-/

/-- The set of possible orders for N×N integer matrices with finite order.
An integer `m` is in this set if there exists an N×N integer matrix `A` such that
`orderOf A = m` and `m > 0` (equivalently, `A` has finite order). -/
@[blueprint
  "integerMatrixOrders-def"
  (statement := /-- The set $\mathrm{Ord}_N$ of possible orders for $N \times N$ integer matrices
  with finite order. An integer $m$ is in this set if there exists an $N \times N$ integer matrix
  $A$ with $\mathrm{ord}(A) = m$. -/)
  (proof := /-- Definition. The set collects all orders $m$ witnessed by some $N \times N$
  integer matrix. -/)]
def integerMatrixOrders (N : ℕ) : Set ℕ :=
  {m | ∃ A : Matrix (Fin N) (Fin N) ℤ, orderOf A = m ∧ 0 < m}

/-- The identity matrix has order 1, so 1 ∈ integerMatrixOrders N for any N. -/
@[blueprint "lem:one-mem-orders"
  (statement := /-- Order $1$ is achievable in any dimension. -/)
  (proof := /-- The identity matrix $I$ has order $1$ in any dimension. -/)]
theorem one_mem_integerMatrixOrders (N : ℕ) : 1 ∈ integerMatrixOrders N := by
  use 1
  constructor
  · exact orderOf_one
  · norm_num

/-- The ring characteristic of integer matrices is 0 for N ≥ 1. -/
lemma ringChar_matrix_int (N : ℕ) [NeZero N] : ringChar (Matrix (Fin N) (Fin N) ℤ) = 0 := by
  rw [ringChar.eq_iff]
  constructor
  intro n
  constructor
  · intro hn
    have h : ∀ i, (n : Matrix (Fin N) (Fin N) ℤ) i i = 0 := fun i => by
      have := congrFun (congrFun hn i) i
      exact this
    have ⟨i⟩ : Nonempty (Fin N) := ⟨⟨0, NeZero.pos N⟩⟩
    have hi := h i
    simp only [Matrix.natCast_apply] at hi
    rw [Nat.cast_eq_zero] at hi
    exact Nat.zero_dvd.mpr hi
  · intro hn
    rw [Nat.zero_dvd] at hn
    subst hn
    simp only [Nat.cast_zero]

/-- For N ≥ 1, the negation of the identity matrix has order 2. -/
@[blueprint "lem:two-mem-orders"
  (statement := /-- Order $2$ is achievable for $N \geq 1$. -/)
  (proof := /-- The matrix $-I$ satisfies $(-I)^2 = I$ and $-I \neq I$ for $N \geq 1$,
  so it has order $2$. -/)]
theorem two_mem_integerMatrixOrders (N : ℕ) [NeZero N] : 2 ∈ integerMatrixOrders N := by
  use -1
  constructor
  · rw [orderOf_neg_one, ringChar_matrix_int, if_neg (by norm_num : (0 : ℕ) ≠ 2)]
  · norm_num

/-- The canonical block diagonal embedding of an M×M matrix into an (M+K)×(M+K) matrix
using Sum types. Places the matrix in the upper-left block and identity in the lower-right. -/
def embedMatrixSum {M K : ℕ} (A : Matrix (Fin M) (Fin M) ℤ) :
    Matrix (Fin M ⊕ Fin K) (Fin M ⊕ Fin K) ℤ :=
  Matrix.fromBlocks A 0 0 1

/-- The embedded identity is identity. -/
lemma embedMatrixSum_one {M K : ℕ} :
    embedMatrixSum (1 : Matrix (Fin M) (Fin M) ℤ) =
    (1 : Matrix (Fin M ⊕ Fin K) (Fin M ⊕ Fin K) ℤ) := by
  simp only [embedMatrixSum, fromBlocks_one]

/-- The embedding preserves multiplication. -/
lemma embedMatrixSum_mul {M K : ℕ} (A B : Matrix (Fin M) (Fin M) ℤ) :
    embedMatrixSum (K := K) (A * B) = embedMatrixSum A * embedMatrixSum B := by
  simp only [embedMatrixSum]
  rw [fromBlocks_multiply]
  simp

/-- The embedding is a monoid homomorphism. -/
def embedMatrixSumHom (M K : ℕ) :
    Matrix (Fin M) (Fin M) ℤ →* Matrix (Fin M ⊕ Fin K) (Fin M ⊕ Fin K) ℤ where
  toFun := embedMatrixSum
  map_one' := embedMatrixSum_one
  map_mul' := embedMatrixSum_mul

/-- The embedding is injective. -/
lemma embedMatrixSumHom_injective (M K : ℕ) : Function.Injective (embedMatrixSumHom M K) := by
  intro A B hAB
  simp only [embedMatrixSumHom, MonoidHom.coe_mk, OneHom.coe_mk] at hAB
  ext i j
  have h := congrFun (congrFun hAB (Sum.inl i)) (Sum.inl j)
  simp only [embedMatrixSum, fromBlocks_apply₁₁] at h
  exact h

/-- The embedding preserves order. -/
lemma orderOf_embedMatrixSum_eq {M K : ℕ} (A : Matrix (Fin M) (Fin M) ℤ) :
    orderOf (embedMatrixSum (K := K) A) = orderOf A :=
  orderOf_injective (embedMatrixSumHom M K) (embedMatrixSumHom_injective M K) A

/-- Alternative set of orders using Sum-indexed matrices for convenience.

This is equivalent to integerMatrixOrders (M + K) but uses Sum types for indexing,
which simplifies working with block diagonal matrices. -/
def integerMatrixOrdersSum (M K : ℕ) : Set ℕ :=
  {m | ∃ A : Matrix (Fin M ⊕ Fin K) (Fin M ⊕ Fin K) ℤ, orderOf A = m ∧ 0 < m}

/-- Orders achievable for M×M matrices are achievable for (M⊕K)-indexed matrices. -/
theorem integerMatrixOrders_subset_sum (M K : ℕ) :
    integerMatrixOrders M ⊆ integerMatrixOrdersSum M K := by
  intro m hm
  simp only [integerMatrixOrders, integerMatrixOrdersSum, Set.mem_setOf_eq] at hm ⊢
  obtain ⟨A, hA_ord, hA_pos⟩ := hm
  use embedMatrixSum A
  constructor
  · rw [orderOf_embedMatrixSum_eq, hA_ord]
  · exact hA_pos

/-- The equivalence between Fin (M + K) and Fin M ⊕ Fin K.

This is the standard bijection used to convert between Fin-indexed and Sum-indexed matrices. -/
def finSumEquiv (M K : ℕ) : Fin (M + K) ≃ Fin M ⊕ Fin K := finSumFinEquiv.symm

/-- Reindexing defines a monoid isomorphism.

Given an equivalence e : m ≃ n between index types, this provides an isomorphism
between the corresponding matrix monoids that preserves multiplication. -/
def reindexMonoidEquiv {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (e : m ≃ n) : Matrix m m ℤ ≃* Matrix n n ℤ where
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
  let e : Fin N ≃ Fin M ⊕ Fin K := hN ▸ (finSumEquiv M K)
  let A'' : Matrix (Fin N) (Fin N) ℤ := (reindexMonoidEquiv e).symm A'
  use A''
  constructor
  · simp only [A'']
    have h1 : orderOf ((reindexMonoidEquiv e).symm A') = orderOf A' :=
      MulEquiv.orderOf_eq (reindexMonoidEquiv e).symm A'
    rw [h1, orderOf_embedMatrixSum_eq, hA_ord]
  · exact hA_pos

/-- Divisibility: if m ∈ integerMatrixOrders N and d | m with d > 0,
then d ∈ integerMatrixOrders N.

If A has order m and d | m, then A^{m/d} has order d. -/
@[blueprint "lem:divisor-mem-orders"
  (statement := /-- If $m \in \mathrm{Ord}_N$ and $d \mid m$, then $d \in \mathrm{Ord}_N$. -/)
  (proof := /-- If $A$ has order $m$ and $d \mid m$, then $A^{m/d}$ has order $d$. -/)]
theorem divisor_mem_integerMatrixOrders {N : ℕ} {m d : ℕ}
    (hm : m ∈ integerMatrixOrders N) (hd : d ∣ m) (hd_pos : 0 < d) :
    d ∈ integerMatrixOrders N := by
  simp only [integerMatrixOrders, Set.mem_setOf_eq] at hm ⊢
  obtain ⟨A, hA_ord, hA_pos⟩ := hm
  use A ^ (m / d)
  constructor
  · rw [← hA_ord]
    exact orderOf_pow_orderOf_div (ne_of_gt (hA_ord.symm ▸ hA_pos)) (hA_ord.symm ▸ hd)
  · exact hd_pos

/-! ## Block diagonal matrix infrastructure -/

/-- Block diagonal of two matrices: places A in upper-left and B in lower-right. -/
@[blueprint "def:blockDiag2"
  (statement := /-- Block diagonal matrix $\mathrm{diag}(A, B)$ of dimension $M + N$. -/)
  (proof := /-- Definition. Block diagonal matrix with $A$ in top-left, $B$ in bottom-right,
  zeros elsewhere. -/)]
def blockDiag2 {M K : ℕ} (A : Matrix (Fin M) (Fin M) ℤ) (B : Matrix (Fin K) (Fin K) ℤ) :
    Matrix (Fin M ⊕ Fin K) (Fin M ⊕ Fin K) ℤ :=
  Matrix.fromBlocks A 0 0 B

/-- Block diagonal of identity matrices is the identity. -/
lemma blockDiag2_one {M K : ℕ} :
    blockDiag2 (1 : Matrix (Fin M) (Fin M) ℤ) (1 : Matrix (Fin K) (Fin K) ℤ) =
    (1 : Matrix (Fin M ⊕ Fin K) (Fin M ⊕ Fin K) ℤ) :=
  Matrix.fromBlocks_one

/-- Block diagonal preserves multiplication. -/
lemma blockDiag2_mul {M K : ℕ}
    (A A' : Matrix (Fin M) (Fin M) ℤ) (B B' : Matrix (Fin K) (Fin K) ℤ) :
    blockDiag2 (A * A') (B * B') = blockDiag2 A B * blockDiag2 A' B' := by
  simp only [blockDiag2, Matrix.fromBlocks_multiply]
  congr 1 <;> simp

/-- Block diagonal is one iff both components are one. -/
@[blueprint "lem:blockDiag2-eq-one"
  (statement := /-- $\mathrm{diag}(A, B) = 1 \iff A = 1 \land B = 1$. \uses{def:blockDiag2} -/)
  (proof := /-- The block diagonal matrix equals $I$ iff both diagonal blocks equal their
  respective identities. -/)]
lemma blockDiag2_eq_one_iff {M K : ℕ}
    (A : Matrix (Fin M) (Fin M) ℤ) (B : Matrix (Fin K) (Fin K) ℤ) :
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
lemma blockDiag2_pow {M K : ℕ}
    (A : Matrix (Fin M) (Fin M) ℤ) (B : Matrix (Fin K) (Fin K) ℤ) (k : ℕ) :
    (blockDiag2 A B) ^ k = blockDiag2 (A ^ k) (B ^ k) := by
  simp only [blockDiag2]
  exact Matrix.fromBlocks_diagonal_pow A B k

end Crystallographic
