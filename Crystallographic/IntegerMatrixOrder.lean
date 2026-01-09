/-
Copyright (c) 2026 Eric Vergo. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Eric Vergo
-/
-- import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
-- import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Algebra.CharP.Two
import Mathlib.Data.Matrix.Block

/-!
# Orders of Integer Matrices

This file defines the set of possible orders for N×N integer matrices with finite order,
and proves basic properties about this set.

## Main definitions

* `integerMatrixOrders N` - The set of orders achievable by N×N integer matrices with finite order.

## Main results

* `one_mem_integerMatrixOrders` - The identity matrix has order 1.
* `two_mem_integerMatrixOrders` - Negation of identity has order 2 (for N ≥ 1).
* `integerMatrixOrders_mono` - Monotonicity: M ≤ N implies OrdM ⊆ OrdN.
* `divisor_mem_integerMatrixOrders` - Divisibility: if m ∈ OrdN and d ∣ m, then d ∈ OrdN.

## Implementation notes

We work with `Matrix (Fin N) (Fin N) ℤ` and use Mathlib's `orderOf` which returns 0 for
elements of infinite order. We require `0 < m` to ensure we're talking about finite orders.
-/

namespace Crystallographic

open Matrix

/-- The set of possible orders for N×N integer matrices with finite order.
An integer `m` is in this set if there exists an N×N integer matrix `A` such that
`orderOf A = m` and `m > 0` (equivalently, `A` has finite order). -/
def integerMatrixOrders (N : ℕ) : Set ℕ :=
  {m | ∃ A : Matrix (Fin N) (Fin N) ℤ, orderOf A = m ∧ 0 < m}

/-- The identity matrix has order 1, so 1 ∈ integerMatrixOrders N for any N. -/
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

/-- Alternative set of orders using Sum-indexed matrices for convenience. -/
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

/-- The equivalence between Fin (M + K) and Fin M ⊕ Fin K -/
def finSumEquiv (M K : ℕ) : Fin (M + K) ≃ Fin M ⊕ Fin K := finSumFinEquiv.symm

/-- Reindexing defines a monoid isomorphism. -/
def reindexMonoidEquiv {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (e : m ≃ n) : Matrix m m ℤ ≃* Matrix n n ℤ where
  toFun A := A.submatrix e.symm e.symm
  invFun A := A.submatrix e e
  left_inv A := by simp only [submatrix_submatrix, Equiv.symm_comp_self, submatrix_id_id]
  right_inv A := by simp only [submatrix_submatrix, Equiv.self_comp_symm, submatrix_id_id]
  map_mul' A B := by
    simp only [← submatrix_mul_equiv (M := A) (N := B) (e₁ := e.symm) (e₂ := e.symm)]

/-- Monotonicity: if M ≤ N, then any order achievable for M×M matrices is also achievable
for N×N matrices. -/
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

/-- Helper: for d | m with d > 0 and m > 0, we have m / gcd(m, m/d) = d -/
lemma div_gcd_div_eq {m d : ℕ} (hd : d ∣ m) (hd_pos : 0 < d) (hm_pos : 0 < m) :
    m / Nat.gcd m (m / d) = d := by
  obtain ⟨k, hk⟩ := hd
  have hk_pos : 0 < k := by
    rcases Nat.eq_zero_or_pos k with hk0 | hk_pos
    · subst hk0
      simp only [mul_zero] at hk
      omega
    · exact hk_pos
  subst hk
  rw [Nat.mul_div_cancel_left k hd_pos]
  -- gcd(d * k, k) = k
  have h1 : Nat.gcd (d * k) k = k := by
    rw [Nat.gcd_comm]
    exact Nat.gcd_eq_left (Nat.dvd_mul_left k d)
  rw [h1]
  rw [mul_comm]
  exact Nat.mul_div_cancel_left d hk_pos

/-- If an element has order m > 0 and d divides m with d > 0, then g^(m/d) has order d. -/
lemma orderOf_pow_of_dvd {G : Type*} [Monoid G] (g : G) (m d : ℕ)
    (hm : orderOf g = m) (hd : d ∣ m) (hd_pos : 0 < d) (hm_pos : 0 < m) :
    orderOf (g ^ (m / d)) = d := by
  have hdiv_pos : 0 < m / d := Nat.div_pos (Nat.le_of_dvd hm_pos hd) hd_pos
  rw [orderOf_pow' g (ne_of_gt hdiv_pos)]
  rw [hm]
  exact div_gcd_div_eq hd hd_pos hm_pos

/-- Divisibility: if m ∈ integerMatrixOrders N and d ∣ m with d > 0,
then d ∈ integerMatrixOrders N. -/
theorem divisor_mem_integerMatrixOrders {N : ℕ} {m d : ℕ}
    (hm : m ∈ integerMatrixOrders N) (hd : d ∣ m) (hd_pos : 0 < d) :
    d ∈ integerMatrixOrders N := by
  simp only [integerMatrixOrders, Set.mem_setOf_eq] at hm ⊢
  obtain ⟨A, hA_ord, hA_pos⟩ := hm
  use A ^ (m / d)
  constructor
  · exact orderOf_pow_of_dvd A m d hA_ord hd hd_pos hA_pos
  · exact hd_pos

/-! ## Block diagonal matrix infrastructure -/

/-- Block diagonal of two matrices: places A in upper-left and B in lower-right. -/
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
lemma blockDiag2_eq_one_iff {M K : ℕ}
    (A : Matrix (Fin M) (Fin M) ℤ) (B : Matrix (Fin K) (Fin K) ℤ) :
    blockDiag2 A B = 1 ↔ A = 1 ∧ B = 1 := by
  rw [← blockDiag2_one]
  simp only [blockDiag2, Matrix.fromBlocks_inj]
  tauto

/-- Power of block diagonal. -/
lemma blockDiag2_pow {M K : ℕ}
    (A : Matrix (Fin M) (Fin M) ℤ) (B : Matrix (Fin K) (Fin K) ℤ) (k : ℕ) :
    (blockDiag2 A B) ^ k = blockDiag2 (A ^ k) (B ^ k) := by
  simp only [blockDiag2]
  exact Matrix.fromBlocks_diagonal_pow A B k

/-- Order of block diagonal is lcm of orders. -/
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

/-- For coprime m and n, lcm(m, n) = m * n. -/
lemma lcm_eq_mul_of_coprime {m n : ℕ} (h : Nat.Coprime m n) :
    Nat.lcm m n = m * n := by
  rw [Nat.lcm_comm, Nat.Coprime.lcm_eq_mul h.symm, mul_comm]

/-- Block diagonal construction for integer matrix orders.
    If m₁ ∈ integerMatrixOrders M and m₂ ∈ integerMatrixOrders K,
    then lcm(m₁, m₂) ∈ integerMatrixOrders (M + K). -/
theorem lcm_mem_integerMatrixOrders {M K m₁ m₂ : ℕ}
    (h₁ : m₁ ∈ integerMatrixOrders M) (h₂ : m₂ ∈ integerMatrixOrders K) :
    Nat.lcm m₁ m₂ ∈ integerMatrixOrders (M + K) := by
  obtain ⟨A, hA_ord, hA_pos⟩ := h₁
  obtain ⟨B, hB_ord, hB_pos⟩ := h₂
  -- Construct block diagonal matrix
  let C := blockDiag2 A B
  -- Reindex from Sum to Fin (M + K)
  let e : Fin (M + K) ≃ Fin M ⊕ Fin K := (finSumEquiv M K)
  let C' : Matrix (Fin (M + K)) (Fin (M + K)) ℤ := (reindexMonoidEquiv e).symm C
  use C'
  constructor
  · have h1 : orderOf C' = orderOf C :=
      MulEquiv.orderOf_eq (reindexMonoidEquiv e).symm C
    rw [h1, orderOf_blockDiag2, hA_ord, hB_ord]
  · exact Nat.lcm_pos hA_pos hB_pos

/-- For coprime m₁, m₂, if m₁ ∈ integerMatrixOrders M and m₂ ∈ integerMatrixOrders K,
    then m₁ * m₂ ∈ integerMatrixOrders (M + K). -/
theorem mul_mem_integerMatrixOrders_of_coprime {M K m₁ m₂ : ℕ}
    (h₁ : m₁ ∈ integerMatrixOrders M) (h₂ : m₂ ∈ integerMatrixOrders K)
    (hcop : Nat.Coprime m₁ m₂) :
    m₁ * m₂ ∈ integerMatrixOrders (M + K) := by
  rw [← lcm_eq_mul_of_coprime hcop]
  exact lcm_mem_integerMatrixOrders h₁ h₂

end Crystallographic
