/-
Copyright (c) 2026 Eric Vergo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo
-/
import Dress
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.LinearAlgebra.Matrix.Charpoly.Minpoly
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Crystallographic.Companion.Cyclotomic
import Crystallographic.FiniteOrder.Order
import Crystallographic.Psi.Basic
import Crystallographic.Psi.Bounds

/-!
# The Crystallographic Restriction Theorem - Backward Direction

This file proves the backward direction of the crystallographic restriction theorem:
if psi(m) <= N, then there exists an N x N integer matrix with order m.

## Main results

* `mem_integerMatrixOrders_of_psi_le` - Backward direction: psi(m) <= N implies order m achievable.

## Proof Strategy

1. Construct companion matrix of cyclotomic polynomial Phi_m over Z
2. This has size phi(m) x phi(m) and order m
3. For composite m, use block diagonal of companion matrices for prime power factors
4. Total size is psi(m) <= N, pad with identity to get N x N matrix

## References

* Sasse, R. (2020). "Crystallographic Groups"

## Tags

crystallographic restriction, backward direction, companion matrix, cyclotomic, permutation matrix
-/

namespace Crystallographic

open Matrix Polynomial

/-!
### Permutation matrix lemmas

These lemmas about permutation matrices are general-purpose and could be contributed
to `Mathlib.LinearAlgebra.Matrix.Permutation`:
- `permMatrix_one`
- `permMatrix_mul`
- `permMatrix_pow`
- `permMatrix_eq_one_iff`
- `orderOf_permMatrix`

They build on `PEquiv.toMatrix_refl`, `PEquiv.toMatrix_trans`, `Equiv.toPEquiv_refl`,
and `Equiv.toPEquiv_trans` from Mathlib.

TODO: Consider upstreaming these to Mathlib.
-/

namespace Equiv.Perm

/-- The permutation matrix of the identity permutation is the identity matrix. -/
@[simp, blueprint "lem:permMatrix-one"
  (above := /-- Before constructing companion matrices, we develop a simpler family of integer matrices
  with prescribed finite order: permutation matrices. A permutation $\sigma \in S_n$ gives
  an $n \times n$ matrix $P_\sigma$ with entries 0 and 1. The key properties we need are that
  $\sigma \mapsto P_\sigma$ preserves powers and is injective, so
  $\mathrm{ord}(P_\sigma) = \mathrm{ord}(\sigma)$. We begin with the base case. -/)
  (title := "Permutation Matrix Identity Base")
  (statement := /-- The permutation matrix of the identity is the identity matrix: $P_{\mathrm{id}} = I$. -/)
  (proof := /-- Direct computation using $\mathrm{toPEquiv}(\mathrm{id}) = \mathrm{refl}$ and
  $\mathrm{toMatrix}(\mathrm{refl}) = I$. -/)]
lemma permMatrix_one {n : Type*} [DecidableEq n] {R : Type*} [Zero R] [One R] :
    (1 : Equiv.Perm n).permMatrix R = (1 : Matrix n n R) := by
  simp only [Equiv.Perm.permMatrix, Equiv.Perm.one_def, Equiv.toPEquiv_refl, PEquiv.toMatrix_refl]

/-- Permutation matrices compose: (σ * τ).permMatrix = τ.permMatrix * σ.permMatrix -/
@[blueprint "lem:permMatrix-mul"
  (title := "Permutation Matrix Multiplication")
  (statement := /-- Permutation matrices satisfy $P_{\sigma \cdot \tau} = P_\tau \cdot P_\sigma$
  (contravariant homomorphism). -/)
  (proof := /-- Follows from $\mathrm{toPEquiv}(\sigma \circ \tau) = \mathrm{toPEquiv}(\tau) \cdot \mathrm{toPEquiv}(\sigma)$
  and the corresponding property for partial equivalence matrices. -/)]
lemma permMatrix_mul {n : Type*} [DecidableEq n] [Fintype n] {R : Type*} [Semiring R]
    (σ τ : Equiv.Perm n) :
    (σ * τ).permMatrix R = τ.permMatrix R * σ.permMatrix R := by
  simp only [Equiv.Perm.permMatrix]
  rw [Equiv.Perm.mul_def, Equiv.toPEquiv_trans, PEquiv.toMatrix_trans]

/-- Permutation matrices power correctly: (σ^k).permMatrix = (σ.permMatrix)^k -/
@[blueprint "lem:permMatrix-pow"
  (title := "Permutation Matrix Power")
  (statement := /-- Powers of permutation matrices satisfy $P_{\sigma^k} = P_\sigma^k$.
  \uses{lem:permMatrix-one, lem:permMatrix-mul} -/)
  (proof := /-- By induction on $k$: the base case uses $P_{\mathrm{id}} = I$, and the inductive
  step uses $P_{\sigma \cdot \tau} = P_\tau \cdot P_\sigma$ together with commutativity of powers. -/)]
lemma permMatrix_pow {n : Type*} [DecidableEq n] [Fintype n] {R : Type*} [Semiring R]
    (σ : Equiv.Perm n) (k : ℕ) :
    (σ ^ k).permMatrix R = (σ.permMatrix R) ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, pow_succ, permMatrix_mul, ih]
    -- Goal: σ.permMatrix * (σ.permMatrix)^k = (σ.permMatrix)^k * σ.permMatrix
    -- Use SemiconjBy or direct equality - both sides are equal
    exact (Commute.pow_self (σ.permMatrix R) k).eq.symm

/-- Permutation matrix is identity iff permutation is identity. -/
@[blueprint "lem:permMatrix-eq-one-iff"
  (above := /-- The power identity $P_{\sigma^k} = P_\sigma^k$ from the permutation matrix power lemma
  reduces the order question for $P_\sigma$ to an injectivity statement: we need
  $P_\sigma = I \iff \sigma = \mathrm{id}$. -/)
  (title := "Permutation Matrix Identity")
  (statement := /-- $P_\sigma = I$ if and only if $\sigma = \mathrm{id}$.
  \uses{lem:permMatrix-one} -/)
  (proof := /-- The forward direction shows that if $P_\sigma = I$ then for each $x$, the entry
  $(P_\sigma)_{x, \sigma(x)} = 1$ forces $\sigma(x) = x$. The reverse is immediate from
  $P_{\mathrm{id}} = I$. -/)]
lemma permMatrix_eq_one_iff {n : Type*} [DecidableEq n] [Fintype n] {R : Type*} [Semiring R]
    [Nontrivial R] (σ : Equiv.Perm n) :
    σ.permMatrix R = 1 ↔ σ = 1 := by
  constructor
  · intro h
    ext x
    have hx := congrFun (congrFun h x) (σ x)
    simp only [Equiv.Perm.permMatrix, Equiv.toPEquiv_apply, PEquiv.toMatrix_apply, Matrix.one_apply,
      Option.mem_def] at hx
    by_cases hσx : σ x = x
    · exact hσx
    · exfalso
      -- hx says: if σ (σ x) = σ x then 1 else 0 = if x = σ x then 1 else 0
      -- After simp, lhs simplifies using σ (σ x) = σ x ↔ σ x = x (by injectivity)
      -- which is true since Option.mem_def
      -- rhs: x = σ x is false by hσx
      have h1 : (1 : R) = if x = σ x then 1 else 0 := hx
      rw [if_neg (ne_comm.mpr hσx)] at h1
      exact one_ne_zero h1
  · intro h; rw [h]; exact permMatrix_one

/-- Order of permutation matrix equals order of permutation. -/
@[blueprint "lem:orderOf-permMatrix"
  (title := "Permutation Matrix Order")
  (statement := /-- The order of $P_\sigma$ equals the order of $\sigma$ for a permutation matrix. -/)
  (proof := /-- Since $P_{\sigma^k} = P_\sigma^k$ and $P_\sigma = I \iff \sigma = \mathrm{id}$, the order
  of $P_\sigma$ equals the order of $\sigma$. The key is that the permutation matrix map preserves
  powers and is injective on the group of permutation matrices. -/)
  (below := /-- With order preservation established, we can produce integer matrices of any desired
  order $n$ simply by finding a permutation of order $n$. The canonical choice is the cyclic
  rotation $\mathrm{finRotate}(n)$, which has order $n$ by the cycle order theorem. -/)]
lemma orderOf_permMatrix {n : Type*} [DecidableEq n] [Fintype n] {R : Type*} [Semiring R]
    [Nontrivial R] (σ : Equiv.Perm n) :
    orderOf (σ.permMatrix R) = orderOf σ := by
  rcases Nat.eq_zero_or_pos (orderOf σ) with hord | hord
  · -- σ has infinite order (orderOf σ = 0)
    rw [hord, orderOf_eq_zero_iff']
    intro k hk heq
    have h1 : (σ ^ k).permMatrix R = 1 := by rw [permMatrix_pow]; exact heq
    rw [permMatrix_eq_one_iff] at h1
    exact (orderOf_eq_zero_iff'.mp hord) k hk h1
  · -- σ has finite order
    rw [orderOf_eq_iff hord]
    constructor
    · rw [← permMatrix_pow, pow_orderOf_eq_one]; exact permMatrix_one
    · intro k hk_lt hk_pos heq
      have hk' : (σ ^ k).permMatrix R = 1 := by rw [permMatrix_pow]; exact heq
      rw [permMatrix_eq_one_iff] at hk'
      have hdvd : orderOf σ ∣ k := orderOf_dvd_of_pow_eq_one hk'
      exact Nat.not_lt.mpr (Nat.le_of_dvd hk_pos hdvd) hk_lt

/-- The finRotate permutation has order n for n at least 2. -/
@[blueprint "lem:orderOf-finRotate"
  (title := "Rotation Order")
  (statement := /-- The order of $\mathrm{finRotate}(n)$ equals $n$. -/)
  (proof := /-- The $\mathrm{finRotate}(n)$ permutation is an $n$-cycle with full support $\mathrm{Fin}\ n$.
  By the cycle order theorem, the order of a cycle equals its length, which is $n$. -/)]
lemma orderOf_finRotate (n : ℕ) (hn : 2 ≤ n) : orderOf (finRotate n) = n := by
  have hcycle := isCycle_finRotate_of_le hn
  have hord := Equiv.Perm.IsCycle.orderOf hcycle
  have hsupp := support_finRotate_of_le hn
  rw [hord, hsupp, Finset.card_univ, Fintype.card_fin]

/-- finRotate permutation matrix has order n for n >= 2. -/
@[blueprint "lem:orderOf-permMatrix-finRotate"
  (title := "Rotation Permutation Order")
  (statement := /-- The permutation matrix of $\mathrm{finRotate}(n)$ has order $n$ over $\mathbb{Z}$.
  \uses{lem:orderOf-permMatrix, lem:orderOf-finRotate} -/)
  (proof := /-- Combines the order-preservation property $\mathrm{ord}(P_\sigma) = \mathrm{ord}(\sigma)$
  with $\mathrm{ord}(\mathrm{finRotate}(n)) = n$. -/)
  (below := /-- This gives $n \in \mathrm{Ord}_n$ for all $n \geq 2$: the rotation permutation matrix
  is an $n \times n$ integer matrix with order $n$. While this only shows order $n$ is achievable
  in dimension $n$ (not the optimal $\psi(n)$), it handles the easy case where $n \leq N$
  in the backward direction. -/)]
lemma orderOf_permMatrix_finRotate (n : ℕ) (hn : 2 ≤ n) :
    orderOf ((finRotate n).permMatrix ℤ) = n := by
  rw [orderOf_permMatrix, orderOf_finRotate n hn]

end Equiv.Perm

/-- Order n is achievable by an n x n integer matrix for n at least 2. -/
@[blueprint "lem:mem-integerMatrixOrders-self"
  (title := "Self in Matrix Orders")
  (statement := /-- $m \in \mathrm{Ord}_m$ for $m \geq 2$ via permutation matrix. -/)
  (proof := /-- The permutation matrix $P_{\mathrm{finRotate}(m)}$ is an $m \times m$ integer matrix
  with order exactly $m$, since $\mathrm{finRotate}(m)$ has order $m$. -/)
  (below := /-- This corollary is used in the backward direction to handle the case $m \leq N$:
  if the matrix dimension $N$ is at least $m$, we can simply use a permutation matrix
  and pad with identity blocks, without needing the more sophisticated companion matrix
  construction. -/)]
lemma mem_integerMatrixOrders_self (n : ℕ) (hn : 2 ≤ n) : n ∈ integerMatrixOrders n := by
  use (finRotate n).permMatrix ℤ
  constructor
  · exact Equiv.Perm.orderOf_permMatrix_finRotate n hn
  · omega

/-! ## Backward direction: Dimension bound implies order is achievable -/

/-- For prime power with p odd or k at least 2, p^k is in integerMatrixOrders(psi(p^k)). -/
@[blueprint "thm:primePow-mem-integerMatrixOrders-psi"
  (above := /-- We now begin the core of the backward direction. The strategy is to show
  $m \in \mathrm{Ord}_{\psi(m)}$ by building matrices for each prime power factor and combining
  them via block diagonals. The first step handles individual prime powers $p^k$
  (excluding $2^1$, which is treated separately via negation). For these, $\psi(p^k) = \varphi(p^k)$,
  and the companion matrix of $\Phi_{p^k}$ from the totient membership theorem provides a matrix
  of the correct dimension and order. -/)
  (title := "Prime Power in Orders")
  (statement := /-- For a prime power $p^k$ with $p$ odd or $k \geq 2$, we have $p^k \in \mathrm{Ord}_{\psi(p^k)}$.
  -/)
  (proof := /-- For these prime powers, $\psi(p^k) = \varphi(p^k)$. The companion matrix of $\Phi_{p^k}$
  has dimension $\varphi(p^k)$ and order exactly $p^k$, so $p^k \in \mathrm{Ord}_{\varphi(p^k)} = \mathrm{Ord}_{\psi(p^k)}$. -/)
  (below := /-- The excluded case $p^k = 2$ is special: $\psi(2) = 0$ and $\varphi(2) = 1$, so
  the companion matrix approach would require dimension 1 but $\psi$ promises dimension 0.
  Instead, multiplying by $-I$ doubles the order of an odd-order matrix without increasing
  dimension. This trick is why $\psi(m)$ can be strictly less than $\varphi(m)$ when $m$ is even. -/)]
theorem primePow_mem_integerMatrixOrders_psi (p k : ℕ) (hp : p.Prime) (hk : 0 < k)
    (hpk : ¬(p = 2 ∧ k = 1)) :
    p ^ k ∈ integerMatrixOrders (psi (p ^ k)) := by
  -- psi(p^k) = totient(p^k) for this case
  have hpsi_eq : psi (p ^ k) = Nat.totient (p ^ k) := by
    rw [psi_prime_pow p k hp hk]
    simp only [hpk, ite_false]
  rw [hpsi_eq]
  -- Use companion matrix lemma
  have hpk_ge2 : 2 ≤ p ^ k := by
    have hp_ge2 : 2 ≤ p := hp.two_le
    calc p ^ k ≥ p ^ 1 := Nat.pow_le_pow_right (Nat.le_of_lt hp.one_lt) hk
      _ = p := pow_one p
      _ ≥ 2 := hp_ge2
  exact mem_integerMatrixOrders_totient (p ^ k) hpk_ge2

/-!
### Private helper lemmas for backward direction

The following lemmas handle specific cases in the backward direction proof,
particularly the cases involving coprimality with 2 and odd prime powers.
-/

/-- Derives oddness, non-equality to 2, and lower bound from coprimality to 2. -/
private lemma odd_ne_two_ge_three_of_coprime_two {m' : ℕ} (hcop : Nat.Coprime 2 m') (hm'_ge2 : 2 ≤ m') :
    Odd m' ∧ m' ≠ 2 ∧ 3 ≤ m' := by
  have hm'_odd : Odd m' := Nat.Coprime.odd_of_left hcop
  have hm'_ne_2 : m' ≠ 2 := fun h => by rw [h] at hcop; simp at hcop
  exact ⟨hm'_odd, hm'_ne_2, by omega⟩

/-- Shows `2 * m' ∈ integerMatrixOrders (psi (2 * m'))` for odd `m' >= 3`.
Uses the fact that negating an odd-order matrix doubles its order without changing dimension. -/
private lemma mem_integerMatrixOrders_psi_2_times_odd (m' : ℕ) (hm'_pos : 0 < m')
    (hm'_odd : Odd m') (hm'_ge3 : 3 ≤ m')
    (IH_m' : m' ∈ integerMatrixOrders (psi m')) :
    2 * m' ∈ integerMatrixOrders (psi (2 * m')) := by
  have hcop : Nat.Coprime 2 m' := Nat.Coprime.symm (Odd.coprime_two_right hm'_odd)
  have hpsi_eq : psi (2 * m') = psi m' := by
    rw [psi_coprime_add 2 m' (by omega) hm'_pos hcop]
    simp only [psi_two, zero_add]
  rw [hpsi_eq]
  have hpsi_pos : 0 < psi m' := psi_pos_of_odd_ge_three hm'_ge3 hm'_odd
  haveI : NeZero (psi m') := ⟨by omega⟩
  obtain ⟨A, hA_ord, hA_pos⟩ := IH_m'
  refine ⟨-A, ?_, by omega⟩
  rw [orderOf_neg_of_odd_order m' hm'_odd A hA_ord]

/-- Shows `k * 2 ∈ integerMatrixOrders (psi (k * 2))` for odd `k >= 3`.
Symmetric version of `mem_integerMatrixOrders_psi_2_times_odd` with factor of 2 on the right. -/
private lemma mem_integerMatrixOrders_psi_odd_times_2 (k : ℕ) (hk_pos : 0 < k)
    (hk_odd : Odd k) (hk_ge3 : 3 ≤ k)
    (IH_k : k ∈ integerMatrixOrders (psi k)) :
    k * 2 ∈ integerMatrixOrders (psi (k * 2)) := by
  have hcop : Nat.Coprime k 2 := Odd.coprime_two_right hk_odd
  have hpsi_eq : psi (k * 2) = psi k := by
    rw [psi_coprime_add k 2 hk_pos (by omega) hcop]
    simp only [psi_two, add_zero]
  rw [hpsi_eq]
  have hpsi_pos : 0 < psi k := psi_pos_of_odd_ge_three hk_ge3 hk_odd
  haveI : NeZero (psi k) := ⟨by omega⟩
  obtain ⟨A, hA_ord, hA_pos⟩ := IH_k
  refine ⟨-A, ?_, by omega⟩
  rw [orderOf_neg_of_odd_order k hk_odd A hA_ord, mul_comm]

/-- Derives that a prime power coprime to 2 is odd and at least 3. -/
private lemma primePow_odd_ge_three_of_coprime_two {p e : ℕ} (hp : p.Prime) (he_pos : 0 < e)
    (hcop : Nat.Coprime (p ^ e) 2) : Odd (p ^ e) ∧ 3 ≤ p ^ e := by
  have hp_odd : p ≠ 2 := by
    intro hp2; rw [hp2] at hcop
    simp only [Nat.coprime_pow_left_iff he_pos, Nat.coprime_self] at hcop
    norm_num at hcop
  have hp_ge3 : 3 ≤ p := by
    rcases hp.two_le.lt_or_eq with h | h
    · exact h
    · omega
  constructor
  · exact (Nat.Prime.odd_of_ne_two hp hp_odd).pow
  · calc p ^ e ≥ p ^ 1 := Nat.pow_le_pow_right (by omega) he_pos
      _ = p := pow_one p
      _ ≥ 3 := hp_ge3

/-- Shows `p^e * m' ∈ integerMatrixOrders (psi (p^e * m'))` via block diagonal construction.
Combines IH results for coprime factors using additivity of psi. -/
private lemma mem_integerMatrixOrders_psi_composite (p e m' : ℕ)
    (hp : p.Prime) (hm'_pos : 0 < m') (hcop : Nat.Coprime (p ^ e) m')
    (IH_pe : p ^ e ∈ integerMatrixOrders (psi (p ^ e)))
    (IH_m' : m' ∈ integerMatrixOrders (psi m')) :
    p ^ e * m' ∈ integerMatrixOrders (psi (p ^ e * m')) := by
  have hpsi_eq : psi (p ^ e * m') =
      psi (p ^ e) + psi m' := by
    rw [psi_coprime_add (p ^ e) m' (Nat.pow_pos hp.pos) hm'_pos hcop]
  rw [hpsi_eq]
  exact mul_mem_integerMatrixOrders_of_coprime IH_pe IH_m' hcop

/-- Every `m >= 1` with `m ≠ 2` belongs to `integerMatrixOrders (psi m)`.

The proof uses strong induction on `m`:
- `m = 1`: `psi 1 = 0`, use identity matrix
- `m = 2`: EXCLUDED - `psi 2 = 0` but `2 ∉ integerMatrixOrders 0`
- `m = p^k` prime power (p ≠ 2 or k ≠ 1): use companion matrix
- `m` composite: factor as `p^e * m'` with coprime parts, apply IH and block diagonal

Note: For `m = 2`, `psi 2 = 0` means no additional dimension is needed, but there is
no 0x0 integer matrix with order 2. The crystallographic restriction theorem
handles `m = 2` separately using the hypothesis `hNm : m = 1 ∨ 0 < N`.

This theorem is used to complete the backward direction of the crystallographic
restriction theorem: if `psi m ≤ N`, then `m ∈ integerMatrixOrders N`. -/
@[blueprint "thm:mem-integerMatrixOrders-psi"
  (above := /-- With the prime power case and
  the negation trick for factors of 2, we can now prove the full result: every $m \geq 1$
  (except $m = 2$) belongs to $\mathrm{Ord}_{\psi(m)}$. The proof uses strong induction on $m$,
  factoring $m$ into coprime parts and assembling block diagonal matrices. The
  additivity of $\psi$ on coprime factors ensures the dimensions
  combine correctly. -/)
  (title := "Psi Characterizes Orders")
  (statement := /-- For $m \geq 1$ with $m \neq 2$, we have $m \in \mathrm{Ord}_{\psi(m)}$.
  The construction achieves order $m$ using exactly $\psi(m)$ dimensions via block diagonal
  matrices of cyclotomic companion matrices.
  \uses{thm:primePow-mem-integerMatrixOrders-psi, psi-def, lem:one-mem-orders} -/)
  (proof := /-- By strong induction on $m$. For $m = 1$, the identity achieves order 1 in
  dimension $\psi(1) = 0$. For prime powers $p^k$ (excluding $2^1$), the companion matrix
  of $\Phi_{p^k}$ has order $p^k$ in dimension $\varphi(p^k) = \psi(p^k)$. For composite
  $m = p^e \cdot m'$ with coprime factors, we use block diagonal of matrices achieving
  orders $p^e$ and $m'$ from the induction hypothesis, with dimension $\psi(p^e) + \psi(m')
  = \psi(m)$ by additivity of $\psi$ on coprime factors. For $m = 2 \cdot m'$ with $m'$ odd,
  negating the order-$m'$ matrix doubles the order without changing dimension. -/)
  (below := /-- The exclusion of $m = 2$ is necessary: $\psi(2) = 0$, but there is no $0 \times 0$
  integer matrix with order 2. The backward direction theorem
  handles $m = 2$ separately using the hypothesis that $N \geq 1$, since $-I_N$ has order 2
  in any positive dimension. -/)]
theorem mem_integerMatrixOrders_psi (m : ℕ) (hm : 0 < m) (hm2 : m ≠ 2) :
    m ∈ integerMatrixOrders (psi m) := by
  -- Use strong induction on m
  induction m using Nat.strong_induction_on with
  | _ m IH =>
  -- Case: m = 1
  rcases (Nat.one_le_iff_ne_zero.mpr hm.ne').eq_or_lt' with rfl | hm_gt1
  · simp only [psi_one]; exact one_mem_integerMatrixOrders 0
  · -- Case: m > 1, i.e., m >= 2
    have hm_gt2 : 2 < m := by omega
    -- Check if m is a prime power
    by_cases hpow : IsPrimePow m
    · -- m is a prime power p^k
      rw [isPrimePow_nat_iff] at hpow
      obtain ⟨p, k, hp, hk, hpk⟩ := hpow
      subst hpk
      by_cases h21 : p = 2 ∧ k = 1
      · obtain ⟨rfl, rfl⟩ := h21; simp only [pow_one] at hm_gt2; omega
      · exact primePow_mem_integerMatrixOrders_psi p k hp hk h21
    · -- m is not a prime power: use factorization_split_lt
      obtain ⟨p, e, m', hp, he_pos, hm_eq, hcop, _, hm'_lt, _⟩ :=
        factorization_split_lt (by omega : 2 < m) hpow
      by_cases h_pe_is_2 : p = 2 ∧ e = 1
      · -- p^e = 2, so m = 2 * m' with m' odd
        have hcop' : Nat.Coprime 2 m' := by simp only [h_pe_is_2.1, h_pe_is_2.2, pow_one] at hcop ⊢; exact hcop
        have ⟨hm'_odd, hm'_ne_2, hm'_ge3⟩ := odd_ne_two_ge_three_of_coprime_two hcop' (by omega)
        rw [show m = 2 * m' by simp only [h_pe_is_2.1, h_pe_is_2.2, pow_one] at hm_eq; omega]
        exact mem_integerMatrixOrders_psi_2_times_odd m' (by omega) hm'_odd hm'_ge3
          (IH m' hm'_lt (by omega) hm'_ne_2)
      · by_cases hm'_eq_2 : m' = 2
        · -- m' = 2, so m = p^e * 2 with p^e odd
          have ⟨hpe_odd, hpe_ge3⟩ := primePow_odd_ge_three_of_coprime_two hp he_pos (hm'_eq_2 ▸ hcop)
          rw [← hm_eq, hm'_eq_2]
          exact mem_integerMatrixOrders_psi_odd_times_2 (p ^ e) (Nat.pow_pos hp.pos) hpe_odd hpe_ge3
            (primePow_mem_integerMatrixOrders_psi p e hp he_pos h_pe_is_2)
        · -- Neither is 2, use block diagonal construction
          rw [← hm_eq]
          exact mem_integerMatrixOrders_psi_composite p e m' hp (by omega) hcop
            (primePow_mem_integerMatrixOrders_psi p e hp he_pos h_pe_is_2)
            (IH m' hm'_lt (by omega) hm'_eq_2)

/-- Helper for small cases: if m ∈ {3, 4, 6} and psi(m) ≤ N, then m ∈ integerMatrixOrders N. -/
private lemma mem_integerMatrixOrders_small (m N : ℕ) (hm : m ∈ ({3, 4, 6} : Finset ℕ))
    (hpsi : psi m ≤ N) : m ∈ integerMatrixOrders N := by
  have hm_ge2 : 2 ≤ m := by fin_cases hm <;> omega
  have htot_eq_2 : Nat.totient m = 2 := by fin_cases hm <;> native_decide
  have hpsi_eq_2 : psi m = 2 := by fin_cases hm <;> simp [psi_three, psi_four, psi_six]
  have hN2 : 2 ≤ N := by omega
  have hmem := mem_integerMatrixOrders_totient m hm_ge2
  rw [htot_eq_2] at hmem
  exact integerMatrixOrders_mono hN2 hmem

/-- Helper for m = 5: psi(5) = 4, so if 4 ≤ N, then 5 ∈ integerMatrixOrders N. -/
private lemma mem_integerMatrixOrders_five (N : ℕ) (hpsi : psi 5 ≤ N) :
    5 ∈ integerMatrixOrders N := by
  have hdeg : (Polynomial.cyclotomic 5 ℤ).natDegree = 4 := by
    rw [Polynomial.natDegree_cyclotomic]
    simp only [Nat.totient_prime Nat.prime_five]
  have hn : 0 < (Polynomial.cyclotomic 5 ℤ).natDegree := by omega
  have hmem : 5 ∈ integerMatrixOrders (Polynomial.cyclotomic 5 ℤ).natDegree :=
    companion_cyclotomic_mem_integerMatrixOrders 5 (by omega) hn
  rw [hdeg] at hmem
  have hN4 : 4 ≤ N := by simp only [psi_five] at hpsi; omega
  exact integerMatrixOrders_mono hN4 hmem

/-- Helper for m > 6: general case using companion matrices or psi construction. -/
private lemma mem_integerMatrixOrders_of_psi_le_large (m N : ℕ) (hm : 6 < m)
    (hpsi : psi m ≤ N) : m ∈ integerMatrixOrders N := by
  have hdeg : (Polynomial.cyclotomic m ℤ).natDegree = Nat.totient m :=
    Polynomial.natDegree_cyclotomic m ℤ
  have htot_pos : 0 < Nat.totient m := Nat.totient_pos.mpr (by omega : 0 < m)
  have hn : 0 < (Polynomial.cyclotomic m ℤ).natDegree := by omega
  -- Check if totient(m) ≤ N
  by_cases htot : Nat.totient m ≤ N
  · -- Case: totient(m) ≤ N, companion matrix works
    have hmem : m ∈ integerMatrixOrders (Polynomial.cyclotomic m ℤ).natDegree :=
      companion_cyclotomic_mem_integerMatrixOrders m (by omega) hn
    rw [hdeg] at hmem
    exact integerMatrixOrders_mono htot hmem
  · -- Case: psi(m) ≤ N < totient(m), use block diagonal construction via psi
    have hmem := mem_integerMatrixOrders_psi m (by omega) (by omega)
    exact integerMatrixOrders_mono hpsi hmem

/-- If psi(m) <= N, then there exists an N x N integer matrix with order m.

This is the backward direction of the crystallographic restriction theorem.
The construction uses companion matrices of cyclotomic polynomials.

**Construction outline:**
1. For m = 1: use identity matrix (psi(1) = 0)
2. For m = 2: use -I (psi(2) = 0)
3. For prime power p^k with p odd or k >= 2:
   - Use companion matrix of Phi_{p^k} (cyclotomic polynomial)
   - This has size phi(p^k) x phi(p^k) = psi(p^k) and order p^k
4. For general m = prod p_i^{k_i}:
   - Take block diagonal of companion matrices for each prime power factor
   - Total size is sum of phi(p_i^{k_i}) = psi(m)
5. Pad with identity blocks to reach size N x N
-/
@[blueprint "thm:backward-direction"
  (above := /-- We now assemble the full backward direction from the components developed above.
  The psi characterization theorem shows $m \in \mathrm{Ord}_{\psi(m)}$ for
  $m \neq 2$, and monotonicity of $\mathrm{Ord}$ extends this to any
  $N \geq \psi(m)$. The proof handles $m = 2$ separately using $-I$, and small cases $m \leq 6$
  by direct computation, before applying the general companion matrix construction for larger $m$.
  Together with the forward direction, this completes the crystallographic restriction:
  $m \in \mathrm{Ord}_N \iff \psi(m) \leq N$. -/)
  (title := "Backward Direction")
  (message := "Explicit construction proves psi(m) <= N is sufficient")
  (statement := /-- Backward Direction: If $\psi(m) \leq N$, then $m \in \mathrm{Ord}_N$.

  The companion matrix of a monic polynomial $p(X)$ has $p(X)$ as both its characteristic
  and minimal polynomial. For the cyclotomic polynomial $\Phi_m$, the companion matrix $C_m$
  satisfies $\Phi_m(C_m) = 0$, so $C_m^m = I$, and since $\Phi_m$ is minimal (irreducible over
  $\mathbb{Q}$ and dividing $X^m - 1$ but not $X^k - 1$ for $k < m$), we get $\mathrm{ord}(C_m) = m$.
  The key optimization in the $\psi$ function is that $\psi(2) = 0$: order 2 is achieved by $-I$
  in any dimension, so we do not need to ``pay'' $\varphi(2) = 1$ for the factor of 2.

  Proof by explicit construction:
  \begin{enumerate}
  \item For $m = 1$: Use the identity matrix (any dimension).
  \item For $m = 2$: Use $-I$ (dimension $\geq 1$), achieving order 2 without adding to $\psi$.
  \item For odd prime power $p^k$: The companion matrix of $\Phi_{p^k}$ has size $\varphi(p^k)$.
  \item For $2^k$ with $k \geq 2$: The companion matrix of $\Phi_{2^k}$ has size $\varphi(2^k) = 2^{k-1}$.
  \item For $m = 2m'$ with $m'$ odd: If $A$ has order $m'$, then $-A$ has order $2m'$ (same dimension).
  \item For general $m = \prod p_i^{k_i}$: Block diagonal of companion matrices for $p_i^{k_i}$
        with $p_i \neq 2$ or $k_i \geq 2$. The orders combine via $\mathrm{lcm}$ (which equals
        the product for coprime factors), giving total order $m$ in dimension $\psi(m)$.
  \item Pad with identity blocks to reach size $N \times N$ (padding does not change order).
  \end{enumerate}
  \uses{integerMatrixOrders-def, psi-def, companion-def, thm:companion-charpoly,
        thm:companion-cycl-order, thm:mem-orders-totient} --/)
  (proof := /-- We construct a matrix of order $m$ in dimension $\psi(m)$ by taking block diagonals
  of companion matrices for cyclotomic polynomials $\Phi_{p^k}$ of each prime power factor.
  The companion matrix $C(\Phi_{p^k})$ has order exactly $p^k$ and size $\varphi(p^k)$.
  Block diagonal matrices have order equal to the lcm of block orders, which equals $m$
  for coprime factors. Identity padding extends to dimension $N \geq \psi(m)$. --/)
  (below := /-- Combined with the forward direction, this yields the
  full crystallographic restriction: $m \in \mathrm{Ord}_N$ if and only if $\psi(m) \leq N$.
  The function $\psi$ is therefore the exact dimension cost of achieving order $m$. -/)]
theorem mem_integerMatrixOrders_of_psi_le (N m : ℕ) (hm : 0 < m)
    (hpsi : psi m ≤ N) (hNm : m = 1 ∨ 0 < N) :
    m ∈ integerMatrixOrders N := by
  -- Handle base cases m = 1, 2
  rcases Nat.lt_trichotomy m 2 with hm_lt2 | rfl | hm_gt2
  · -- m < 2 and 0 < m, so m = 1
    interval_cases m
    exact one_mem_integerMatrixOrders N
  · -- m = 2: use -I, need N > 0
    cases hNm with
    | inl h => omega
    | inr hN_pos =>
      haveI : NeZero N := ⟨Nat.pos_iff_ne_zero.mp hN_pos⟩
      exact two_mem_integerMatrixOrders N
  · -- m > 2, i.e., m >= 3
    -- If m ≤ N, use permutation matrix directly
    by_cases hle : m ≤ N
    · exact integerMatrixOrders_mono hle (mem_integerMatrixOrders_self m (by omega))
    · -- m > N: need companion matrices
      push_neg at hle
      -- Case split on m
      rcases Nat.lt_trichotomy m 5 with hm_lt5 | rfl | hm_gt5
      · -- m ∈ {3, 4}: use small case helper
        have hm34 : m ∈ ({3, 4, 6} : Finset ℕ) := by
          simp only [Finset.mem_insert, Finset.mem_singleton]
          omega
        exact mem_integerMatrixOrders_small m N hm34 hpsi
      · -- m = 5
        exact mem_integerMatrixOrders_five N hpsi
      · -- m > 5
        rcases Nat.lt_trichotomy m 6 with hm_lt6 | rfl | hm_gt6
        · omega -- impossible: 5 < m < 6
        · -- m = 6
          exact mem_integerMatrixOrders_small 6 N (by simp) hpsi
        · -- m > 6: general case
          exact mem_integerMatrixOrders_of_psi_le_large m N hm_gt6 hpsi

end Crystallographic
