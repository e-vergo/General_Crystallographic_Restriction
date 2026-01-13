/-
Copyright (c) 2026 Eric Vergo. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Eric Vergo
-/
import Architect
import Crystallographic.CrystallographicRestriction.Backward
import Crystallographic.CrystallographicRestriction.Forward
import Crystallographic.FiniteOrder.Basic
import Crystallographic.Psi.Basic

/-!
# The Crystallographic Restriction Theorem

This file contains the statement and proof of the crystallographic restriction theorem.

## Main Result

The crystallographic restriction theorem characterizes which orders are achievable
by N×N integer matrices: an order m is achievable if and only if psi(m) ≤ N.

The psi function is defined as:
- psi(1) = psi(2) = 0
- For other m, psi(m) = sum over prime power factors p^k of phi(p^k),
  except psi(2) = 0 contributes nothing.

## Main results

* `crystallographic_restriction` - The complete theorem

## References

* Sasse, R. (2020). "Crystallographic Groups"
-/

namespace Crystallographic

/-- **The Crystallographic Restriction Theorem:**
An N×N integer matrix can have finite order m if and only if psi(m) ≤ N.

This characterizes exactly which rotation orders are possible in N-dimensional
crystallographic groups. -/
@[blueprint "thm:main-theorem"
  (statement := /-- \textbf{The Crystallographic Restriction Theorem:}
  An $N \times N$ integer matrix can have finite order $m$ if and only if $\psi(m) \leq N$.

  Equivalently: $m \in \mathrm{Ord}_N \iff \psi(m) \leq N$.

  This theorem completely characterizes which rotation orders are achievable by
  integer matrices in each dimension. The function $\psi$ is defined as:
  $\psi(1) = \psi(2) = 0$, and for other $m$, $\psi(m) = \sum_{p^k \| m, p \neq 2 \text{ or } k \geq 2} \varphi(p^k)$.

  \textbf{Forward direction:} If $A \in \mathbb{Z}^{N \times N}$ has order $m$, the minimal polynomial
  of $A$ over $\mathbb{Q}$ divides $X^m - 1$ and must include cyclotomic factors $\Phi_d$ for
  divisors $d$ whose lcm equals $m$. The sum of $\varphi(d)$ over these divisors is at least $\psi(m)$,
  and this sum bounds the degree of the minimal polynomial, which is at most $N$.

  \textbf{Backward direction:} For each prime power $p^k$ (with $p \neq 2$ or $k \geq 2$),
  the companion matrix of $\Phi_{p^k}$ has size $\varphi(p^k)$ and order $p^k$. For general $m$,
  block diagonal combinations of these companion matrices achieve order $m$ in dimension $\psi(m)$.
  \uses{thm:forward-direction, thm:backward-direction} --/)
  (proof := /-- The proof combines the forward and backward directions. The forward direction shows
  that eigenvalue constraints force $\psi(m) \leq N$. The backward direction constructs explicit
  matrices achieving each order using companion matrices of cyclotomic polynomials. --/)]
theorem crystallographic_restriction (N m : ℕ) (hm : 0 < m) (hNm : m = 1 ∨ 0 < N) :
    m ∈ integerMatrixOrders N ↔ psi m ≤ N :=
  ⟨psi_le_of_mem_integerMatrixOrders N m hm,
   fun hpsi => mem_integerMatrixOrders_of_psi_le N m hm hpsi hNm⟩

end Crystallographic
