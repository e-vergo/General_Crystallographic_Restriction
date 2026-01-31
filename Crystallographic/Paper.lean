/-
The Crystallographic Restriction Theorem: A Formalized Proof in Lean 4

This is the Verso/SBSBlueprint version of the paper, equivalent to paper.tex
but authored directly in Lean.

Authors: Eric Vergo, Claude (Anthropic)
-/
import SBSBlueprint

open Verso.Genre.SBSBlueprint

set_option maxRecDepth 2048

#doc (SBSBlueprint) "The Crystallographic Restriction Theorem: A Formalized Proof in Lean 4" =>

%%%
authors := ["Eric Vergo", "Claude (Anthropic)"]
%%%

# Abstract

We present a complete formalization in the Lean 4 proof assistant of the crystallographic
restriction theorem, which characterizes exactly which finite orders can be achieved by integer
matrices of a given dimension. The theorem states that an $N \times N$ matrix with integer
entries can have finite order $m$ if and only if $\psi(m) \leq N$, where $\psi$ is a function
closely related to Euler's totient function. This elegant result connects linear algebra over
the integers with number-theoretic properties and explains why crystal lattices can only exhibit
2-, 3-, 4-, or 6-fold rotational symmetry. Our formalization follows the exposition of Kuzmanovich
and Pavlichenkov, establishing both the forward direction (necessity) via minimal polynomial theory
and the backward direction (sufficiency) via explicit construction using companion matrices of
cyclotomic polynomials.

# Introduction

Finite groups of matrices with integer entries arise naturally in many areas of mathematics and
physics. In crystallography, the symmetry groups of crystal lattices are realized as finite subgroups
of $\mathrm{GL}(n,\mathbb{Z})$, the group of $n \times n$ matrices with integer entries whose inverses
also have integer entries. A fundamental question is: *which finite orders can elements of
$\mathrm{GL}(n,\mathbb{Z})$ have?*

The answer involves a beautiful interplay between linear algebra, number theory, and algebra.
Minkowski proved the remarkable result that $\mathrm{GL}(n, \mathbb{Z})$ contains only finitely many
isomorphism classes of finite subgroups, which implies that there are only finitely many possible
orders for elements of finite order. The crystallographic restriction theorem provides a precise
characterization of these orders.

## Historical Context

The name "crystallographic restriction" originates from the physical study of crystals. A crystal
lattice in $\mathbb{R}^n$ is a discrete subgroup of translations, and the rotational symmetries of
such a lattice must preserve the lattice structure. This requirement severely constrains the possible
rotation angles.

In two and three dimensions, the classical crystallographic restriction states that a rotation
preserving a lattice must have order 1, 2, 3, 4, or 6. This explains why crystals can have 2-fold,
3-fold, 4-fold, or 6-fold rotational symmetry, but never 5-fold or 7-fold symmetry---a fact observed
experimentally long before it was proved mathematically.

The general theorem we formalize extends this to all dimensions, answering completely which
orders are achievable in $\mathrm{GL}(N, \mathbb{Z})$ for any $N$.

## Statement of the Main Result

The characterization involves a function $\psi : \mathbb{N} \to \mathbb{N}$ that we call the
*dimensional cost function*. Informally, $\psi(m)$ measures the minimum dimension needed to
construct an integer matrix of order $m$.

:::paperStatement "thm:main-theorem"

The function $\psi$ is defined as follows. For a prime power $p^k$:
$$\psi_{\text{pp}}(p, k) = \begin{cases}
0 & \text{if } k = 0, \\
0 & \text{if } p = 2 \text{ and } k = 1, \\
\varphi(p^k) & \text{otherwise},
\end{cases}$$
where $\varphi$ denotes Euler's totient function. For a general positive integer
$m = \prod_i p_i^{k_i}$, we define $\psi(m) = \sum_i \psi_{\text{pp}}(p_i, k_i)$.

The special treatment of $2^1$ reflects the fact that order 2 is "free" in any positive dimension:
the matrix $-I$ has order 2 in any dimension $N \geq 1$.

## Significance and Applications

The crystallographic restriction has several notable consequences:

1. **Classical 2D/3D restriction:** Since $\psi(m) \leq 2$ only for $m \in \{1, 2, 3, 4, 6\}$, these
   are the only achievable orders in dimensions 2 and 3, explaining the observed rotational
   symmetries of crystals.

2. **Dimension parity:** Since $\psi(m)$ is always even for $m > 2$, the achievable orders in
   dimension $2k$ are the same as in dimension $2k + 1$. This surprising result means that odd
   dimensions offer no new orders beyond their even predecessors.

3. **First occurrence of orders:** The theorem determines exactly when each order first becomes
   achievable. For instance, order 5 requires dimension at least 4 (since $\psi(5) = \varphi(5) = 4$),
   while order 7 requires dimension at least 6.

## Overview of the Proof

Our formalization follows the proof structure of Kuzmanovich and Pavlichenkov. The proof
proceeds in two directions:

**Forward direction (necessity):** If an $N \times N$ integer matrix $A$ has order $m$, we show
$\psi(m) \leq N$. The key insight is that the minimal polynomial of $A$ (viewed over $\mathbb{Q}$)
must be a product of distinct cyclotomic polynomials $\Phi_d$ for various divisors $d$ of $m$.
The constraint that the order is exactly $m$ forces the lcm of these divisors to equal $m$,
leading to the dimension bound.

**Backward direction (sufficiency):** If $\psi(m) \leq N$, we construct an explicit $N \times N$
integer matrix with order $m$. The construction uses companion matrices of cyclotomic polynomials
combined via block diagonal matrices.

The formalization required developing substantial supporting infrastructure, including properties
of cyclotomic polynomials, companion matrices, block diagonal constructions, and the $\psi$
function itself.

# Preliminaries

We establish notation and recall the key definitions needed for the proof.

## Notation and Conventions

Throughout, we use the following notation:
- $\mathbb{N}$ denotes the natural numbers $\{0, 1, 2, \ldots\}$
- $\mathbb{Z}$ denotes the integers
- $\mathbb{Q}$ denotes the rational numbers
- $\mathrm{GL}(N, \mathbb{Z})$ denotes the group of $N \times N$ invertible integer matrices
- $\varphi(m)$ denotes Euler's totient function
- $\Phi_m(X)$ denotes the $m$-th cyclotomic polynomial
- $\mathrm{ord}(A)$ denotes the multiplicative order of a matrix $A$ (the smallest positive $k$
  with $A^k = I$)

For a matrix $A$ with $A^m = I$ for some $m > 0$, we say $A$ has *finite order*, and
$\mathrm{ord}(A)$ is the smallest such $m$.

We write $p^k \| m$ to mean that $p^k$ is the exact power of $p$ dividing $m$, that is,
$p^k \mid m$ but $p^{k+1} \nmid m$.

## The Psi Function

The dimensional cost function $\psi$ is central to the crystallographic restriction. We first
define it on prime powers.

:::paperStatement "psiPrimePow-def"

The function $\psi_{\text{pp}}(p, k)$ equals $\varphi(p^k) = (p-1)p^{k-1}$ in most cases, with two
exceptions: $\psi_{\text{pp}}(p, 0) = 0$ for any prime $p$, and $\psi_{\text{pp}}(2, 1) = 0$. The
latter exception captures the fact that order 2 requires no "dimensional cost" since $-I$ has
order 2 in any positive dimension.

:::paperStatement "psi-def"

## Properties of Psi

Several properties of $\psi$ are essential for the proof.

**Explicit Values.** For small values of $m$:

| $m$ | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 |
|-----|---|---|---|---|---|---|---|---|---|----|----|----|
| $\psi(m)$ | 0 | 0 | 2 | 2 | 4 | 2 | 6 | 4 | 6 | 4 | 10 | 4 |

:::paperFull "lem:psi-prime-pow"

The power of $\psi$ comes from its additivity on coprime factors.

:::paperFull "lem:psi-coprime-add"

The function $\psi$ is bounded above by the totient function.

:::paperFull "lem:psi-le-totient"

**Remark.** The only case where $\psi(m) < \varphi(m)$ is when $2 \| m$ (that is, $m$ is divisible
by 2 but not by 4). In this case, the factor of 2 contributes $\varphi(2) = 1$ to the totient but
0 to $\psi$.

# Companion Matrices

Companion matrices are the fundamental tool for constructing matrices with prescribed characteristic
polynomials. They play a central role in the backward direction of our proof.

## Definition and Basic Properties

:::paperStatement "companion-def"

The companion matrix of a monic polynomial provides a canonical matrix realization
whose characteristic polynomial equals the original polynomial.

:::paperFull "thm:companion-charpoly"

By the Cayley-Hamilton theorem, every matrix satisfies its characteristic polynomial. For
companion matrices, this means the defining polynomial evaluates to zero at the companion matrix.

:::paperFull "lem:companion-aeval-zero"

:::paperFull "thm:companion-pow-dvd"

## Cyclotomic Companion Matrices

When we apply the companion matrix construction to cyclotomic polynomials, we obtain integer
matrices with precisely controlled finite orders.

Recall that the $m$-th cyclotomic polynomial $\Phi_m(X)$ is the minimal polynomial over $\mathbb{Q}$
of a primitive $m$-th root of unity. It has three crucial properties:
1. $\Phi_m(X)$ has integer coefficients.
2. $\Phi_m(X)$ has degree $\varphi(m)$.
3. $\Phi_m(X)$ divides $X^m - 1$ but does not divide $X^k - 1$ for any $0 < k < m$.

:::paperFull "lem:companion-cycl-pow"

:::paperFull "thm:companion-cycl-order"

:::paperFull "thm:companion-cycl-mem"

This gives us the key result for constructing matrices of prescribed order.

:::paperFull "thm:mem-orders-totient"

**Example.** The cyclotomic polynomial $\Phi_3(X) = X^2 + X + 1$ has companion matrix
$$C(\Phi_3) = \begin{pmatrix} 0 & -1 \\ 1 & -1 \end{pmatrix}.$$
One can verify directly: $C(\Phi_3)^2 = \begin{pmatrix} -1 & 1 \\ -1 & 0 \end{pmatrix}$ and
$C(\Phi_3)^3 = I$. This $2 \times 2$ integer matrix has order exactly 3.

**Example.** The cyclotomic polynomial $\Phi_6(X) = X^2 - X + 1$ has companion matrix
$$C(\Phi_6) = \begin{pmatrix} 0 & -1 \\ 1 & 1 \end{pmatrix}.$$
This $2 \times 2$ matrix has order 6, demonstrating that order 6 is achievable in dimension 2.

# Block Diagonal Matrices

To construct matrices of arbitrary orders from companion matrices of cyclotomic polynomials, we
use block diagonal combinations.

## Definition

:::paperStatement "def:blockDiag2"

This construction extends naturally to any finite number of blocks.

## Order of Block Diagonal Matrices

:::paperFull "lem:blockDiag2-one"

:::paperFull "lem:blockDiag2-mul"

:::paperFull "lem:blockDiag2-pow"

:::paperFull "thm:orderOf-blockDiag2"

**Corollary.** If $A$ has order $a$, $B$ has order $b$, and $\gcd(a, b) = 1$, then
$\mathrm{diag}(A, B)$ has order $ab$.

:::paperFull "lem:lcm-mem-orders"

# The Forward Direction

We now prove that if an integer matrix has order $m$, then its dimension must be at least $\psi(m)$.

## Minimal Polynomials of Matrices with Finite Order

Let $A \in \mathrm{GL}(N, \mathbb{Z})$ be a matrix with finite order $m$. Since $A^m = I$, the
polynomial $X^m - 1$ annihilates $A$. The minimal polynomial $\mu_A$ of $A$ (over $\mathbb{Q}$)
therefore divides $X^m - 1$.

**Lemma.** Over $\mathbb{Q}$, we have the factorization
$$X^m - 1 = \prod_{d \mid m} \Phi_d(X),$$
where the product is over all positive divisors $d$ of $m$.

This is a standard result: every $m$-th root of unity is a primitive $d$-th root of unity for
exactly one divisor $d$ of $m$.

:::paperFull "lem:pow-eq-one-of-minpoly-dvd"

:::paperFull "lem:minpoly-dvd-X-pow-sub-one"

## The Order Constraint

:::paperFull "lem:cyclotomic-finset-product-dvd"

:::paperFull "lem:minpoly-dvd-prod-cyclotomic"

:::paperFull "lem:minpoly-eq-prod-cyclotomic"

:::paperFull "lem:cyclotomic-divisors-lcm-eq"

## The Key Inequality

The heart of the forward direction is the following combinatorial lemma about subsets of divisors.

:::paperFull "lem:sum-totient-ge-psi"

## Proof of the Forward Direction

:::paperFull "thm:forward-direction"

# The Backward Direction

We now show that every order satisfying the necessary condition is actually achievable.

## Prime Power Orders

By Corollary 3.7, for any prime power $p^k$ with $k \geq 1$, the companion matrix $C(\Phi_{p^k})$
achieves order $p^k$ in dimension $\varphi(p^k)$.

:::paperFull "thm:primePow-mem-integerMatrixOrders-psi"

## Order 2 is Free

The special case $(p, k) = (2, 1)$ requires separate treatment.

:::paperFull "lem:two-mem-orders"

This is why $\psi(2) = 0$: achieving order 2 costs nothing beyond having at least one dimension.

:::paperFull "lem:orderOf-neg-of-odd-order"

**Corollary.** If order $k$ (odd) is achievable in dimension $N$, then order $2k$ is achievable
in dimension $N$.

## General Construction

:::paperFull "thm:mem-integerMatrixOrders-psi"

:::paperFull "thm:backward-direction"

**Example (Order 12 in Dimension 4).** We have $12 = 4 \cdot 3 = 2^2 \cdot 3$, so we use Case 3
with $a = 2$ and $m' = 3$.

For the factor $2^2 = 4$: $C(\Phi_4) = C(X^2 + 1) = \begin{pmatrix} 0 & -1 \\ 1 & 0 \end{pmatrix}$,
which has order 4 and dimension $\varphi(4) = 2$.

For the factor 3: $C(\Phi_3) = \begin{pmatrix} 0 & -1 \\ 1 & -1 \end{pmatrix}$, which has order 3
and dimension $\varphi(3) = 2$.

The block diagonal
$$\mathrm{diag}(C(\Phi_4), C(\Phi_3)) = \begin{pmatrix}
0 & -1 & 0 & 0 \\
1 & 0 & 0 & 0 \\
0 & 0 & 0 & -1 \\
0 & 0 & 1 & -1
\end{pmatrix}$$
has order $\mathrm{lcm}(4, 3) = 12$ and dimension $2 + 2 = 4 = \psi(12)$.

# The Crystallographic Restriction Theorem

We now combine the forward and backward directions.

## The Main Result

:::paperFull "thm:main-theorem"

:::paperStatement "integerMatrixOrders-def"

**Corollary.** $\mathrm{Ord}_N = \{m \geq 1 : \psi(m) \leq N\}$.

## The Classical Crystallographic Restriction

**Corollary (Classical Restriction).** In dimensions 2 and 3, the achievable orders are exactly
$\{1, 2, 3, 4, 6\}$.

*Proof.* From the explicit values table, $\psi(m) \leq 2$ if and only if $m \in \{1, 2, 3, 4, 6\}$:
- $\psi(1) = \psi(2) = 0 \leq 2$ (check)
- $\psi(3) = \psi(4) = \psi(6) = 2 \leq 2$ (check)
- $\psi(5) = 4 > 2$ (cross)
- $\psi(7) = 6 > 2$ (cross)

Since $\psi(m) \leq 3$ if and only if $\psi(m) \leq 2$ (as $\psi(m)$ is always even for $m > 2$),
the achievable orders in dimensions 2 and 3 coincide.

This explains why crystals in our three-dimensional world exhibit only 2-, 3-, 4-, and 6-fold
rotational symmetries: these correspond to the elements of orders 2, 3, 4, and 6 in
$\mathrm{GL}(3, \mathbb{Z})$.

## Dimension Parity

**Corollary.** For $k \geq 1$, the sets $\mathrm{Ord}_{2k}$ and $\mathrm{Ord}_{2k+1}$ are equal.

*Proof.* For $m > 2$, the value $\psi(m) = \sum_{(p,k) \neq (2,1)} \varphi(p^k)$ is a sum of terms
$\varphi(p^k) = (p-1)p^{k-1}$. Each such term is even: if $p$ is odd, then $p - 1$ is even; if
$p = 2$ and $k \geq 2$, then $p^{k-1} = 2^{k-1}$ is even. Thus $\psi(m)$ is even for all $m \geq 1$.
The condition $\psi(m) \leq 2k$ is equivalent to $\psi(m) \leq 2k + 1$.

This means that passing from an even dimension to the next odd dimension never unlocks new
achievable orders.

## First Occurrence Table

The following table shows when each small order first becomes achievable:

| Order $m$ | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 |
|-----------|---|---|---|---|---|---|---|---|---|----|----|----|
| $\psi(m)$ | 0 | 0 | 2 | 2 | 4 | 2 | 6 | 4 | 6 | 4 | 10 | 4 |
| First dimension | 1 | 1 | 2 | 2 | 4 | 2 | 6 | 4 | 6 | 4 | 10 | 4 |

We observe:
- Orders 1 and 2 are achievable in dimension 1 (the smallest possible).
- Orders 3, 4, 6 first appear in dimension 2.
- Orders 5, 8, 10, 12 first appear in dimension 4.
- Orders 7, 9 first appear in dimension 6.
- Order 11 requires dimension 10.

# References

1. J. Kuzmanovich and A. Pavlichenkov. *Finite groups of matrices whose entries are integers.*
   The American Mathematical Monthly, 109(2):173--186, 2002.

2. J. Bamberg, G. Cairns, and D. Kilminster. *The crystallographic restriction, permutations,
   and Goldbach's conjecture.* The American Mathematical Monthly, 110(3):202--209, 2003.

3. M. Newman. *Integral Matrices.* Academic Press, New York, 1972.

4. D. S. Dummit and R. M. Foote. *Abstract Algebra.* Prentice Hall, 3rd edition, 2004.

5. S. Lang. *Algebra.* Springer, 3rd edition, 2002.
