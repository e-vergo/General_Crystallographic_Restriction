/-
Verso blueprint document for the Crystallographic Restriction Theorem.
Complete conversion from blueprint/src/blueprint.tex to Verso SBSBlueprint genre.
-/
import SBSBlueprint

open Verso.Genre.SBSBlueprint

set_option maxRecDepth 2048

#doc (SBSBlueprint) "The Crystallographic Restriction Theorem" =>

# Introduction

We present a complete formalization of the crystallographic restriction theorem,
which characterizes exactly which finite orders can be achieved by integer
matrices of a given dimension. The theorem states that an $N \times N$ matrix
with integer entries can have finite order $m$ if and only if $\psi(m) \leq N$,
where $\psi$ is a function closely related to Euler's totient function.

# Companion Matrices

Companion matrices provide a systematic way to construct matrices with prescribed
characteristic polynomials, making them the fundamental tool for achieving specific
matrix orders.

## Basic Definitions

Given a monic polynomial $p(X) = X^n + a_{n-1}X^{n-1} + \cdots + a_1 X + a_0$,
its companion matrix is the $n \times n$ matrix with ones on the subdiagonal and
the negated coefficients in the last column.

The companion matrix of a monic polynomial provides a canonical matrix realization
whose characteristic polynomial equals the original polynomial.

:::leanNode "companion-def"
:::

## Characteristic Polynomial

The fundamental property of companion matrices is that their characteristic
polynomial equals the defining polynomial.

:::leanNode "thm:companion-charpoly"
:::

Since the companion matrix satisfies its own characteristic polynomial
(by Cayley-Hamilton), evaluating the defining polynomial at the companion
matrix gives zero.

:::leanNode "lem:companion-aeval-zero"
:::

This immediately gives us control over powers of the companion matrix:
if $p(X)$ divides $X^m - 1$, then $C(p)^m = I$.

:::leanNode "thm:companion-pow-dvd"
:::

## Cyclotomic Companion Matrices

Companion matrices of cyclotomic polynomials have particularly nice properties:
they are integer matrices with prescribed finite order.

:::leanNode "lem:companion-cycl-pow"
:::

The order of the companion matrix of $\Phi_m$ is exactly $m$.

:::leanNode "thm:companion-cycl-order"
:::

Since $\Phi_m$ has integer coefficients, the companion matrix has integer entries.

:::leanNode "thm:companion-cycl-mem"
:::

This gives us the key result for constructing matrices of prescribed order:
the companion matrix of $\Phi_m$ achieves order $m$ in dimension $\varphi(m)$.

:::leanNode "thm:mem-orders-totient"
:::

# The Psi Function

The $\psi$ function is the key invariant that characterizes achievable matrix
orders. It refines Euler's totient function $\varphi$ by accounting for the
special role of order 2.

## Definition

The function $\psi : \mathbb{N} \to \mathbb{N}$ computes the minimum dimension
needed to achieve a given order. The key insight is that order 2 is "free" in
any positive dimension (achieved by $-I$), so we should not count the
$\varphi(2) = 1$ contribution from a single factor of 2.

:::leanNode "psiPrimePow-def"
:::

For a general positive integer $m$ with prime factorization
$m = \prod_i p_i^{k_i}$, we define $\psi(m) = \sum_i \psi_{\mathrm{pp}}(p_i, k_i)$.

:::leanNode "psi-def"
:::

## Basic Properties

For a prime power $p^k$ (with $k \geq 1$), $\psi(p^k)$ equals $\varphi(p^k)$
in all cases except $\psi(2) = 0$.

:::leanNode "lem:psi-prime-pow"
:::

The power of $\psi$ comes from its additivity on coprime factors. When
$\gcd(m, n) = 1$, the prime factorizations of $m$ and $n$ are disjoint.

:::leanNode "lem:factorization-disjoint"
:::

This disjointness gives us the key additivity property.

:::leanNode "lem:psi-coprime-add"
:::

The function $\psi$ is bounded below by the contribution from any single
prime power factor.

:::leanNode "lem:psi-ge-psiPrimePow"
:::

## Bounds

These bounds on the $\psi$ function are essential for the forward direction
of the main theorem.

:::leanNode "lem:two-le-totient-prime-pow"
:::

The following lemma provides a way to factor composite numbers that are not
prime powers, which is crucial for the inductive structure of our proofs.

:::leanNode "lem:factorization-split-lt"
:::

For odd numbers at least 3, $\psi$ is strictly positive.

:::leanNode "lem:psi-pos-of-odd"
:::

The function $\psi$ is bounded above by the totient function.

:::leanNode "lem:psi-le-totient"
:::

The following lemmas establish key properties about sets of divisors whose
lcm equals a given value. These are essential for the forward direction.

:::leanNode "lem:prime-pow-achieved-of-lcm-eq"
:::

:::leanNode "lem:finset-nonempty-of-two-le-lcm"
:::

:::leanNode "lem:finset-exists-one-lt-of-two-le-lcm"
:::

The crucial bound relating sums of totients to $\psi$.

:::leanNode "lem:sum-totient-ge-psi"
:::

# Integer Matrix Orders

This chapter develops the theory of finite orders achievable by integer
matrices, including closure properties under block diagonal operations
that are essential for the backward direction.

## Basic Properties

We define $\mathrm{Ord}_N$ as the set of finite orders achievable by
$N \times N$ integer matrices.

:::leanNode "integerMatrixOrders-def"
:::

The identity matrix has order 1, so $1 \in \mathrm{Ord}_N$ for all $N$.

:::leanNode "lem:one-mem-orders"
:::

For $N \geq 1$, the matrix $-I$ has order 2.

:::leanNode "lem:two-mem-orders"
:::

The set of achievable orders is monotone in dimension.

:::leanNode "lem:orders-mono"
:::

## Block Diagonal Matrices

Block diagonal matrices are essential for combining matrices with
coprime orders.

:::leanNode "def:blockDiag2"
:::

Block diagonal respects the identity.

:::leanNode "lem:blockDiag2-one"
:::

Block diagonal respects multiplication.

:::leanNode "lem:blockDiag2-mul"
:::

This gives us a monoid homomorphism structure.

:::leanNode "def:blockDiag2-prodMonoidHom"
:::

A block diagonal matrix equals the identity iff both blocks equal the identity.

:::leanNode "lem:blockDiag2-eq-one"
:::

Powers distribute over block diagonal.

:::leanNode "lem:blockDiag2-pow"
:::

## Order Results

The order of a block diagonal matrix is the lcm of the block orders.

:::leanNode "thm:orderOf-blockDiag2"
:::

This gives us the key closure property: $\mathrm{Ord}_N$ is closed under
lcm for dimensions that accommodate both factors.

:::leanNode "lem:lcm-mem-orders"
:::

For coprime orders, the lcm equals the product, so we can combine
coprime orders.

:::leanNode "lem:mul-mem-orders-coprime"
:::

# The Crystallographic Restriction

This chapter contains the forward and backward directions of the
crystallographic restriction theorem.

## Forward Direction

The forward direction shows that if an $N \times N$ integer matrix has
order $m$, then $\psi(m) \leq N$. The proof uses eigenvalue theory.

The first lemma transfers polynomial divisibility to matrix powers.

:::leanNode "lem:pow-eq-one-of-minpoly-dvd"
:::

Conversely, if $A^m = I$ then the minimal polynomial divides $X^m - 1$.

:::leanNode "lem:minpoly-dvd-X-pow-sub-one"
:::

When cyclotomic polynomials divide a target, so does their product.

:::leanNode "lem:cyclotomic-finset-product-dvd"
:::

The minimal polynomial divides the product of just those cyclotomic
polynomials that divide it.

:::leanNode "lem:minpoly-dvd-prod-cyclotomic"
:::

In fact, the minimal polynomial equals this product.

:::leanNode "lem:minpoly-eq-prod-cyclotomic"
:::

The key constraint: if $\mathrm{ord}(A) = m$ and $\mu_A = \prod_{d \in S} \Phi_d$,
then $\mathrm{lcm}(S) = m$.

:::leanNode "lem:cyclotomic-divisors-lcm-eq"
:::

The forward direction theorem.

:::leanNode "thm:forward-direction"
:::

## Backward Direction

The backward direction shows that if $\psi(m) \leq N$, then there exists
an $N \times N$ integer matrix with order $m$.

First, we establish properties of permutation matrices.

:::leanNode "lem:permMatrix-one"
:::

:::leanNode "lem:permMatrix-mul"
:::

:::leanNode "lem:permMatrix-pow"
:::

:::leanNode "lem:permMatrix-eq-one-iff"
:::

:::leanNode "lem:orderOf-permMatrix"
:::

:::leanNode "lem:orderOf-finRotate"
:::

:::leanNode "lem:orderOf-permMatrix-finRotate"
:::

This gives us that $m \in \mathrm{Ord}_m$ for $m \geq 2$.

:::leanNode "lem:mem-integerMatrixOrders-self"
:::

For prime powers (excluding $2^1$), we use cyclotomic companion matrices.

:::leanNode "thm:primePow-mem-integerMatrixOrders-psi"
:::

The general case uses strong induction, combining the prime power result
with block diagonal constructions for composite $m$.

:::leanNode "thm:mem-integerMatrixOrders-psi"
:::

The backward direction theorem.

:::leanNode "thm:backward-direction"
:::

# Main Results

This chapter contains the main theorem and its supporting lemmas,
bringing together all the machinery developed in previous chapters.

## Supporting Lemmas

Several auxiliary results are needed for the final synthesis.

:::leanNode "lem:sum-le-prod"
:::

:::leanNode "lem:lcm-factorization-le-sup"
:::

:::leanNode "lem:primePow-mem-of-lcm-eq"
:::

:::leanNode "lem:totient-ge-two"
:::

:::leanNode "lem:prod-coprime-dvd"
:::

:::leanNode "lem:totient-prod-coprime"
:::

A key lemma for the construction: if $A$ has odd order $m$, then $-A$
has order $2m$.

:::leanNode "lem:orderOf-neg-of-odd-order"
:::

## The Main Theorem

The crystallographic restriction theorem provides a necessary and sufficient
condition for an order to be achievable by integer matrices of a given
dimension: $m \in \mathrm{Ord}_N$ if and only if $\psi(m) \leq N$.

:::leanNode "thm:main-theorem"
:::
