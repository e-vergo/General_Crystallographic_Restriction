# Crystallographic Restriction Theorem

A formal verification in Lean 4 of the crystallographic restriction theorem, which characterizes exactly which rotation orders are achievable by integer matrices in arbitrary dimension.

## Mathematical Statement

**Main Theorem.** An N x N integer matrix can have finite order m if and only if psi(m) <= N.

### The psi Function

The function psi : N -> N determines the minimum dimension required to realize a given order:

- psi(1) = 0
- psi(2) = 0
- For m = prod p_i^{k_i} (prime factorization):

  psi(m) = sum phi(p_i^{k_i}), excluding the term phi(2) when 2^1 exactly divides m

Equivalently, psi(m) equals the sum of Euler's totient function over the prime power factors of m, with the special case that a single factor of 2 contributes nothing (since -I has order 2 in any dimension >= 1).

### Achievable Orders by Dimension

| Dimension N | Achievable orders m with psi(m) <= N |
|-------------|--------------------------------------|
| 0           | {1} |
| 1           | {1, 2} |
| 2           | {1, 2, 3, 4, 6} |
| 3           | {1, 2, 3, 4, 6} |
| 4           | {1, 2, 3, 4, 5, 6, 8, 10, 12} |
| 5           | {1, 2, 3, 4, 5, 6, 8, 10, 12} |
| 6           | {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 18} |

### The 2D Crystallographic Restriction

The classical crystallographic restriction theorem states that 2D lattice symmetries can only have rotational orders in {1, 2, 3, 4, 6}. This follows immediately from our general theorem: psi(m) <= 2 holds exactly for m in {1, 2, 3, 4, 6}.

| m | psi(m) | Achievable in 2D? |
|---|--------|-------------------|
| 1 | 0      | Yes |
| 2 | 0      | Yes |
| 3 | 2      | Yes |
| 4 | 2      | Yes |
| 5 | 4      | No  |
| 6 | 2      | Yes |
| 7 | 6      | No  |

## Proof Strategy

### Forward Direction: If A has order m, then psi(m) <= N

1. Let A be an N x N integer matrix with orderOf(A) = m
2. The minimal polynomial of A (over Q) divides X^m - 1
3. Since orderOf(A) = m exactly, the minimal polynomial is the product of cyclotomic polynomials Phi_d for a set S of divisors of m with lcm(S) = m
4. The degree of the minimal polynomial equals sum_{d in S} phi(d)
5. By a key lemma (sum_totient_ge_psi_of_lcm_eq), this sum is >= psi(m)
6. Since the minimal polynomial degree <= characteristic polynomial degree = N, we get psi(m) <= N

### Backward Direction: If psi(m) <= N, construct a matrix with order m

1. **Base cases:**
   - m = 1: The identity matrix has order 1
   - m = 2: The matrix -I has order 2 (for N >= 1)

2. **Prime powers p^k (excluding 2^1):**
   - The companion matrix of the cyclotomic polynomial Phi_{p^k} has dimension phi(p^k) and order p^k
   - Since psi(p^k) = phi(p^k) in this case, this provides the required matrix

3. **Composite m with coprime factorization m = m_1 * m_2:**
   - Recursively construct matrices A_1 and A_2 with orders m_1 and m_2
   - The block diagonal matrix has order lcm(m_1, m_2) = m_1 * m_2

4. **Padding:** If the constructed matrix has dimension psi(m) < N, pad with identity blocks

## Project Structure

```
Crystallographic/
  Definitions/
    Psi.lean                  -- The psi function and its properties
    IntegerMatrixOrder.lean   -- Integer matrix orders, block diagonal lemmas
    CompanionMatrix.lean      -- Companion matrix definition
    RotationMatrices.lean     -- Explicit 2x2 rotation matrices
  Proofs/
    PsiLowerBound.lean        -- sum_totient_ge_psi_of_lcm_eq
    CompanionMatrix.lean      -- Companion matrices of cyclotomic polynomials
    RotationMatrices.lean     -- Proofs for explicit rotation matrices
    CrystallographicRestriction.lean -- Main proof components
  MainTheorem.lean            -- Theorem statement
  ProofOfMainTheorem.lean     -- Final proof assembly
```

## Building

```bash
lake build
```

## References

- Sasse, R. (2020). "Crystallographic Groups"
