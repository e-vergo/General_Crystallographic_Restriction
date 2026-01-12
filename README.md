# Crystallographic Restriction Theorem

A formal verification in Lean 4 of the crystallographic restriction theorem, which characterizes exactly which rotation orders are achievable by integer matrices in arbitrary dimension.

## Main Result

**Theorem (Crystallographic Restriction).** An N x N integer matrix can have finite order m if and only if psi(m) <= N.

```lean
theorem crystallographic_restriction (N m : ℕ) (hm : 0 < m) (hNm : m = 1 ∨ 0 < N) :
    m ∈ integerMatrixOrders N ↔ psi m ≤ N
```

## The Psi Function

The function `psi : N -> N` determines the minimum dimension required to realize a given order:

- `psi(1) = 0`
- `psi(2) = 0`
- For m with prime factorization m = prod p_i^{k_i}:
  `psi(m) = sum phi(p_i^{k_i})`, excluding the term `phi(2)` when 2^1 exactly divides m

The special case for 2^1 reflects that -I has order 2 in any dimension >= 1.

| m      | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 12 |
|--------|---|---|---|---|---|---|---|---|---|----|----|
| psi(m) | 0 | 0 | 2 | 2 | 4 | 2 | 6 | 4 | 6 | 4  | 4  |

## Project Structure

```
Crystallographic/
  MainTheorem.lean                     -- Main theorem statement and proof
  Psi/
    Basic.lean                         -- Definition of the psi function
    Bounds.lean                        -- Bounds on psi values
  FiniteOrder/
    Basic.lean                         -- Integer matrix orders definition
    Order.lean                         -- Order properties
  Companion/
    Cyclotomic.lean                    -- Companion matrices of cyclotomic polynomials
  CrystallographicRestriction/
    Forward.lean                       -- Forward direction: order m implies psi(m) <= N
    Backward.lean                      -- Backward direction: psi(m) <= N implies order m achievable
  Companion.lean                       -- Companion matrix infrastructure
  Lemmas.lean                          -- Supporting lemmas
```

## Building

```bash
lake build
```

## Dependencies

- Mathlib v4.26.0

## Author

Eric Vergo

## License

MIT License

## References

- Sasse, R. (2020). "Crystallographic Groups"
