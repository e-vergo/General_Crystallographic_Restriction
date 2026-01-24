# Crystallographic Restriction Theorem

[![Blueprint](https://img.shields.io/badge/Blueprint-Live-blue)](https://e-vergo.github.io/General_Crystallographic_Restriction/blueprint/)

A formal verification in Lean 4 of the crystallographic restriction theorem, which characterizes exactly which rotation orders are achievable by integer matrices in arbitrary dimension. All proofs are complete with no `sorry` statements.

## Main Result

**Theorem (Crystallographic Restriction).** An N x N integer matrix can have finite order m if and only if psi(m) <= N.

```lean
theorem crystallographic_restriction (N m : ℕ) (hm : 0 < m) (hNm : m = 1 ∨ 0 < N) :
    m ∈ integerMatrixOrders N ↔ psi m ≤ N
```

## The Psi Function

The function `psi : ℕ → ℕ` determines the minimum dimension required to realize a given order:

- `psi(1) = 0`
- `psi(2) = 0`
- For m with prime factorization m = prod p_i^{k_i}:
  `psi(m) = sum phi(p_i^{k_i})`, excluding the term `phi(2)` when 2^1 exactly divides m

The special case for 2^1 reflects that -I has order 2 in any dimension >= 1.

| m      | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 12 |
|--------|---|---|---|---|---|---|---|---|---|----|----|
| psi(m) | 0 | 0 | 2 | 2 | 4 | 2 | 6 | 4 | 6 | 4  | 4  |

## Proof Strategy

The proof splits into two directions:

**Forward direction** (`m ∈ Ord_N => psi(m) <= N`): If an N x N integer matrix M has order m, then M^m = I, so its minimal polynomial divides X^m - 1. Since M has exact order m, the m-th cyclotomic polynomial divides the minimal polynomial. The degree constraint forces psi(m) <= N.

**Backward direction** (`psi(m) <= N => m ∈ Ord_N`): We construct integer matrices achieving each order using companion matrices of cyclotomic polynomials. For a prime power p^k, the companion matrix of the p^k-th cyclotomic polynomial has size phi(p^k) and order p^k. For composite m, block diagonal combinations achieve order m in dimension psi(m).

## Project Structure

```
Crystallographic/
├── Main/
│   ├── MainTheorem.lean       -- Main theorem statement and proof
│   └── Lemmas.lean            -- Supporting lemmas
├── Psi/
│   ├── Basic.lean             -- Definition of the psi function
│   └── Bounds.lean            -- Bounds on psi values
├── FiniteOrder/
│   ├── Basic.lean             -- Integer matrix orders definition
│   └── Order.lean             -- Order properties
├── Companion/
│   ├── Basic.lean             -- Companion matrix infrastructure
│   └── Cyclotomic.lean        -- Companion matrices of cyclotomic polynomials
└── CrystallographicRestriction/
    ├── Forward.lean           -- Forward direction proof
    └── Backward.lean          -- Backward direction proof
```

## Blueprint

**[View the live blueprint](https://e-vergo.github.io/General_Crystallographic_Restriction/blueprint/)** — an interactive proof document with side-by-side LaTeX/Lean display, hover tooltips, and dependency graphs.

The blueprint is generated using experimental tooling:
- [Dress](https://github.com/e-vergo/Dress) — Artifact generator with syntax highlighting
- [LeanArchitect](https://github.com/e-vergo/LeanArchitect) — `@[blueprint]` attribute for marking declarations
- [leanblueprint](https://github.com/e-vergo/leanblueprint) — Interactive web/PDF generation

## Building

```bash
lake build
```

## Dependencies

- Lean 4 (toolchain specified in `lean-toolchain`)
- Mathlib v4.26.0
- LeanArchitect v4.26.0

## Author

Eric Vergo

## License

Apache 2.0 — see [LICENSE](LICENSE) for details.

## References

- Bamberg, J., Cairns, G., and Kilminster, D. (2003). "The crystallographic restriction, permutations, and Goldbach's conjecture." *Amer. Math. Monthly*, 110(3):202-209.
