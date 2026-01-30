# Crystallographic Restriction Theorem

![Lean](https://img.shields.io/badge/Lean-v4.27.0-blue)
![Mathlib](https://img.shields.io/badge/Mathlib-v4.27.0-blue)
![License](https://img.shields.io/badge/License-Apache%202.0-green)

[![Blueprint](https://img.shields.io/badge/Blueprint-Live-blue)](https://e-vergo.github.io/General_Crystallographic_Restriction/)
[![Paper](https://img.shields.io/badge/Paper-PDF-green)](https://e-vergo.github.io/General_Crystallographic_Restriction/paper.pdf)
[![Docs](https://img.shields.io/badge/Docs-API-orange)](https://e-vergo.github.io/General_Crystallographic_Restriction/docs/)

A complete formalization in Lean 4 of the crystallographic restriction theorem, characterizing exactly which rotation orders are achievable by integer matrices in arbitrary dimension.

## Main Result

**Theorem (Crystallographic Restriction).** An N x N integer matrix can have finite order m if and only if psi(m) <= N.

```lean
theorem crystallographic_restriction (N m : ℕ) (hm : 0 < m) (hNm : m = 1 ∨ 0 < N) :
    m ∈ integerMatrixOrders N ↔ psi m ≤ N
```

### The Psi Function

The function `psi : ℕ → ℕ` determines the minimum dimension required to realize a given order:

- `psi(1) = psi(2) = 0`
- For m = prod p_i^{k_i}: `psi(m) = sum phi(p_i^{k_i})`, excluding `phi(2)` when 2^1 exactly divides m

The special case for 2^1 reflects that -I has order 2 in any dimension >= 1.

| m      | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 12 |
|--------|---|---|---|---|---|---|---|---|---|----|----|
| psi(m) | 0 | 0 | 2 | 2 | 4 | 2 | 6 | 4 | 6 | 4  | 4  |

## Proof Strategy

**Forward direction:** If an N x N integer matrix has order m, its minimal polynomial divides X^m - 1 and must include the m-th cyclotomic polynomial. The degree constraint forces psi(m) <= N.

**Backward direction:** Companion matrices of cyclotomic polynomials Phi_{p^k} have size phi(p^k) and order p^k. Block diagonal combinations achieve order m in dimension psi(m).

## Built with Side-by-Side Blueprint

This project uses the [Side-by-Side Blueprint](https://github.com/e-vergo/Dress) toolchain for interactive proof documentation. The toolchain provides:

- **Side-by-side display** of LaTeX statements alongside Lean code with syntax highlighting and hover information
- **Interactive dependency graph** with Sugiyama layout, pan/zoom, and clickable modals showing full declarations
- **PDF/Paper generation** with `\paperstatement{}` and `\paperfull{}` hooks that link exposition to formal proofs
- **Dashboard** with progress metrics, validation checks, and project notes
- **Real dependency inference** traced from Lean code (not manual `\uses{}` annotations)

All outputs are generated automatically from `@[blueprint]` annotations in the Lean source.

### Live Documentation

| Output | Link |
|--------|------|
| Dashboard | [e-vergo.github.io/General_Crystallographic_Restriction/](https://e-vergo.github.io/General_Crystallographic_Restriction/) |
| Blueprint | [companion-matrices.html](https://e-vergo.github.io/General_Crystallographic_Restriction/companion-matrices.html) |
| Paper PDF | [paper.pdf](https://e-vergo.github.io/General_Crystallographic_Restriction/paper.pdf) |
| API Docs | [docs/](https://e-vergo.github.io/General_Crystallographic_Restriction/docs/) |

## Project Structure

```
Crystallographic/
├── Main/
│   ├── MainTheorem.lean      -- Main theorem statement and proof
│   └── Lemmas.lean           -- Supporting lemmas
├── Psi/
│   ├── Basic.lean            -- Definition of the psi function
│   └── Bounds.lean           -- Bounds on psi values
├── FiniteOrder/
│   ├── Basic.lean            -- Integer matrix orders definition
│   └── Order.lean            -- Order properties
├── Companion/
│   ├── Basic.lean            -- Companion matrix infrastructure
│   └── Cyclotomic.lean       -- Companion matrices of cyclotomic polynomials
└── CrystallographicRestriction/
    ├── Forward.lean          -- Forward direction proof
    └── Backward.lean         -- Backward direction proof

blueprint/src/
├── blueprint.tex             -- LaTeX source with \inputleannode{} commands
└── paper.tex                 -- Paper source with \paperstatement{} commands
```

## Building

### Lean Project

```bash
lake build
```

### Blueprint Site

The blueprint site is built via GitHub Actions using [dress-blueprint-action](https://github.com/e-vergo/dress-blueprint-action). The live site is deployed automatically on push to main.

### Dependencies

- Lean 4.27.0 (see `lean-toolchain`)
- Mathlib v4.27.0
- [Dress](https://github.com/e-vergo/Dress) (for blueprint generation)

## Toolchain Components

| Component | Purpose |
|-----------|---------|
| [SubVerso](https://github.com/e-vergo/subverso) | Syntax highlighting extraction with hover data |
| [LeanArchitect](https://github.com/e-vergo/LeanArchitect) | `@[blueprint]` attribute with metadata and status flags |
| [Dress](https://github.com/e-vergo/Dress) | Artifact generation, graph construction, validation |
| [Runway](https://github.com/e-vergo/Runway) | Static site generator with dashboard and paper support |
| [dress-blueprint-action](https://github.com/e-vergo/dress-blueprint-action) | GitHub Action for CI/CD |

### Related Projects

- [SBS-Test](https://github.com/e-vergo/SBS-Test) -- Minimal test project demonstrating all features
- [PrimeNumberTheoremAnd](https://github.com/teorth/PrimeNumberTheoremAnd) -- Large-scale integration (530 annotations)

## References

- Kuzmanovich, J. and Pavlichenkov, A. (2002). "Finite groups of matrices whose entries are integers." *Amer. Math. Monthly*, 109(2):173-186.
- Bamberg, J., Cairns, G., and Kilminster, D. (2003). "The crystallographic restriction, permutations, and Goldbach's conjecture." *Amer. Math. Monthly*, 110(3):202-209.

## License

Apache 2.0
