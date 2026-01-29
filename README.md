# Crystallographic Restriction Theorem

[![Blueprint](https://img.shields.io/badge/Blueprint-Live-blue)](https://e-vergo.github.io/General_Crystallographic_Restriction/)
[![Paper](https://img.shields.io/badge/Paper-PDF-green)](https://e-vergo.github.io/General_Crystallographic_Restriction/paper.pdf)
[![Docs](https://img.shields.io/badge/Docs-API-orange)](https://e-vergo.github.io/General_Crystallographic_Restriction/docs/)

> **Side-by-Side Blueprint Example Project** -- This formalization demonstrates the [Side-by-Side Blueprint](https://github.com/e-vergo/Dress) toolchain for interactive proof documentation with coupled LaTeX/Lean display.

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

## Live Documentation

This project serves as a **production example for the Side-by-Side Blueprint toolchain**, demonstrating all major features:

| Output | Description |
|--------|-------------|
| [Dashboard](https://e-vergo.github.io/General_Crystallographic_Restriction/) | Dashboard with progress metrics, soundness checks, and project operational details|
| [Side-by-side blueprint](https://e-vergo.github.io/General_Crystallographic_Restriction/companion-matrices.html) | Blueprint with LaTeX and lean, with Verso support|
| [Paper](https://e-vergo.github.io/General_Crystallographic_Restriction/paper.pdf) | PDF with `\paperstatement{}` and `\paperfull{}` hooks linking formal proofs to exposition |

All outputs are generated automatically from `@[blueprint]` annotations in the Lean source code.

### Blueprint Features Demonstrated

- **Dashboard homepage** with stats, key theorems, user messages, and project notes
- **Side-by-side display** showing LaTeX statements alongside Lean code with syntax highlighting
- **Proof toggles** to expand/collapse formal proofs
- **Dependency graph** with Sugiyama layout, edge routing, pan/zoom, and clickable modals
- **Paper generation** with PDF output and ar5iv-style HTML
- **Real dependency inference** from Lean code (not manual `\uses{}` annotations)
- **Validation checks** for connectivity and cycles

## Proof Strategy

**Forward direction:** If an N x N integer matrix has order m, its minimal polynomial divides X^m - 1 and must include the m-th cyclotomic polynomial. The degree constraint forces psi(m) <= N.

**Backward direction:** Companion matrices of cyclotomic polynomials Phi_{p^k} have size phi(p^k) and order p^k. Block diagonal combinations achieve order m in dimension psi(m).

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

### Full Blueprint Build

```bash
./scripts/build_blueprint.sh
```

This runs the complete pipeline:
1. Builds the Lean project with `BLUEPRINT_DRESS=1`
2. Generates artifacts via the `:blueprint` Lake facet
3. Creates dependency graph and manifest
4. Generates the static site with Runway
5. Generates paper PDF (if configured)
6. Starts a local server at `localhost:8000`

### Lean Only

```bash
lake build
```

### Dependencies

- Lean 4 (see `lean-toolchain`)
- Mathlib (v4.27.0)
- Dress (for blueprint generation)

## Side-by-Side Blueprint Toolchain

This project demonstrates the Side-by-Side Blueprint toolchain -- a pure Lean 4 system for generating interactive documentation that couples formal proofs with mathematical exposition.

| Component | Purpose |
|-----------|---------|
| [Dress](https://github.com/e-vergo/Dress) | Artifact generation, graph construction, validation (connectivity, cycles), dependency inference |
| [LeanArchitect](https://github.com/e-vergo/LeanArchitect) | `@[blueprint]` attribute with metadata options (`title`, `keyDeclaration`, `message`, status flags) |
| [Runway](https://github.com/e-vergo/Runway) | Static site generator with dashboard, dependency graph, paper/PDF generation |
| [dress-blueprint-action](https://github.com/e-vergo/dress-blueprint-action) | GitHub Action for CI/CD with CSS/JS assets |

### Related Projects

- [SBS-Test](https://github.com/e-vergo/SBS-Test) -- Minimal test project (11 nodes, all features)
- [PrimeNumberTheoremAnd](https://github.com/e-vergo/PrimeNumberTheoremAnd) -- Large-scale integration (530 annotations, 33 files)

## References

- Kuzmanovich, J. and Pavlichenkov, A. (2002). "Finite groups of matrices whose entries are integers." *Amer. Math. Monthly*, 109(2):173-186.
- Bamberg, J., Cairns, G., and Kilminster, D. (2003). "The crystallographic restriction, permutations, and Goldbach's conjecture." *Amer. Math. Monthly*, 110(3):202-209.

## License

Apache 2.0
