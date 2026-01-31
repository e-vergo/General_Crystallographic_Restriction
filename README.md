# General Crystallographic Restriction

A formalization in Lean 4 of the crystallographic restriction theorem, which characterizes exactly which finite orders are achievable by integer matrices in any dimension.

**Live Blueprint:** [e-vergo.github.io/General_Crystallographic_Restriction](https://e-vergo.github.io/General_Crystallographic_Restriction/)

## The Theorem

An N x N integer matrix can have finite order m if and only if psi(m) <= N.

```lean
theorem crystallographic_restriction (N m : Nat) (hm : 0 < m) (hNm : m = 1 \/ 0 < N) :
    m \in integerMatrixOrders N <-> psi m <= N
```

This theorem explains why crystals in three-dimensional space can only exhibit 2-, 3-, 4-, or 6-fold rotational symmetry: these correspond to the finite orders achievable by 3x3 integer matrices.

### The Psi Function

The function `psi : Nat -> Nat` determines the minimum dimension required to realize a given order:

- `psi(1) = psi(2) = 0`
- For m with prime factorization m = prod p_i^{k_i}: `psi(m) = sum phi(p_i^{k_i})`, excluding `phi(2)` when exactly 2^1 divides m

The special treatment of 2^1 reflects that -I achieves order 2 in any dimension >= 1.

| m      | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 |
|--------|---|---|---|---|---|---|---|---|---|----|----|-----|
| psi(m) | 0 | 0 | 2 | 2 | 4 | 2 | 6 | 4 | 6 | 4  | 10 | 4  |

### Proof Strategy

**Forward direction:** If an N x N integer matrix A has order m, its minimal polynomial over Q divides X^m - 1 and factors as a product of distinct cyclotomic polynomials Phi_d for various divisors d of m. The constraint that ord(A) = m forces the lcm of these divisors to equal m. The sum of phi(d) over these divisors is at least psi(m), bounded by deg(minpoly) <= deg(charpoly) = N.

**Backward direction:** Companion matrices of cyclotomic polynomials Phi_{p^k} have size phi(p^k) and order exactly p^k. Block diagonal combinations of these matrices achieve order m = prod p_i^{k_i} in dimension psi(m). The construction handles the special case of 2^1 by using matrix negation: if A has odd order k, then -A has order 2k without increasing dimension.

## Live Documentation

| Output | URL |
|--------|-----|
| Dashboard | [e-vergo.github.io/General_Crystallographic_Restriction/](https://e-vergo.github.io/General_Crystallographic_Restriction/) |
| Dependency Graph | [dep_graph.html](https://e-vergo.github.io/General_Crystallographic_Restriction/dep_graph.html) |
| Paper (HTML) | [paper_tex.html](https://e-vergo.github.io/General_Crystallographic_Restriction/paper_tex.html) |
| Paper (PDF) | [paper.pdf](https://e-vergo.github.io/General_Crystallographic_Restriction/paper.pdf) |
| API Documentation | [docs/](https://e-vergo.github.io/General_Crystallographic_Restriction/docs/) |

## Project Structure

```
General_Crystallographic_Restriction/
├── Crystallographic.lean              # Library root
├── Crystallographic/
│   ├── Main/
│   │   ├── MainTheorem.lean           # Main theorem statement and proof
│   │   └── Lemmas.lean                # Supporting technical lemmas
│   ├── Psi/
│   │   ├── Basic.lean                 # Definition of psi, additivity on coprime factors
│   │   └── Bounds.lean                # Bounds relating psi to totient function
│   ├── FiniteOrder/
│   │   ├── Basic.lean                 # Definition of integerMatrixOrders, block diagonal
│   │   └── Order.lean                 # Order properties, lcm of block diagonal orders
│   ├── Companion/
│   │   ├── Basic.lean                 # Companion matrix definition and charpoly theorem
│   │   └── Cyclotomic.lean            # Companion matrices of cyclotomic polynomials
│   ├── CrystallographicRestriction/
│   │   ├── Forward.lean               # Forward direction via minimal polynomial theory
│   │   └── Backward.lean              # Backward direction via explicit construction
│   └── Paper.lean                     # Verso document for paper generation
├── blueprint/src/
│   ├── blueprint.tex                  # LaTeX blueprint document
│   └── paper.tex                      # Academic paper
├── runway.json                        # Site configuration
├── lakefile.toml                      # Lake build configuration
└── lean-toolchain                     # Lean version (v4.27.0)
```

### Module Dependencies

```
Psi.Basic --> Psi.Bounds
    |
    v
 FiniteOrder.Basic --> FiniteOrder.Order
    |                      |
    v                      v
Companion.Basic --> Companion.Cyclotomic
    |                      |
    |                      v
    +---------> CrystallographicRestriction.Forward
                CrystallographicRestriction.Backward
                           |
                           v
                    Main.MainTheorem
```

## Key Lemmas

| Label | Description |
|-------|-------------|
| `psi-def` | Definition of the psi function via prime factorization |
| `lem:psi-coprime-add` | psi(mn) = psi(m) + psi(n) for coprime m, n |
| `thm:companion-charpoly` | Companion matrix has prescribed characteristic polynomial |
| `thm:companion-cycl-order` | Companion of Phi_m has order exactly m |
| `thm:forward-direction` | m in Ord_N implies psi(m) <= N |
| `thm:backward-direction` | psi(m) <= N implies m in Ord_N |

## Building

### Prerequisites

- Lean 4.27.0 (specified in `lean-toolchain`)
- Mathlib v4.27.0

### Build Lean Project

```bash
lake build
```

### Generate Blueprint Site

The blueprint site is built via GitHub Actions using [dress-blueprint-action](https://github.com/e-vergo/dress-blueprint-action). Navigate to the Actions tab on GitHub, select "Full Blueprint Build and Deploy", and click "Run workflow".

The workflow builds the Lean project with artifact generation, generates the dependency graph (57 nodes), produces the interactive blueprint site and academic paper (HTML + PDF), downloads pre-generated DocGen4 documentation from the `docs-static` branch, and deploys to GitHub Pages.

### Local Development

```bash
./scripts/build_blueprint.sh
```

This script builds the complete toolchain, fetches mathlib cache, generates artifacts, runs the `:blueprint` Lake facet, generates the dependency graph, produces the HTML site and paper, and starts a local server at http://localhost:8000.

## Side-by-Side Blueprint Toolchain

This project uses the [Side-by-Side Blueprint](https://github.com/e-vergo/Side-By-Side-Blueprint) toolchain for interactive documentation.

### Toolchain Components

| Component | Purpose |
|-----------|---------|
| [SubVerso](https://github.com/e-vergo/subverso) | Syntax highlighting extraction |
| [LeanArchitect](https://github.com/e-vergo/LeanArchitect) | `@[blueprint]` attribute |
| [Dress](https://github.com/e-vergo/Dress) | Artifact generation, graph layout |
| [Verso](https://github.com/e-vergo/verso) | Document framework |
| [Runway](https://github.com/e-vergo/Runway) | Static site generator |
| [dress-blueprint-action](https://github.com/e-vergo/dress-blueprint-action) | GitHub Action for CI/CD |

### Blueprint Annotation Example

```lean
@[blueprint "thm:main-theorem"
  (title := "Crystallographic Restriction Theorem")
  (keyDeclaration := true)
  (message := "Central result of the formalization")
  (statement := /-- LaTeX statement... -/)
  (proof := /-- Proof outline... -/)]
theorem crystallographic_restriction ...
```

### Status Model

| Status | Color | Meaning |
|--------|-------|---------|
| notReady | Sandy Brown | Not ready to formalize |
| ready | Light Sea Green | Ready to be proven |
| sorry | Dark Red | Contains sorry |
| proven | Light Green | Complete proof |
| fullyProven | Forest Green | Proven with all dependencies proven |
| mathlibReady | Light Blue | Ready for mathlib contribution |

## References

- Kuzmanovich, J. and Pavlichenkov, A. (2002). "Finite groups of matrices whose entries are integers." *American Mathematical Monthly*, 109(2):173-186.

- Bamberg, J., Cairns, G., and Kilminster, D. (2003). "The crystallographic restriction, permutations, and Goldbach's conjecture." *American Mathematical Monthly*, 110(3):202-209.

- Newman, M. (1972). *Integral Matrices*. Academic Press.

## Authors

- Eric Vergo
- Claude (Anthropic)

## License

Apache 2.0
