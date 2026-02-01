# The Crystallographic Restriction Theorem

![Lean](https://img.shields.io/badge/Lean-v4.27.0-blue)
![Mathlib](https://img.shields.io/badge/Mathlib-v4.27.0-purple)
![Nodes](https://img.shields.io/badge/Blueprint-57%20nodes-green)
![License](https://img.shields.io/badge/License-Apache%202.0-orange)

A complete formalization in Lean 4 of the crystallographic restriction theorem, which characterizes exactly which finite orders are achievable by integer matrices in any dimension.

**Live Demo:** [e-vergo.github.io/General_Crystallographic_Restriction](https://e-vergo.github.io/General_Crystallographic_Restriction/)

This is a full production example of the [Side-by-Side Blueprint](https://github.com/e-vergo/Side-By-Side-Blueprint) toolchain, demonstrating all features including side-by-side displays, dependency graphs, and academic paper generation.

**What to explore:**
- **Blueprint**: Complete side-by-side documentation with theorem statements and formal proofs
- **Dependency Graph**: 57-node visualization showing how lemmas and theorems build toward the main result
- **Paper (HTML and PDF)**: Standalone academic publication with links to formal proofs
- **Dashboard**: Progress overview with key theorems and formalization status

## The Mathematics

### The Problem

Which finite orders can an integer matrix have? This question has a complete answer, and that answer explains a physical phenomenon: why crystals in three-dimensional space can only exhibit 2-, 3-, 4-, or 6-fold rotational symmetry.

### Main Result

**Theorem (Crystallographic Restriction).** An N x N integer matrix can have finite order m if and only if psi(m) <= N.

```lean
theorem crystallographic_restriction (N m : Nat) (hm : 0 < m) (hNm : m = 1 \/ 0 < N) :
    m \in integerMatrixOrders N <-> psi m <= N
```

### The Psi Function

The key is the function psi : Nat -> Nat, which determines the minimum dimension required to realize a given order:

- psi(1) = psi(2) = 0
- For m with prime factorization m = prod p_i^{k_i}, we have psi(m) = sum phi(p_i^{k_i}), excluding phi(2) when exactly 2^1 divides m

| m      | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 |
|--------|---|---|---|---|---|---|---|---|---|----|----|-----|
| psi(m) | 0 | 0 | 2 | 2 | 4 | 2 | 6 | 4 | 6 | 4  | 10 | 4  |

The special case psi(2) = 0 reflects that -I (negative identity) achieves order 2 in any dimension >= 1, so order 2 is "free."

### Physical Interpretation

In crystallography, the symmetry group of a crystal lattice consists of isometries preserving the lattice. The rotational part of such an isometry is represented by an integer matrix. The crystallographic restriction explains why pentagons don't tile the plane and why quasicrystals with 5-fold symmetry were so surprising when discovered.

### Proof Strategy

**Forward direction:** If an N x N integer matrix A has order m, its minimal polynomial over Q divides X^m - 1 and factors as a product of distinct cyclotomic polynomials Phi_d for various divisors d of m. The constraint that ord(A) = m forces the lcm of these divisors to equal m. The sum of phi(d) over these divisors is at least psi(m), bounded by deg(minpoly) <= deg(charpoly) = N.

**Backward direction:** Companion matrices of cyclotomic polynomials Phi_{p^k} have size phi(p^k) and order exactly p^k. Block diagonal combinations of these matrices achieve order m = prod p_i^{k_i} in dimension psi(m). The construction handles the special case of 2^1 by using matrix negation: if A has odd order k, then -A has order 2k without increasing dimension.

## Live Documentation

| Page | Description |
|------|-------------|
| [Dashboard](https://e-vergo.github.io/General_Crystallographic_Restriction/) | Project overview with progress stats and key theorems |
| [Blueprint](https://e-vergo.github.io/General_Crystallographic_Restriction/chapter-1.html) | Side-by-side LaTeX and Lean with proof toggles |
| [Dependency Graph](https://e-vergo.github.io/General_Crystallographic_Restriction/dep_graph.html) | Interactive 57-node visualization with pan/zoom |
| [Paper (HTML)](https://e-vergo.github.io/General_Crystallographic_Restriction/paper_tex.html) | Academic paper with links to Lean proofs |
| [Paper (PDF)](https://e-vergo.github.io/General_Crystallographic_Restriction/paper.pdf) | Printable PDF version |
| [API Docs](https://e-vergo.github.io/General_Crystallographic_Restriction/docs/) | DocGen4 API documentation |

## Project Structure

```
General_Crystallographic_Restriction/
├── Crystallographic.lean              # Library root (imports all modules)
├── Crystallographic/
│   ├── Psi/
│   │   ├── Basic.lean                 # psi definition, values, coprime additivity
│   │   └── Bounds.lean                # Bounds relating psi to totient function
│   ├── FiniteOrder/
│   │   ├── Basic.lean                 # integerMatrixOrders definition, block diagonal
│   │   └── Order.lean                 # Order properties, lcm of block diagonal orders
│   ├── Companion/
│   │   ├── Basic.lean                 # Companion matrix definition, charpoly theorem
│   │   └── Cyclotomic.lean            # Companion matrices of cyclotomic polynomials
│   ├── CrystallographicRestriction/
│   │   ├── Forward.lean               # Forward direction via minimal polynomial theory
│   │   └── Backward.lean              # Backward direction via explicit construction
│   └── Main/
│       ├── MainTheorem.lean           # Main theorem statement and proof
│       └── Lemmas.lean                # Supporting technical lemmas
├── blueprint/src/
│   ├── blueprint.tex                  # LaTeX blueprint document
│   └── paper.tex                      # Academic paper source
├── runway.json                        # Site configuration
├── lakefile.toml                      # Lake build configuration
└── lean-toolchain                     # Lean version (v4.27.0)
```

### Module Dependency Structure

```
          Psi.Basic
             |
             v
       Psi.Bounds     FiniteOrder.Basic
             |               |
             v               v
       Companion.Basic  FiniteOrder.Order
             |               |
             v               v
       Companion.Cyclotomic  |
             |               |
             +-------+-------+
                     |
                     v
        CrystallographicRestriction.Forward
        CrystallographicRestriction.Backward
                     |
                     v
              Main.MainTheorem
```

## Key Formalizations

| Label | Lean Name | Description |
|-------|-----------|-------------|
| `psi-def` | `Crystallographic.psi` | The psi function via prime factorization |
| `lem:psi-coprime-add` | `psi_coprime_add` | psi(mn) = psi(m) + psi(n) for coprime m, n |
| `lem:psi-prime-pow` | `psi_prime_pow` | psi(p^k) = phi(p^k) for most prime powers |
| `thm:companion-charpoly` | `charpoly_companion_eq` | Companion matrix has prescribed charpoly |
| `thm:companion-cycl-order` | `orderOf_companion_cyclotomic` | Companion of Phi_m has order exactly m |
| `thm:forward-direction` | `psi_le_of_mem_integerMatrixOrders` | m in Ord_N implies psi(m) <= N |
| `thm:backward-direction` | `mem_integerMatrixOrders_of_psi_le` | psi(m) <= N implies m in Ord_N |
| `thm:main-theorem` | `crystallographic_restriction` | The complete iff statement |

## Building

### Prerequisites

- Lean 4.27.0 (specified in `lean-toolchain`)
- Mathlib v4.27.0

### One-Click Build (Recommended)

From the monorepo root:

```bash
./dev/build-gcr.sh
```

This executes a single command that:
1. Validates project configuration
2. Syncs all repos to GitHub
3. Builds the toolchain in dependency order
4. Fetches mathlib cache
5. Compiles the Lean project with blueprint artifact generation
6. Generates the dependency graph and site
7. Generates the academic paper (PDF and HTML)
8. Captures screenshots for compliance validation
9. Starts a local server at http://localhost:8000

The site is generated at `.lake/build/runway/` with interactive pages, assets, and manifest files.

### Manual Build

For finer control, you can build components individually:

```bash
# Fetch mathlib cache
lake exe cache get

# Build the Lean project with blueprint artifacts
lake build

# Generate dependency graph and manifest
lake exe Dress extract_blueprint graph

# Generate the site
lake exe Runway build runway.json
```

### CI/CD

The live documentation is built via GitHub Actions using [dress-blueprint-action](https://github.com/e-vergo/dress-blueprint-action). Navigate to Actions > "Full Blueprint Build and Deploy" > Run workflow to rebuild.

## Documentation Toolchain

This project uses the **[Side-by-Side Blueprint](https://github.com/e-vergo/Side-By-Side-Blueprint)** toolchain, a pure Lean implementation consisting of:

**Core Components:**
- **Dress**: Captures blueprint artifacts during elaboration (syntax highlighting, code blocks, metadata)
- **Runway**: Generates the interactive website, dashboard, and paper
- **LeanArchitect**: Provides the `@[blueprint]` attribute for tagging theorems and lemmas
- **SubVerso**: O(1) indexed syntax highlighting with semantic information
- **Verso**: Document framework supporting side-by-side displays with rainbow brackets

**Feature Set:**
- **Side-by-side display**: LaTeX theorem statements alongside syntax-highlighted Lean code
- **Interactive dependency graph**: Sugiyama hierarchical layout with pan/zoom, modals, and connectivity validation
- **6-status tracking**: notReady, ready, sorry, proven, fullyProven, mathlibReady
- **Paper generation**: Academic ar5iv-style paper with verification badges and links to proofs
- **Automatic dependency inference**: Traces actual Lean code dependencies (no manual `\uses{}`)
- **Rainbow brackets**: Depth-colored bracket matching for nested expressions
- **Validation checks**: Connectivity and cycle detection to catch missing dependencies (inspired by the Tao incident)

The toolchain runs entirely during build time and requires only Lean - no additional runtime dependencies.

## References

The formalization is based on classical results about integer matrices and cyclotomic polynomials:

- Kuzmanovich, J. and Pavlichenkov, A. (2002). "Finite groups of matrices whose entries are integers." *American Mathematical Monthly*, 109(2):173-186.

- Bamberg, J., Cairns, G., and Kilminster, D. (2003). "The crystallographic restriction, permutations, and Goldbach's conjecture." *American Mathematical Monthly*, 110(3):202-209.

- Newman, M. (1972). *Integral Matrices*. Academic Press.

- Sasse, R. (2020). "Crystallographic Groups" - Primary reference for the proof structure.

## Attribution

- **Side-by-Side Blueprint**: Documentation toolchain by [e-vergo](https://github.com/e-vergo/Side-By-Side-Blueprint)
- **leanblueprint**: Original Python implementation by [Patrick Massot](https://github.com/PatrickMassot/leanblueprint)
- **LeanArchitect**: Based on [hanwenzhu/LeanArchitect](https://github.com/hanwenzhu/LeanArchitect)

## Author

Eric Vergo

## License

Apache 2.0
