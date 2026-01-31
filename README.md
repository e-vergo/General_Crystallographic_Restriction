# General Crystallographic Restriction

A complete formalization in Lean 4 of the crystallographic restriction theorem, which characterizes exactly which finite orders are achievable by integer matrices in any dimension.

## Main Result

**Theorem (Crystallographic Restriction).** An N x N integer matrix can have finite order m if and only if psi(m) <= N.

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

## Mathematical Content

### Proof Strategy

**Forward direction:** If an N x N integer matrix A has order m, its minimal polynomial over Q divides X^m - 1 and factors as a product of distinct cyclotomic polynomials Phi_d for various divisors d of m. The constraint that ord(A) = m (not some smaller divisor) forces the lcm of these divisors to equal m. The sum of phi(d) over these divisors is at least psi(m), bounded by deg(minpoly) <= deg(charpoly) = N.

**Backward direction:** Companion matrices of cyclotomic polynomials Phi_{p^k} have size phi(p^k) and order exactly p^k. Block diagonal combinations of these matrices achieve order m = prod p_i^{k_i} in dimension psi(m). The construction handles the special case of 2^1 by using matrix negation: if A has odd order k, then -A has order 2k without increasing dimension.

### Key Lemmas

| Label | Description |
|-------|-------------|
| `psi-def` | Definition of the psi function via prime factorization |
| `lem:psi-coprime-add` | psi(mn) = psi(m) + psi(n) for coprime m, n |
| `thm:companion-charpoly` | Companion matrix has prescribed characteristic polynomial |
| `thm:companion-cycl-order` | Companion of Phi_m has order exactly m |
| `thm:forward-direction` | m in Ord_N implies psi(m) <= N |
| `thm:backward-direction` | psi(m) <= N implies m in Ord_N |

## Project Structure

```
Crystallographic/
  Main/
    MainTheorem.lean    -- Main theorem statement and proof
    Lemmas.lean         -- Supporting technical lemmas
  Psi/
    Basic.lean          -- Definition of psi, additivity on coprime factors
    Bounds.lean         -- Bounds relating psi to totient function
  FiniteOrder/
    Basic.lean          -- Definition of integerMatrixOrders, block diagonal
    Order.lean          -- Order properties, lcm of block diagonal orders
  Companion/
    Basic.lean          -- Companion matrix definition and charpoly theorem
    Cyclotomic.lean     -- Companion matrices of cyclotomic polynomials
  CrystallographicRestriction/
    Forward.lean        -- Forward direction via minimal polynomial theory
    Backward.lean       -- Backward direction via explicit construction
  Paper.lean            -- Verso document for paper generation

blueprint/src/
  blueprint.tex         -- Blueprint document with \inputleannode{} commands
  paper.tex             -- Academic paper with \paperstatement{} commands
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

## Blueprint Integration

This project uses the [Side-by-Side Blueprint](https://github.com/e-vergo/Side-By-Side-Blueprint) toolchain for interactive documentation. The formalization contains 57 `@[blueprint]` annotations across 10 Lean files.

### Annotation Patterns

**Main theorem with full metadata:**
```lean
@[blueprint "thm:main-theorem"
  (title := "Crystallographic Restriction Theorem")
  (keyDeclaration := true)
  (message := "Central result of the formalization")
  (statement := /-- The theorem statement in LaTeX... -/)
  (proof := /-- Proof outline... -/)]
theorem crystallographic_restriction ...
```

**Key definition:**
```lean
@[blueprint "psi-def"
  (title := "Psi Function Definition")
  (keyDeclaration := true)
  (message := "The psi function characterizes achievable orders")
  (statement := /-- The psi function... \uses{psiPrimePow-def} -/)]
def psi (m : Nat) : Nat := ...
```

**Lemma with dependency tracking:**
```lean
@[blueprint "lem:psi-coprime-add"
  (title := "Psi Coprime Additivity")
  (statement := /-- psi(mn) = psi(m) + psi(n) for coprime m, n.
    \uses{psi-def, lem:factorization-disjoint} -/)
  (proof := /-- Coprime factorizations are disjoint... -/)]
theorem psi_coprime_add ...
```

### Attribute Options Used

| Option | Usage in Project |
|--------|------------------|
| `title` | Custom labels for graph nodes |
| `keyDeclaration` | Marks main theorem and psi definition |
| `message` | Progress notes on key results |
| `statement` | LaTeX theorem statements with `\uses{}` |
| `proof` | Proof outlines for documentation |
| `misc` | Additional notes on definitions |

## Building

### Prerequisites

- Lean 4.27.0 (see `lean-toolchain`)
- Mathlib v4.27.0
- [Dress](https://github.com/e-vergo/Dress) (for blueprint generation)

### Build Lean Project

```bash
lake build
```

### Generate Blueprint Site

The blueprint site is built via GitHub Actions using [dress-blueprint-action](https://github.com/e-vergo/dress-blueprint-action). To trigger a build:

1. Navigate to Actions tab on GitHub
2. Select "Full Blueprint Build and Deploy"
3. Click "Run workflow"

The workflow:
1. Builds the Lean project with artifact generation
2. Generates dependency graph and statistics
3. Generates the interactive blueprint site
4. Generates paper.html and paper.pdf
5. Downloads pre-generated DocGen4 documentation from `docs-static` branch
6. Deploys to GitHub Pages

### Local Development

For local blueprint generation, use the shared build script:

```bash
./scripts/build_blueprint.sh
```

This script:
- Builds the complete toolchain (SubVerso -> LeanArchitect -> Dress -> Runway)
- Fetches mathlib cache
- Generates artifacts with `BLUEPRINT_DRESS=1`
- Runs the `:blueprint` Lake facet
- Generates the dependency graph
- Produces the HTML site and paper
- Starts a local server at http://localhost:8000

## Output Artifacts

### Live Documentation

| Output | URL |
|--------|-----|
| Dashboard | [e-vergo.github.io/General_Crystallographic_Restriction/](https://e-vergo.github.io/General_Crystallographic_Restriction/) |
| Blueprint | [companion-matrices.html](https://e-vergo.github.io/General_Crystallographic_Restriction/companion-matrices.html) |
| Dependency Graph | [dep_graph.html](https://e-vergo.github.io/General_Crystallographic_Restriction/dep_graph.html) |
| Paper (HTML) | [paper.html](https://e-vergo.github.io/General_Crystallographic_Restriction/paper.html) |
| Paper (PDF) | [paper.pdf](https://e-vergo.github.io/General_Crystallographic_Restriction/paper.pdf) |
| API Documentation | [docs/](https://e-vergo.github.io/General_Crystallographic_Restriction/docs/) |

### Build Outputs

| Location | Content |
|----------|---------|
| `.lake/build/dressed/` | Per-declaration artifacts (decl.tex, decl.html, decl.json) |
| `.lake/build/runway/` | Generated HTML site |
| `.lake/build/runway/manifest.json` | Statistics, validation, project metadata |
| `.lake/build/runway/paper.pdf` | Compiled paper |

## Configuration

### runway.json

```json
{
  "title": "General Crystallographic Restriction Theorem",
  "projectName": "Crystallographic",
  "githubUrl": "https://github.com/e-vergo/General_Crystallographic_Restriction",
  "baseUrl": "/General_Crystallographic_Restriction/",
  "docgen4Url": "docs/",
  "blueprintTexPath": "blueprint/src/blueprint.tex",
  "assetsDir": "../dress-blueprint-action/assets",
  "paperTexPath": "blueprint/src/paper.tex"
}
```

### lakefile.toml

```toml
name = "Crystallographic"
defaultTargets = ["Crystallographic"]

[leanOptions]
pp.unicode.fun = true
autoImplicit = false
relaxedAutoImplicit = false

[[require]]
name = "mathlib"
git = "https://github.com/leanprover-community/mathlib4.git"
rev = "v4.27.0"

[[require]]
name = "Dress"
git = "https://github.com/e-vergo/Dress.git"
rev = "main"

[[require]]
name = "verso"
git = "https://github.com/e-vergo/verso.git"
rev = "main"

[[require]]
scope = "dev"
name = "doc-gen4"
git = "https://github.com/leanprover/doc-gen4.git"
rev = "01e1433"
```

## Toolchain

This project uses the Side-by-Side Blueprint toolchain:

| Component | Purpose |
|-----------|---------|
| [SubVerso](https://github.com/e-vergo/subverso) | Syntax highlighting extraction with O(1) indexed lookups |
| [LeanArchitect](https://github.com/e-vergo/LeanArchitect) | `@[blueprint]` attribute with 8 metadata + 3 status options |
| [Dress](https://github.com/e-vergo/Dress) | Artifact generation, graph layout, validation |
| [Verso](https://github.com/e-vergo/verso) | Document framework with blueprint genres |
| [Runway](https://github.com/e-vergo/Runway) | Static site generator with dashboard and paper support |
| [dress-blueprint-action](https://github.com/e-vergo/dress-blueprint-action) | GitHub Action for CI/CD + CSS/JS assets |

The dependency chain is: `SubVerso -> LeanArchitect -> Dress -> Runway`

## Status Model

The project uses a 6-status color model for tracking formalization progress:

| Status | Color | Meaning |
|--------|-------|---------|
| notReady | Sandy Brown | Not ready to formalize |
| ready | Light Sea Green | Ready to be proven |
| sorry | Dark Red | Contains sorry |
| proven | Light Green | Complete proof |
| fullyProven | Forest Green | Proven with all dependencies proven |
| mathlibReady | Light Blue | Ready for mathlib contribution |

Status is auto-detected from the Lean code (sorry detection, dependency analysis) with manual override options.

## References

- Kuzmanovich, J. and Pavlichenkov, A. (2002). "Finite groups of matrices whose entries are integers." *American Mathematical Monthly*, 109(2):173-186.

- Bamberg, J., Cairns, G., and Kilminster, D. (2003). "The crystallographic restriction, permutations, and Goldbach's conjecture." *American Mathematical Monthly*, 110(3):202-209.

- Newman, M. (1972). *Integral Matrices*. Academic Press.

## Related Projects

| Project | Description |
|---------|-------------|
| [SBS-Test](https://github.com/e-vergo/SBS-Test) | Minimal test project for the toolchain |
| [PrimeNumberTheoremAnd](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd) | Large-scale blueprint integration (530 annotations) |

## Authors

- Eric Vergo
- Claude (Anthropic)

## License

Apache 2.0
