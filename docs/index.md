---
layout: default
---

# Crystallographic Restriction Theorem

A complete formal verification of the **Crystallographic Restriction Theorem** in Lean 4, establishing which finite orders are achievable by integer matrices.

## Main Result

An $N \times N$ integer matrix can have finite order $m$ if and only if $\psi(m) \leq N$, where:

$$\psi(m) = \sum_{\substack{p^k \| m \\ (p,k) \neq (2,1)}} \varphi(p^k)$$

All proofs are complete with no `sorry` statements.

## Resources

<div class="resources">

| Resource | Description |
|----------|-------------|
| [API Documentation](docs/) | Complete Lean 4 API docs (doc-gen4) |
| [Blueprint](blueprint/) | Mathematical blueprint with proof outlines |
| [Dependency Graph](blueprint/dep_graph_document.html) | Visual proof dependency graph |
| [GitHub Repository](https://github.com/e-vergo/General_Crystallographic_Restriction) | Source code |

</div>

## Proof Strategy

The proof proceeds in two directions:

**Forward direction:** If an integer matrix has order $m$, its minimal polynomial divides $X^m - 1$ and must include cyclotomic factors whose degrees sum to at least $\psi(m)$.

**Backward direction:** Companion matrices of cyclotomic polynomials $\Phi_{p^k}$ achieve prime power orders in dimension $\varphi(p^k)$. Block diagonal combinations yield any order $m$ in dimension exactly $\psi(m)$.

## References

- J. Bamberg, G. Cairns, and D. Kilminster. "The crystallographic restriction, permutations, and Goldbach's conjecture." *Amer. Math. Monthly*, 110(3):202–209, 2003.
