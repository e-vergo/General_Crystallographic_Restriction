/-
Copyright (c) 2026 Eric Vergo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo
-/
import Dress
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.LinearAlgebra.Matrix.Charpoly.Minpoly
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Crystallographic.FiniteOrder.Order
import Crystallographic.Psi.Basic
import Crystallographic.Psi.Bounds

/-!
# The Crystallographic Restriction Theorem - Forward Direction

This file proves the forward direction of the crystallographic restriction theorem:
if an N x N integer matrix has finite order m, then psi(m) <= N.

## Main results

* `psi_le_of_mem_integerMatrixOrders` - Forward direction: order m implies psi(m) <= N.

## Proof Strategy

1. Take A with orderOf A = m
2. The minimal polynomial of A divides X^m - 1
3. The primitive m-th roots of unity must appear as eigenvalues (otherwise order < m)
4. The Q-dimension required to contain all primitive m-th roots is >= phi(m)
5. Sum over prime power factors gives psi(m) <= N

## References

* Sasse, R. (2020). "Crystallographic Groups"

## Tags

crystallographic restriction, forward direction, minimal polynomial, eigenvalue, cyclotomic
-/

namespace Matrix

open Polynomial

/-- If the minimal polynomial of an integer matrix A divides X^k - 1, then A^k = 1.
This transfers the polynomial identity back to the matrix via the ring homomorphism. -/
@[blueprint "lem:pow-eq-one-of-minpoly-dvd"
  (displayName := "Power Equals One from Minpoly")
  (statement := /-- If $\mu_A \mid X^k - 1$, then $A^k = I$.
  \uses{def:minpoly} -/)
  (proof := /-- The polynomial $X^k - 1$ annihilates $A$ (since the minimal polynomial does),
  meaning $A^k - I = 0$. Transfer this identity from $\mathbb{Q}$ back to $\mathbb{Z}$ via
  the injectivity of $\mathbb{Z} \to \mathbb{Q}$. -/)]
lemma pow_eq_one_of_minpoly_dvd_X_pow_sub_one {N : ℕ} (A : Matrix (Fin N) (Fin N) ℤ) (k : ℕ)
    (hdvd : minpoly ℚ (A.map (algebraMap ℤ ℚ)) ∣ X ^ k - 1) : A ^ k = 1 := by
  let A_Q := A.map (algebraMap ℤ ℚ)
  -- If minpoly | X^k - 1, then aeval A_Q (X^k - 1) = 0
  have haeval : aeval A_Q (X ^ k - 1 : ℚ[X]) = 0 := by
    obtain ⟨q, hq⟩ := hdvd
    rw [hq, map_mul, minpoly.aeval, zero_mul]
  -- This means A_Q^k = 1
  simp only [map_sub, map_pow, aeval_X, map_one, sub_eq_zero] at haeval
  -- Transfer back to A via injectivity
  have hinj := Crystallographic.Matrix.map_algebraMap_int_injective N
  apply hinj
  change (A ^ k).map (algebraMap ℤ ℚ) =
    (1 : Matrix (Fin N) (Fin N) ℤ).map (algebraMap ℤ ℚ)
  rw [Matrix.map_pow, Matrix.map_one (algebraMap ℤ ℚ) (map_zero _) (map_one _)]
  exact haeval

/-- If A^m = 1, then the minimal polynomial of A divides X^m - 1.
This is because X^m - 1 annihilates A, and the minimal polynomial divides any annihilating polynomial. -/
@[blueprint "lem:minpoly-dvd-X-pow-sub-one"
  (displayName := "Minpoly Divides X^n - 1")
  (statement := /-- If $A^m = I$, then $\mu_A \mid X^m - 1$.
  \uses{def:minpoly} -/)
  (proof := /-- The polynomial $X^m - 1$ annihilates $A$ since $(A_{\mathbb{Q}})^m - I = 0$.
  The minimal polynomial divides any annihilating polynomial by definition. -/)]
lemma minpoly_dvd_X_pow_sub_one_of_pow_eq_one {N : ℕ} (A : Matrix (Fin N) (Fin N) ℤ) (m : ℕ)
    (hpow : A ^ m = 1) : minpoly ℚ (A.map (algebraMap ℤ ℚ)) ∣ X ^ m - 1 := by
  apply minpoly.dvd
  simp only [map_sub, map_pow, aeval_X, map_one]
  rw [← Matrix.map_pow, hpow,
    Matrix.map_one (algebraMap ℤ ℚ) (map_zero _) (map_one _), sub_self]

end Matrix

namespace Crystallographic

open Matrix Polynomial

/-- If each cyclotomic polynomial in a finset divides a target polynomial,
then their product also divides the target. -/
@[blueprint "lem:cyclotomic-finset-product-dvd"
  (displayName := "Cyclotomic Product Divisibility")
  (statement := /-- If $\Phi_d \mid f$ for all $d \in S$, then $\prod_{d \in S} \Phi_d \mid f$. -/)
  (proof := /-- By induction on $S$. The empty product divides everything. For the insert case,
  use that cyclotomic polynomials with distinct indices are coprime over $\mathbb{Q}$, so
  $\Phi_d$ is coprime to $\prod_{x \in s} \Phi_x$ when $d \notin s$. Then apply coprime
  divisibility: if $a, b$ are coprime and both divide $f$, then $ab \mid f$. -/)]
lemma cyclotomic_finset_product_dvd {target : ℚ[X]} (S : Finset ℕ)
    (hdvd_each : ∀ d ∈ S, cyclotomic d ℚ ∣ target) :
    (∏ d ∈ S, cyclotomic d ℚ) ∣ target := by
  induction S using Finset.induction with
  | empty => simp only [Finset.prod_empty, one_dvd]
  | @insert d s hd_notin IH =>
    rw [Finset.prod_insert hd_notin]
    have hdvd_d : cyclotomic d ℚ ∣ target := hdvd_each d (Finset.mem_insert_self d s)
    have hdvd_prod : (∏ x ∈ s, cyclotomic x ℚ) ∣ target :=
        IH (fun x hx => hdvd_each x (Finset.mem_insert_of_mem hx))
    have hcop : IsCoprime (cyclotomic d ℚ) (∏ x ∈ s, cyclotomic x ℚ) := by
      apply IsCoprime.prod_right
      intro x hx
      exact cyclotomic.isCoprime_rat (fun heq => hd_notin (heq ▸ hx))
    exact hcop.mul_dvd hdvd_d hdvd_prod

/-- For a divisor d not in the cyclotomic divisor set S of the minimal polynomial,
the cyclotomic polynomial Φ_d is coprime to the minimal polynomial. -/
lemma cyclotomic_coprime_minpoly_of_not_mem {N : ℕ} [NeZero N]
    (A : Matrix (Fin N) (Fin N) ℤ) (d : ℕ) (hd_pos : 0 < d)
    (hndvd : ¬cyclotomic d ℚ ∣ minpoly ℚ (A.map (algebraMap ℤ ℚ))) :
    IsCoprime (cyclotomic d ℚ) (minpoly ℚ (A.map (algebraMap ℤ ℚ))) :=
  (cyclotomic.irreducible_rat hd_pos).coprime_iff_not_dvd.mpr hndvd

/-- If the minimal polynomial divides X^m - 1, then it divides the product of cyclotomic
polynomials for divisors d where Φ_d divides the minimal polynomial.

The proof uses coprimality: minpoly is coprime to Φ_d when Φ_d does not divide it
(since Φ_d is irreducible), hence minpoly is coprime to the product of such Φ_d.
Since X^m - 1 = (∏_{d∈S} Φ_d) * (∏_{d∉S} Φ_d) and minpoly divides the LHS while
being coprime to the second factor, it must divide the first factor. -/
@[blueprint "lem:minpoly-dvd-prod-cyclotomic"
  (displayName := "Minpoly Divides Cyclotomic Product")
  (statement := /-- If $\mu_A \mid X^m - 1$ and $S = \{d \mid m : \Phi_d \mid \mu_A\}$,
  then $\mu_A \mid \prod_{d \in S} \Phi_d$.
  \uses{def:minpoly, lem:cyclotomic-finset-product-dvd} -/)
  (proof := /-- Split $X^m - 1 = (\prod_{d \in S} \Phi_d) \cdot (\prod_{d \notin S} \Phi_d)$.
  Since $\Phi_d$ is irreducible and does not divide $\mu_A$ for $d \notin S$, we have
  $\gcd(\mu_A, \Phi_d) = 1$. Thus $\mu_A$ is coprime to $\prod_{d \notin S} \Phi_d$.
  Since $\mu_A \mid X^m - 1$, it must divide $\prod_{d \in S} \Phi_d$. -/)]
lemma minpoly_dvd_prod_cyclotomic_of_dvd_X_pow_sub_one {N : ℕ} [NeZero N]
    (A : Matrix (Fin N) (Fin N) ℤ) (m : ℕ) (hm : 0 < m) (S : Finset ℕ) (hS_sub : S ⊆ m.divisors)
    (hS_def : ∀ d ∈ m.divisors, d ∈ S ↔ cyclotomic d ℚ ∣ minpoly ℚ (A.map (algebraMap ℤ ℚ)))
    (hminpoly_dvd : minpoly ℚ (A.map (algebraMap ℤ ℚ)) ∣ X ^ m - 1) :
    minpoly ℚ (A.map (algebraMap ℤ ℚ)) ∣ ∏ d ∈ S, cyclotomic d ℚ := by
  let A_Q := A.map (algebraMap ℤ ℚ)
  -- Key: {x ∈ m.divisors | x ∈ S} = S since S ⊆ m.divisors
  have hS_eq : m.divisors.filter (· ∈ S) = S := by
    ext d
    simp only [Finset.mem_filter]
    exact ⟨fun ⟨_, hd⟩ => hd, fun hd => ⟨hS_sub hd, hd⟩⟩
  -- minpoly is coprime to the product of cyclotomics NOT in S
  have hcoprime_with_complement : IsCoprime (minpoly ℚ A_Q)
      (∏ d ∈ m.divisors.filter (· ∉ S), cyclotomic d ℚ) :=
    IsCoprime.prod_right fun d hd => by
      have hd_div := (Finset.mem_filter.mp hd).1
      have hd_not_in_S := (Finset.mem_filter.mp hd).2
      have hndvd : ¬cyclotomic d ℚ ∣ minpoly ℚ A_Q := fun hdvd =>
        hd_not_in_S ((hS_def d hd_div).mpr hdvd)
      exact (cyclotomic_coprime_minpoly_of_not_mem A d (Nat.pos_of_mem_divisors hd_div) hndvd).symm
  -- Split X^m - 1 = (∏_{d∈S} Φ_d) * (∏_{d∉S} Φ_d)
  have hprod_split : ∏ d ∈ m.divisors, cyclotomic d ℚ =
      (∏ d ∈ S, cyclotomic d ℚ) * (∏ d ∈ m.divisors.filter (· ∉ S), cyclotomic d ℚ) := by
    rw [← Finset.prod_filter_mul_prod_filter_not m.divisors (· ∈ S), hS_eq]
  rw [← prod_cyclotomic_eq_X_pow_sub_one hm, hprod_split] at hminpoly_dvd
  exact hcoprime_with_complement.dvd_of_dvd_mul_right hminpoly_dvd

/-- For a polynomial that divides X^m - 1, we can characterize it as a product of cyclotomic
polynomials. Specifically, S = {d ∈ divisors(m) | Φ_d ∣ p} gives minpoly = ∏_{d∈S} Φ_d
when p is monic and irreducible factors are coprime. -/
@[blueprint "lem:minpoly-eq-prod-cyclotomic"
  (displayName := "Minpoly Cyclotomic Factorization")
  (statement := /-- If $\mu_A \mid X^m - 1$, then there exists $S \subseteq \mathrm{divisors}(m)$
  such that $\mu_A = \prod_{d \in S} \Phi_d$.
  \uses{def:minpoly, lem:minpoly-dvd-prod-cyclotomic, lem:cyclotomic-finset-product-dvd} -/)
  (proof := /-- Let $S = \{d \mid m : \Phi_d \mid \mu_A\}$. By the previous lemma,
  $\mu_A \mid \prod_{d \in S} \Phi_d$. Conversely, by definition of $S$, each $\Phi_d$ for
  $d \in S$ divides $\mu_A$, so their coprime product divides $\mu_A$. Mutual divisibility
  of monic polynomials implies equality. -/)]
lemma minpoly_eq_prod_cyclotomic_of_dvd_X_pow_sub_one {N : ℕ} [NeZero N]
    (A : Matrix (Fin N) (Fin N) ℤ) (m : ℕ) (hm : 0 < m)
    (hminpoly_dvd : minpoly ℚ (A.map (algebraMap ℤ ℚ)) ∣ X ^ m - 1) :
    ∃ S : Finset ℕ, (∀ d ∈ S, d ∣ m) ∧
      minpoly ℚ (A.map (algebraMap ℤ ℚ)) = ∏ d ∈ S, cyclotomic d ℚ := by
  classical
  let A_Q := A.map (algebraMap ℤ ℚ)
  let S := m.divisors.filter (fun d => cyclotomic d ℚ ∣ minpoly ℚ A_Q)
  have hS_sub : S ⊆ m.divisors := Finset.filter_subset _ _
  have hS_dvd : ∀ d ∈ S, d ∣ m := fun d hd =>
    (Nat.mem_divisors.mp (Finset.mem_filter.mp hd).1).1
  have hS_def : ∀ d ∈ m.divisors, d ∈ S ↔ cyclotomic d ℚ ∣ minpoly ℚ A_Q := fun d hd =>
    ⟨fun hS => (Finset.mem_filter.mp hS).2, fun hdvd => Finset.mem_filter.mpr ⟨hd, hdvd⟩⟩
  -- minpoly ∣ ∏_{d∈S} Φ_d (by coprimality argument)
  have hminpoly_dvd_prod : minpoly ℚ A_Q ∣ ∏ d ∈ S, cyclotomic d ℚ :=
    minpoly_dvd_prod_cyclotomic_of_dvd_X_pow_sub_one A m hm S hS_sub hS_def hminpoly_dvd
  -- ∏_{d∈S} Φ_d ∣ minpoly (by definition of S)
  have hprod_dvd_minpoly : (∏ d ∈ S, cyclotomic d ℚ) ∣ minpoly ℚ A_Q :=
    cyclotomic_finset_product_dvd S (fun d hd => (Finset.mem_filter.mp hd).2)
  -- Equality by mutual divisibility of monic polynomials
  exact ⟨S, hS_dvd, Polynomial.eq_of_monic_of_associated
    (minpoly.monic (Matrix.isIntegral A_Q))
    (Polynomial.monic_prod_of_monic _ _ (fun d _ => cyclotomic.monic d ℚ))
    (associated_of_dvd_dvd hminpoly_dvd_prod hprod_dvd_minpoly)⟩

/-- If A has order m and minpoly = ∏_{d∈S} Φ_d where S ⊆ divisors(m),
then S.lcm id = m. This is the key lemma: if lcm(S) < m, then A^{lcm(S)} = 1,
contradicting that A has exact order m. -/
@[blueprint "lem:cyclotomic-divisors-lcm-eq"
  (displayName := "Cyclotomic Divisors LCM")
  (statement := /-- If $\mathrm{ord}(A) = m$ and $\mu_A = \prod_{d \in S} \Phi_d$ with
  $S \subseteq \mathrm{divisors}(m)$, then $\mathrm{lcm}(S) = m$.
  \uses{lem:minpoly-eq-prod-cyclotomic, lem:pow-eq-one-of-minpoly-dvd} -/)
  (proof := /-- Suppose $\ell = \mathrm{lcm}(S) < m$. Then $\mu_A = \prod_{d \in S} \Phi_d$
  divides $\prod_{d \mid \ell} \Phi_d = X^\ell - 1$, since each $d \in S$ divides $\ell$.
  By the transfer lemma, $A^\ell = I$. But this contradicts $\mathrm{ord}(A) = m > \ell$. -/)]
lemma cyclotomic_divisors_lcm_eq_of_orderOf {N : ℕ} [NeZero N]
    (A : Matrix (Fin N) (Fin N) ℤ) (m : ℕ) (hm : 0 < m) (hA_ord : orderOf A = m)
    (S : Finset ℕ) (hS_sub : ∀ d ∈ S, d ∣ m)
    (hminpoly_eq_prod : minpoly ℚ (A.map (algebraMap ℤ ℚ)) = ∏ d ∈ S, cyclotomic d ℚ) :
    S.lcm id = m := by
  let A_Q := A.map (algebraMap ℤ ℚ)
  -- If lcm(S) < m, then minpoly | X^{lcm(S)} - 1, so A^{lcm(S)} = 1
  -- This contradicts orderOf A = m
  by_contra hne
  have hlcm_dvd_m : S.lcm id ∣ m := Finset.lcm_dvd (fun d hd => hS_sub d hd)
  have hlcm_le : S.lcm id ≤ m := Nat.le_of_dvd hm hlcm_dvd_m
  have hlcm_lt : S.lcm id < m := Nat.lt_of_le_of_ne hlcm_le hne
  -- minpoly | ∏_{d|lcm(S)} Φ_d = X^{lcm(S)} - 1
  have hlcm_pos : 0 < S.lcm id := by
    by_cases hS_empty : S = ∅
    · -- If S = ∅, then minpoly = 1 (empty product), contradiction since
      -- minpoly has positive degree
      simp only [hS_empty, Finset.prod_empty] at hminpoly_eq_prod
      have hdeg := minpoly.natDegree_pos (Matrix.isIntegral A_Q)
      rw [hminpoly_eq_prod, natDegree_one] at hdeg
      omega
    · have hne_zero : S.lcm id ≠ 0 := Finset.lcm_ne_zero_iff.mpr fun d hd =>
        (Nat.pos_of_mem_divisors (Nat.mem_divisors.mpr ⟨hS_sub d hd, hm.ne'⟩)).ne'
      exact Nat.pos_of_ne_zero hne_zero
  -- Helper: X^d - 1 | X^n - 1 when d | n
  have X_pow_sub_one_dvd : ∀ (d n : ℕ), d ∣ n → (X ^ d - 1 : ℚ[X]) ∣ X ^ n - 1 := by
    intro d n hdvd
    obtain ⟨k, hk⟩ := hdvd
    rw [hk]
    exact pow_one_sub_dvd_pow_mul_sub_one X d k
  have hminpoly_dvd_lcm : minpoly ℚ A_Q ∣ X ^ (S.lcm id) - 1 := by
    rw [hminpoly_eq_prod]
    apply cyclotomic_finset_product_dvd
    intro d hd
    have hd_dvd_lcm : d ∣ S.lcm id := Finset.dvd_lcm hd
    calc cyclotomic d ℚ ∣ X ^ d - 1 := cyclotomic.dvd_X_pow_sub_one d ℚ
      _ ∣ X ^ (S.lcm id) - 1 := X_pow_sub_one_dvd d (S.lcm id) hd_dvd_lcm
  -- Therefore A^{lcm(S)} = 1
  have hpow_lcm : A ^ (S.lcm id) = 1 :=
    Matrix.pow_eq_one_of_minpoly_dvd_X_pow_sub_one A (S.lcm id) hminpoly_dvd_lcm
  -- But orderOf A = m > lcm(S), so orderOf A | lcm(S) is false
  have hord_dvd := orderOf_dvd_of_pow_eq_one hpow_lcm
  rw [hA_ord] at hord_dvd
  have := Nat.le_of_dvd hlcm_pos hord_dvd
  omega

/-- If an N x N integer matrix has finite order m, then psi(m) <= N.

This is the forward direction of the crystallographic restriction theorem.
The proof uses eigenvalue theory: primitive m-th roots of unity must appear
as eigenvalues, and their algebraic degree constrains the matrix dimension.

**Proof outline:**
1. An integer matrix A with A^m = 1 has minimal polynomial dividing X^m - 1
2. If orderOf A = m, then the minimal polynomial is lcm of cyclotomic polynomials
   Φ_d for some divisors d of m with lcm(d) = m
3. The primitive m-th roots have minimal polynomial Phi_m (the cyclotomic polynomial)
4. These eigenvalues require dimension >= phi(d) for each d in the set
5. By sum_totient_ge_psi_of_lcm_eq, the sum of φ(d) >= psi(m)
6. Therefore psi(m) <= deg(minpoly) <= deg(charpoly) = N
-/
@[blueprint "thm:forward-direction"
  (displayName := "Forward Direction")
  (keyDeclaration := true)
  (message := "Shows psi(m) <= N is necessary")
  (statement := /-- \textbf{Forward Direction:} If $m \in \mathrm{Ord}_N$, then $\psi(m) \leq N$.

  \textbf{Mathematical context:}
  The key insight is that integer matrices with finite order have constrained eigenvalues:
  if $A^m = I$, all eigenvalues are $m$-th roots of unity. The minimal polynomial over $\mathbb{Q}$
  factors into cyclotomic polynomials $\Phi_d$ for various divisors $d$ of $m$. The requirement
  that $\mathrm{ord}(A) = m$ (not some proper divisor) forces the set of cyclotomic factors to
  have $\mathrm{lcm} = m$, which constrains the total degree.

  \textbf{Proof outline:}
  \begin{enumerate}
  \item Let $A$ be an $N \times N$ integer matrix with $\mathrm{ord}(A) = m$.
  \item The minimal polynomial of $A$ over $\mathbb{Q}$ divides $X^m - 1 = \prod_{d \mid m} \Phi_d$.
  \item Since $\Phi_d$ are irreducible and pairwise coprime over $\mathbb{Q}$, the minimal
        polynomial
        equals $\prod_{d \in S} \Phi_d$ for some $S \subseteq \mathrm{divisors}(m)$.
  \item The condition $\mathrm{ord}(A) = m$ forces $\mathrm{lcm}(S) = m$: if $\mathrm{lcm}(S) < m$,
        then $A^{\mathrm{lcm}(S)} = I$, contradicting $\mathrm{ord}(A) = m$.
  \item The degree of the minimal polynomial is $\sum_{d \in S} \varphi(d)$.
  \item By the sum-totient lemma (applied to any $S$ with $\mathrm{lcm}(S) = m$),
        $\psi(m) \leq \sum_{d \in S} \varphi(d) = \deg(\mathrm{minpoly})
        \leq \deg(\mathrm{charpoly}) = N$.
  \end{enumerate}
  \uses{integerMatrixOrders-def, psi-def, lem:sum-totient-ge-psi} -/)
  (proof := /-- Let $A$ be an $N \times N$ integer matrix with $A^m = I$. The minimal polynomial
  $\mu_A$
  over $\mathbb{Q}$ divides $X^m - 1$ and factors into cyclotomic polynomials $\Phi_d$ for
  various $d \mid m$. Each factor contributes $\varphi(d)$ to $\deg(\mu_A) \leq N$.
  Since distinct $\Phi_d$ are coprime and their lcm must be $m$, summing the totients
  of appearing divisors gives $\psi(m) \leq N$. --/)]
theorem psi_le_of_mem_integerMatrixOrders (N m : ℕ) (hm : 0 < m)
    (hord : m ∈ integerMatrixOrders N) : Crystallographic.psi m ≤ N := by
  -- Extract the matrix A with orderOf A = m
  obtain ⟨A, hA_ord, _⟩ := hord
  -- Handle the case N = 0 separately
  rcases Nat.eq_zero_or_pos N with rfl | hN_pos
  · -- N = 0: The only 0×0 matrix is empty, with order 1
    haveI : IsEmpty (Fin 0) := Fin.isEmpty
    have hA_eq_1 : A = 1 := Matrix.ext fun i => Fin.elim0 i
    rw [hA_eq_1, orderOf_one] at hA_ord
    subst hA_ord
    simp [Crystallographic.psi_one]
  · -- N > 0: Use psi ≤ deg(minpoly) ≤ deg(charpoly) = N
    haveI : NeZero N := ⟨Nat.pos_iff_ne_zero.mp hN_pos⟩
    let A_Q := A.map (algebraMap ℤ ℚ)
    -- The minimal polynomial degree is at most N
    have hminpoly_deg_le : (minpoly ℚ A_Q).natDegree ≤ N := by
      have hdvd := Matrix.minpoly_dvd_charpoly A_Q
      have hne : A_Q.charpoly ≠ 0 := (Matrix.charpoly_monic A_Q).ne_zero
      calc (minpoly ℚ A_Q).natDegree ≤ A_Q.charpoly.natDegree :=
          Polynomial.natDegree_le_of_dvd hdvd hne
        _ = Fintype.card (Fin N) := Matrix.charpoly_natDegree_eq_dim A_Q
        _ = N := Fintype.card_fin N
    -- minpoly | X^m - 1 since A^m = 1
    have hpow : A ^ m = 1 := by rw [← hA_ord]; exact pow_orderOf_eq_one A
    have hminpoly_dvd : minpoly ℚ A_Q ∣ X ^ m - 1 :=
      Matrix.minpoly_dvd_X_pow_sub_one_of_pow_eq_one A m hpow
    -- Get S and the product decomposition from helper lemma
    obtain ⟨S, hS_sub, hminpoly_eq_prod⟩ :=
      minpoly_eq_prod_cyclotomic_of_dvd_X_pow_sub_one A m hm hminpoly_dvd
    -- The lcm of S equals m (otherwise order would be smaller)
    have hS_lcm : S.lcm id = m :=
      cyclotomic_divisors_lcm_eq_of_orderOf A m hm hA_ord S hS_sub hminpoly_eq_prod
    -- Compute the degree as sum of totients
    have hdeg_eq : (minpoly ℚ A_Q).natDegree = ∑ d ∈ S, Nat.totient d := by
      rw [hminpoly_eq_prod, Polynomial.natDegree_prod _ _ (fun d _ => cyclotomic_ne_zero d ℚ)]
      exact Finset.sum_congr rfl (fun d _ => natDegree_cyclotomic d ℚ)
    -- Apply sum_totient_ge_psi_of_lcm_eq
    calc Crystallographic.psi m ≤ ∑ d ∈ S, Nat.totient d :=
        sum_totient_ge_psi_of_lcm_eq m hm S hS_sub hS_lcm
      _ = (minpoly ℚ A_Q).natDegree := hdeg_eq.symm
      _ ≤ N := hminpoly_deg_le

end Crystallographic

