/-
Copyright (c) 2026 Eric Vergo. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Eric Vergo
-/
import Architect
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
-/

namespace Crystallographic

open Matrix Polynomial

/-- If each cyclotomic polynomial in a finset divides a target polynomial,
then their product also divides the target. -/
@[blueprint "lem:cyclotomic-finset-product-dvd"
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
  \item Since $\Phi_d$ are irreducible and pairwise coprime over $\mathbb{Q}$, the minimal polynomial
        equals $\prod_{d \in S} \Phi_d$ for some $S \subseteq \mathrm{divisors}(m)$.
  \item The condition $\mathrm{ord}(A) = m$ forces $\mathrm{lcm}(S) = m$: if $\mathrm{lcm}(S) < m$,
        then $A^{\mathrm{lcm}(S)} = I$, contradicting $\mathrm{ord}(A) = m$.
  \item The degree of the minimal polynomial is $\sum_{d \in S} \varphi(d)$.
  \item By the sum-totient lemma (applied to any $S$ with $\mathrm{lcm}(S) = m$),
        $\psi(m) \leq \sum_{d \in S} \varphi(d) = \deg(\mathrm{minpoly}) \leq \deg(\mathrm{charpoly}) = N$.
  \end{enumerate}
  \uses{integerMatrixOrders-def, psi-def, lem:sum-totient-ge-psi} --/)
  (proof := /-- Let $A$ be an $N \times N$ integer matrix with $A^m = I$. The minimal polynomial $\mu_A$
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
    -- Any two 0×0 matrices are equal since there are no indices
    have hA_eq_1 : A = 1 := Matrix.ext fun i => Fin.elim0 i
    rw [hA_eq_1, orderOf_one] at hA_ord
    subst hA_ord
    simp [Crystallographic.psi_one]
  · -- N > 0: Use psi ≤ φ ≤ N via minimal polynomial degree bounds
    haveI : NeZero N := ⟨Nat.pos_iff_ne_zero.mp hN_pos⟩
    let A_Q := A.map (algebraMap ℤ ℚ)
    -- The minimal polynomial over ℚ is the key object
    -- Its degree satisfies: psi(m) ≤ deg(minpoly) ≤ deg(charpoly) = N
    have hminpoly_deg_le : (minpoly ℚ A_Q).natDegree ≤ N := by
      have hdvd := Matrix.minpoly_dvd_charpoly A_Q
      have hne : A_Q.charpoly ≠ 0 := (Matrix.charpoly_monic A_Q).ne_zero
      calc (minpoly ℚ A_Q).natDegree ≤ A_Q.charpoly.natDegree :=
          Polynomial.natDegree_le_of_dvd hdvd hne
        _ = Fintype.card (Fin N) := Matrix.charpoly_natDegree_eq_dim A_Q
        _ = N := Fintype.card_fin N
    -- minpoly | X^m - 1 since A^m = 1
    have hpow : A ^ m = 1 := by rw [← hA_ord]; exact pow_orderOf_eq_one A
    have pow_eq_one_of_minpoly_dvd : ∀ k : ℕ, minpoly ℚ A_Q ∣ X ^ k - 1 → A ^ k = 1 := by
      intro k hdvd
      -- If minpoly | X^k - 1, then aeval A_Q (X^k - 1) = 0
      have haeval : aeval A_Q (X ^ k - 1 : ℚ[X]) = 0 := by
        obtain ⟨q, hq⟩ := hdvd
        rw [hq, map_mul, minpoly.aeval, zero_mul]
      -- This means A_Q^k = 1
      simp only [map_sub, map_pow, aeval_X, map_one, sub_eq_zero] at haeval
      -- Transfer back to A via injectivity
      have hinj : Function.Injective
          (Matrix.map · (algebraMap ℤ ℚ) :
            Matrix (Fin N) (Fin N) ℤ → Matrix (Fin N) (Fin N) ℚ) := by
        intro M₁ M₂ heq
        ext i j
        have h := congrFun (congrFun heq i) j
        simp only [Matrix.map_apply] at h
        exact (algebraMap ℤ ℚ).injective_int h
      apply hinj
      change (A ^ k).map (algebraMap ℤ ℚ) =
        (1 : Matrix (Fin N) (Fin N) ℤ).map (algebraMap ℤ ℚ)
      rw [Matrix.map_pow, Matrix.map_one (algebraMap ℤ ℚ) (map_zero _) (map_one _)]
      exact haeval
    -- The minimal polynomial divides X^m - 1 = ∏_{d|m} Φ_d
    have hminpoly_dvd : minpoly ℚ A_Q ∣ X ^ m - 1 := by
      apply minpoly.dvd
      simp only [map_sub, map_pow, aeval_X, map_one]
      rw [← Matrix.map_pow, hpow,
        Matrix.map_one (algebraMap ℤ ℚ) (map_zero _) (map_one _), sub_self]
    -- The key algebraic fact: minpoly = ∏_{d∈S} Φ_d for some S ⊆ divisors(m),
    -- and lcm(S) = m.
    -- The degree equals ∑_{d∈S} φ(d) ≥ psi(m) by sum_totient_ge_psi_of_lcm_eq.
    --
    -- We prove this by showing that the set S of divisors d where Φ_d | minpoly has:
    -- 1. minpoly = ∏_{d∈S} Φ_d (since cyclotomics are irreducible and pairwise coprime)
    -- 2. lcm(S) = m (since otherwise orderOf A < m)
    --
    -- Define S = {d ∈ divisors(m) | Φ_d ∣ minpoly ℚ A_Q}
    classical
    let S : Finset ℕ := m.divisors.filter (fun d => cyclotomic d ℚ ∣ minpoly ℚ A_Q)
    -- Every element of S divides m
    have hS_sub : ∀ d ∈ S, d ∣ m := by
      intro d hd
      have hd' := Finset.mem_filter.mp hd
      exact Nat.mem_divisors.mp hd'.1 |>.1
    -- The minpoly is the product of Φ_d for d ∈ S (by unique factorization)
    -- First, show that minpoly ∣ ∏_{d∈S} Φ_d
    have hminpoly_dvd_prod : minpoly ℚ A_Q ∣ ∏ d ∈ S, cyclotomic d ℚ := by
      have hcoprime_outside : ∀ d ∈ m.divisors, d ∉ S →
          IsCoprime (cyclotomic d ℚ) (minpoly ℚ A_Q) := by
        intro d hd hd_not_in_S
        have hd_pos : 0 < d := Nat.pos_of_mem_divisors hd
        have hirr : Irreducible (cyclotomic d ℚ) := cyclotomic.irreducible_rat hd_pos
        have hndvd : ¬(cyclotomic d ℚ ∣ minpoly ℚ A_Q) := by
          intro hdvd
          apply hd_not_in_S
          exact Finset.mem_filter.mpr ⟨hd, hdvd⟩
        -- Since Φ_d is irreducible and doesn't divide minpoly, they're coprime
        exact (EuclideanDomain.dvd_or_coprime _ _ hirr).resolve_left hndvd
      -- minpoly | ∏_{d|m} Φ_d = ∏_{d∈S} Φ_d * ∏_{d∉S} Φ_d
      -- and minpoly is coprime with ∏_{d∉S} Φ_d (since coprime with each factor)
      -- so minpoly | ∏_{d∈S} Φ_d
      have hprod_split : ∏ d ∈ m.divisors, cyclotomic d ℚ =
          (∏ d ∈ S, cyclotomic d ℚ) *
          (∏ d ∈ m.divisors.filter (· ∉ S), cyclotomic d ℚ) := by
        rw [← Finset.prod_filter_mul_prod_filter_not m.divisors (· ∈ S)]
        -- Need to show {x ∈ m.divisors | x ∈ S} = S
        -- Since S = m.divisors.filter _, S ⊆ m.divisors, so this holds
        have hS_eq : m.divisors.filter (· ∈ S) = S := by
          ext d
          simp only [Finset.mem_filter]
          constructor
          · intro ⟨_, hd⟩; exact hd
          · intro hd; exact ⟨Finset.mem_filter.mp hd |>.1, hd⟩
        rw [hS_eq]
      have hcoprime_with_complement : IsCoprime (minpoly ℚ A_Q)
          (∏ d ∈ m.divisors.filter (· ∉ S), cyclotomic d ℚ) := by
        apply IsCoprime.prod_right
        intro d hd
        have hd_in_div : d ∈ m.divisors := Finset.mem_of_mem_filter d hd
        have hd_not_in_S : d ∉ S := (Finset.mem_filter.mp hd).2
        exact (hcoprime_outside d hd_in_div hd_not_in_S).symm
      rw [← prod_cyclotomic_eq_X_pow_sub_one hm, hprod_split] at hminpoly_dvd
      exact hcoprime_with_complement.dvd_of_dvd_mul_right hminpoly_dvd
    -- Conversely, ∏_{d∈S} Φ_d ∣ minpoly (by definition of S and coprimality)
    have hprod_dvd_minpoly : (∏ d ∈ S, cyclotomic d ℚ) ∣ minpoly ℚ A_Q :=
      cyclotomic_finset_product_dvd S (fun d hd => (Finset.mem_filter.mp hd).2)
    -- Therefore minpoly = ∏_{d∈S} Φ_d (up to units, but both are monic)
    have hminpoly_eq_prod : minpoly ℚ A_Q = ∏ d ∈ S, cyclotomic d ℚ := by
      apply Polynomial.eq_of_monic_of_associated
      · exact minpoly.monic (Matrix.isIntegral A_Q)
      · exact Polynomial.monic_prod_of_monic _ _ (fun d _ => cyclotomic.monic d ℚ)
      · exact associated_of_dvd_dvd hminpoly_dvd_prod hprod_dvd_minpoly
    -- Now show lcm(S) = m
    have hS_lcm : S.lcm id = m := by
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
      have hpow_lcm : A ^ (S.lcm id) = 1 := pow_eq_one_of_minpoly_dvd (S.lcm id) hminpoly_dvd_lcm
      -- But orderOf A = m > lcm(S), so orderOf A | lcm(S) is false
      have hord_dvd := orderOf_dvd_of_pow_eq_one hpow_lcm
      rw [hA_ord] at hord_dvd
      have := Nat.le_of_dvd hlcm_pos hord_dvd
      omega
    -- Now compute the degree
    have hdeg_eq : (minpoly ℚ A_Q).natDegree = ∑ d ∈ S, Nat.totient d := by
      rw [hminpoly_eq_prod, Polynomial.natDegree_prod _ _ (fun d hd => cyclotomic_ne_zero d ℚ)]
      apply Finset.sum_congr rfl
      intro d hd
      exact natDegree_cyclotomic d ℚ
    -- Apply sum_totient_ge_psi_of_lcm_eq
    calc Crystallographic.psi m ≤ ∑ d ∈ S, Nat.totient d :=
        sum_totient_ge_psi_of_lcm_eq m hm S hS_sub hS_lcm
      _ = (minpoly ℚ A_Q).natDegree := hdeg_eq.symm
      _ ≤ N := hminpoly_deg_le

end Crystallographic
