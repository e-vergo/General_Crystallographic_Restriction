# Code Quality Audit - Crystallographic Restriction

## Summary
- Total actionable findings: 18
- Files affected: 8

---

## File-by-File Plan

### 1. Psi/Basic.lean

#### 1.1 Extract `psi_odd_prime` helper
**Location**: Lines 124-176

**Current**:
```lean
theorem psi_three : psi 3 = 2 := by
  have h := psi_prime_pow 3 1 Nat.prime_three (by norm_num : 0 < 1)
  simp only [pow_one] at h
  rw [h]
  simp only [(by decide : (3 : ℕ) ≠ 2), false_and, ite_false]
  rw [Nat.totient_prime Nat.prime_three]

theorem psi_five : psi 5 = 4 := by
  have hp : Nat.Prime 5 := by decide
  have h := psi_prime_pow 5 1 hp (by norm_num : 0 < 1)
  simp only [pow_one] at h
  rw [h]
  simp only [(by decide : (5 : ℕ) ≠ 2), false_and, ite_false]
  rw [Nat.totient_prime hp]

theorem psi_seven : psi 7 = 6 := by
  have hp : Nat.Prime 7 := by decide
  have h := psi_prime_pow 7 1 hp (by norm_num : 0 < 1)
  simp only [pow_one] at h
  rw [h]
  simp only [(by decide : (7 : ℕ) ≠ 2), false_and, ite_false]
  rw [Nat.totient_prime hp]
```

**Proposed**:
```lean
/-- psi of an odd prime p equals p - 1 -/
theorem psi_odd_prime (p : ℕ) (hp : p.Prime) (hp_odd : p ≠ 2) : psi p = p - 1 := by
  have h := psi_prime_pow p 1 hp (by norm_num : 0 < 1)
  simp only [pow_one] at h
  rw [h, if_neg (by simp [hp_odd]), Nat.totient_prime hp]

theorem psi_three : psi 3 = 2 := psi_odd_prime 3 Nat.prime_three (by decide)
theorem psi_five : psi 5 = 4 := psi_odd_prime 5 (by decide) (by decide)
theorem psi_seven : psi 7 = 6 := psi_odd_prime 7 (by decide) (by decide)
```

#### 1.2 Extract `psi_two_pow` and `psi_odd_prime_pow` helpers
**Location**: Lines 132-176

**Current**:
```lean
theorem psi_four : psi 4 = 2 := by
  have h := psi_prime_pow 2 2 Nat.prime_two (by norm_num : 0 < 2)
  simp only [show (4 : ℕ) = 2 ^ 2 by norm_num] at h ⊢
  rw [h]
  simp only [(by decide : (2 : ℕ) ≠ 1), and_false, ite_false]
  rw [Nat.totient_prime_pow Nat.prime_two (by norm_num : 0 < 2)]
  norm_num

theorem psi_eight : psi 8 = 4 := by
  have h := psi_prime_pow 2 3 Nat.prime_two (by norm_num : 0 < 3)
  simp only [show (8 : ℕ) = 2 ^ 3 by norm_num] at h ⊢
  rw [h]
  simp only [(by decide : (3 : ℕ) ≠ 1), and_false, ite_false]
  rw [Nat.totient_prime_pow Nat.prime_two (by norm_num : 0 < 3)]
  norm_num

theorem psi_nine : psi 9 = 6 := by
  have h := psi_prime_pow 3 2 Nat.prime_three (by norm_num : 0 < 2)
  simp only [show (9 : ℕ) = 3 ^ 2 by norm_num] at h ⊢
  rw [h]
  simp only [(by decide : (3 : ℕ) ≠ 2), false_and, ite_false]
  rw [Nat.totient_prime_pow Nat.prime_three (by norm_num : 0 < 2)]
  norm_num
```

**Proposed**:
```lean
/-- psi of 2^k for k ≥ 2 equals φ(2^k) = 2^(k-1) -/
theorem psi_two_pow (k : ℕ) (hk : 2 ≤ k) : psi (2 ^ k) = 2 ^ (k - 1) := by
  have h := psi_prime_pow 2 k Nat.prime_two (by omega : 0 < k)
  rw [h, if_neg (by omega : ¬(2 = 2 ∧ k = 1))]
  rw [Nat.totient_prime_pow Nat.prime_two (by omega : 0 < k)]

/-- psi of p^k for odd prime p equals φ(p^k) -/
theorem psi_odd_prime_pow (p k : ℕ) (hp : p.Prime) (hp_odd : p ≠ 2) (hk : 0 < k) :
    psi (p ^ k) = p ^ (k - 1) * (p - 1) := by
  rw [psi_prime_pow p k hp hk, if_neg (by simp [hp_odd])]
  rw [Nat.totient_prime_pow hp hk]

theorem psi_four : psi 4 = 2 := by simpa using psi_two_pow 2 (by norm_num)
theorem psi_eight : psi 8 = 4 := by simpa using psi_two_pow 3 (by norm_num)
theorem psi_nine : psi 9 = 6 := by simpa using psi_odd_prime_pow 3 2 Nat.prime_three (by decide) (by norm_num)
```

#### 1.3 Extract `factorization_eq_zero_of_disjoint_support` helper
**Location**: Lines 204-229 (`psi_coprime_add`)

**Current**: Repeated pattern in two branches:
```lean
have : n.factorization p = 0 := by
  by_contra hne
  have hmem : p ∈ n.factorization.support := Finsupp.mem_support_iff.mpr hne
  exact Finset.disjoint_left.mp hdisj hp hmem
```

**Proposed**: Extract helper:
```lean
private lemma factorization_eq_zero_of_disjoint_support {m n p : ℕ}
    (hdisj : Disjoint m.factorization.support n.factorization.support)
    (hp : p ∈ m.factorization.support) : n.factorization p = 0 := by
  by_contra hne
  exact Finset.disjoint_left.mp hdisj hp (Finsupp.mem_support_iff.mpr hne)
```

#### 1.4 Convert `factorization_support_disjoint` to term mode
**Location**: Lines 183-186

**Current**:
```lean
lemma factorization_support_disjoint {m n : ℕ} (h : m.Coprime n) :
    Disjoint m.factorization.support n.factorization.support := by
  simp only [Nat.support_factorization]
  exact h.disjoint_primeFactors
```

**Proposed**:
```lean
lemma factorization_support_disjoint {m n : ℕ} (h : m.Coprime n) :
    Disjoint m.factorization.support n.factorization.support :=
  Nat.support_factorization m ▸ Nat.support_factorization n ▸ h.disjoint_primeFactors
```

---

### 2. Psi/Bounds.lean

#### 2.1 Consider inlining `nontrivialPrimes`
**Location**: Lines 296-297

**Current**:
```lean
private abbrev nontrivialPrimes (m : ℕ) : Finset ℕ :=
  m.factorization.support.filter (fun q => ¬(q = 2 ∧ m.factorization q = 1))
```

**Action**: Review the two call sites. If inlining improves clarity, remove the abbreviation and inline. If the abbreviation aids readability, keep it.

---

### 3. FiniteOrder/Basic.lean

#### 3.1 Add `Matrix.map_algebraMap_int_injective` lemma
**Location**: Add near other matrix lemmas

**Proposed** (new lemma):
```lean
lemma Matrix.map_algebraMap_int_injective (N : ℕ) :
    Function.Injective (Matrix.map · (algebraMap ℤ ℚ) :
      Matrix (Fin N) (Fin N) ℤ → Matrix (Fin N) (Fin N) ℚ) := by
  intro M₁ M₂ heq
  ext i j
  exact (algebraMap ℤ ℚ).injective_int (congrFun (congrFun heq i) j)
```

#### 3.2 Simplify `two_mem_integerMatrixOrders`
**Location**: Lines 73-77

**Current**:
```lean
lemma two_mem_integerMatrixOrders (N : ℕ) [NeZero N] : 2 ∈ integerMatrixOrders N := by
  use -1
  constructor
  · rw [orderOf_neg_one, ringChar_matrix_int, if_neg (by norm_num : (0 : ℕ) ≠ 2)]
  · norm_num
```

**Proposed**:
```lean
lemma two_mem_integerMatrixOrders (N : ℕ) [NeZero N] : 2 ∈ integerMatrixOrders N :=
  ⟨-1, by rw [orderOf_neg_one, ringChar_matrix_int]; simp, by norm_num⟩
```

#### 3.3 Make `embedMatrixSum_mul` simp explicit
**Location**: Lines 94-98

**Current**:
```lean
lemma embedMatrixSum_mul {M K : ℕ} {R : Type*} [Semiring R] (A B : Matrix (Fin M) (Fin M) R) :
    embedMatrixSum (K := K) (A * B) = embedMatrixSum A * embedMatrixSum B := by
  simp only [embedMatrixSum]
  rw [fromBlocks_multiply]
  simp
```

**Proposed**:
```lean
lemma embedMatrixSum_mul {M K : ℕ} {R : Type*} [Semiring R] (A B : Matrix (Fin M) (Fin M) R) :
    embedMatrixSum (K := K) (A * B) = embedMatrixSum A * embedMatrixSum B := by
  simp only [embedMatrixSum, fromBlocks_multiply, mul_zero, zero_mul, add_zero, zero_add, mul_one]
```

#### 3.4 Simplify `blockDiag2_mul`
**Location**: Lines 207-211

**Current**:
```lean
lemma blockDiag2_mul ... :
    blockDiag2 (A * A') (B * B') = blockDiag2 A B * blockDiag2 A' B' := by
  simp only [blockDiag2, Matrix.fromBlocks_multiply]
  congr 1 <;> simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]
```

**Proposed**:
```lean
lemma blockDiag2_mul ... :
    blockDiag2 (A * A') (B * B') = blockDiag2 A B * blockDiag2 A' B' := by
  simp only [blockDiag2, fromBlocks_multiply, mul_zero, zero_mul, add_zero, zero_add]
```

---

### 4. Companion/Basic.lean

#### 4.1 Simplify `CompanionMinor00IndexConds` structure
**Location**: Lines 338-391

**Current**: 12-field structure used only once for bundling index conditions.

**Action**: Review whether inlining conditions directly in `companion_charmatrix_minor00_apply` with `have` statements would be clearer. The structure adds ~60 lines for a single use.

#### 4.2 Simplify `companion_charpoly_of_natDegree_one`
**Location**: Lines 119-155

**Action**: Run `simp?` to find minimal simp lemma set. Replace verbose individual steps with combined simp.

---

### 5. Companion/Cyclotomic.lean

#### 5.1 Check if `Nat.not_dvd_of_pos_of_lt` exists in Mathlib
**Location**: Lines 83-86

**Current**:
```lean
lemma Nat.not_dvd_of_pos_of_lt {m k : ℕ} (hk_pos : 0 < k) (hk_lt : k < m) : ¬m ∣ k := by
  intro hdvd
  exact Nat.not_lt.mpr (Nat.le_of_dvd hk_pos hdvd) hk_lt
```

**Action**: Search Mathlib for `Nat.not_dvd_of_lt` or similar. If exists, replace. If not, keep (potential upstream candidate).

#### 5.2 Remove redundant inline comments
**Location**: Lines 89-130 (`dvd_of_cyclotomic_dvd_X_pow_sub_one`)

**Action**: Remove comments that duplicate the docstring, e.g., `-- cyclotomic m Q is irreducible over Q` before `have hirr : Irreducible (cyclotomic m ℚ)`.

---

### 6. CrystallographicRestriction/Forward.lean

#### 6.1 Use extracted `Matrix.map_algebraMap_int_injective`
**Location**: Lines 66-78

**Current**:
```lean
have hinj : Function.Injective
    (Matrix.map · (algebraMap ℤ ℚ) :
      Matrix (Fin N) (Fin N) ℤ → Matrix (Fin N) (Fin N) ℚ) := by
  intro M₁ M₂ heq
  ext i j
  have h := congrFun (congrFun heq i) j
  simp only [Matrix.map_apply] at h
  exact (algebraMap ℤ ℚ).injective_int h
```

**Proposed** (after adding lemma to FiniteOrder/Basic.lean):
```lean
have hinj := Matrix.map_algebraMap_int_injective N
```

---

### 7. CrystallographicRestriction/Backward.lean

#### 7.1 Delete trivial wrappers
**Location**: Lines 189-198

**Current**:
```lean
lemma order_one_achievable (N : ℕ) : 1 ∈ integerMatrixOrders N :=
  one_mem_integerMatrixOrders N

lemma order_two_achievable (N : ℕ) [NeZero N] : 2 ∈ integerMatrixOrders N :=
  two_mem_integerMatrixOrders N
```

**Action**: Delete these lemmas. Update call sites to use `one_mem_integerMatrixOrders` and `two_mem_integerMatrixOrders` directly. If blueprint annotations are needed, add them to the original lemmas in FiniteOrder/Basic.lean instead.

#### 7.2 Unify `mem_integerMatrixOrders_small` cases
**Location**: Lines 361-372

**Current**:
```lean
private lemma mem_integerMatrixOrders_small (m N : ℕ) (hm : m ∈ ({3, 4, 6} : Finset ℕ))
    (hpsi : psi m ≤ N) : m ∈ integerMatrixOrders N := by
  fin_cases hm
  · have hN2 : 2 ≤ N := by simp only [psi_three] at hpsi; omega
    exact integerMatrixOrders_mono hN2 (mem_integerMatrixOrders_totient 3 (by omega))
  · have hN2 : 2 ≤ N := by simp only [psi_four] at hpsi; omega
    exact integerMatrixOrders_mono hN2 (mem_integerMatrixOrders_totient 4 (by omega))
  · have hN2 : 2 ≤ N := by simp only [psi_six] at hpsi; omega
    exact integerMatrixOrders_mono hN2 (mem_integerMatrixOrders_totient 6 (by omega))
```

**Proposed**:
```lean
private lemma mem_integerMatrixOrders_small (m N : ℕ) (hm : m ∈ ({3, 4, 6} : Finset ℕ))
    (hpsi : psi m ≤ N) : m ∈ integerMatrixOrders N := by
  have hm_ge2 : 2 ≤ m := by fin_cases hm <;> omega
  have hpsi_eq_2 : psi m = 2 := by fin_cases hm <;> simp [psi_three, psi_four, psi_six]
  have hN2 : 2 ≤ N := by omega
  exact integerMatrixOrders_mono hN2 (mem_integerMatrixOrders_totient m hm_ge2)
```

#### 7.3 Add section comment for private helpers
**Location**: Lines 222-292

**Action**: Add a section comment grouping `odd_ne_two_ge_three_of_coprime_two`, `mem_integerMatrixOrders_psi_2_times_odd`, and related private lemmas.

#### 7.4 Track permutation matrix lemmas for Mathlib
**Location**: Lines 56-171

**Lemmas**: `permMatrix_one`, `permMatrix_mul`, `permMatrix_pow`, `permMatrix_eq_one_iff`, `orderOf_permMatrix`

**Action**: These are general-purpose and should be upstreamed to `Mathlib.LinearAlgebra.Matrix.Permutation`. Add TODO comment or track in separate issue.

---

### 8. Main/Lemmas.lean

#### 8.1 Use anonymous `have` in `two_le_totient_of_two_lt`
**Location**: Lines 162-165

**Current**:
```lean
theorem two_le_totient_of_two_lt (n : ℕ) (hn : 2 < n) : 2 ≤ Nat.totient n := by
  have hpos := Nat.totient_pos.mpr (by omega : 0 < n)
  have hne_one := Nat.totient_eq_one_iff.not.mpr (by omega : ¬(n = 1 ∨ n = 2))
  omega
```

**Proposed**:
```lean
theorem two_le_totient_of_two_lt (n : ℕ) (hn : 2 < n) : 2 ≤ Nat.totient n := by
  have := Nat.totient_pos.mpr (by omega : 0 < n)
  have := Nat.totient_eq_one_iff.not.mpr (by omega : ¬(n = 1 ∨ n = 2))
  omega
```

---

## Cross-File Tasks

### Import Optimization
After all changes, run import analysis to identify unused imports across all files.

### Mathlib Upstream Candidates
Track these for potential contribution:
- Permutation matrix lemmas (Backward.lean)
- `Nat.not_dvd_of_pos_of_lt` (Companion/Cyclotomic.lean)
- `Matrix.map_algebraMap_int_injective` (FiniteOrder/Basic.lean)

---

## Execution Order

1. **FiniteOrder/Basic.lean** - Add `Matrix.map_algebraMap_int_injective` first (dependency for Forward.lean)
2. **Psi/Basic.lean** - Extract helper lemmas
3. **Psi/Bounds.lean** - Review `nontrivialPrimes`
4. **FiniteOrder/Basic.lean** - Remaining simplifications
5. **Companion/Basic.lean** - Structure simplification
6. **Companion/Cyclotomic.lean** - Mathlib check and comment cleanup
7. **CrystallographicRestriction/Forward.lean** - Use extracted lemma
8. **CrystallographicRestriction/Backward.lean** - Delete wrappers, unify cases
9. **Main/Lemmas.lean** - Minor cleanup
10. **All files** - Import optimization

---

## Verification

After each file:
- Run `lake build`
- Check diagnostics with `lean_diagnostic_messages`

After all changes:
- Full build verification
- Spot-check renamed/moved lemmas are found correctly
