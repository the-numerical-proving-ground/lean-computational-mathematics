import ComputationalMathematics.Source.CertifiedTridiagonalEigenpairs.Scaling
import ComputationalMathematics.Source.CertifiedTridiagonalEigenpairs.BidiagonalMassShift

/-!
# Exact binary scaling of a stored bidiagonal matrix

The two packed bands use the same magnitude scan as a symmetric tridiagonal
matrix with those bands. Only the physical orientation of the adjacent band
differs. The scale and the scaled bands are represented by input-precision words.
-/

namespace NumStability.CertifiedTridiagonalEigenpairs

open FloatingPointFormat.UnboundedBinary

variable {p n : ℕ} {hp : 2 ≤ p}

private def upperStoredBidiagonalWord
    (a : Fin (n + 1) → Word p hp) (b : Fin n → Word p hp) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) (Word p hp) :=
  fun i j =>
    if i = j then a i
    else if h : i.val + 1 = j.val then b ⟨i.val, by omega⟩
    else .zero

/-- Expand the packed bands if an individual physical entry is needed. -/
def storedBidiagonalWord (upper : Bool)
    (a : Fin (n + 1) → Word p hp) (b : Fin n → Word p hp) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) (Word p hp) :=
  if upper then upperStoredBidiagonalWord a b else Matrix.transpose (upperStoredBidiagonalWord a b)

/-- The real denotation of the stored bidiagonal input. -/
noncomputable def storedBidiagonal (upper : Bool)
    (a : Fin (n + 1) → Word p hp) (b : Fin n → Word p hp) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  fun i j => (storedBidiagonalWord upper a b i j).value

theorem storedBidiagonalWord_value (upper : Bool)
    (a : Fin (n + 1) → Word p hp) (b : Fin n → Word p hp) (i j : Fin (n + 1)) :
    (storedBidiagonalWord upper a b i j).value = storedBidiagonal upper a b i j :=
  rfl

@[simp] theorem storedBidiagonal_diag (upper : Bool)
    (a : Fin (n + 1) → Word p hp) (b : Fin n → Word p hp) (i : Fin (n + 1)) :
    storedBidiagonal upper a b i i = (a i).value := by
  cases upper <;> simp [storedBidiagonal, storedBidiagonalWord, upperStoredBidiagonalWord]

@[simp] theorem storedBidiagonal_upper (a : Fin (n + 1) → Word p hp) (b : Fin n → Word p hp)
    (i : Fin n) : storedBidiagonal true a b i.castSucc i.succ = (b i).value := by
  have hne : i.castSucc ≠ i.succ := by
    intro h
    have hv := congrArg Fin.val h
    simp at hv
  simp [storedBidiagonal, storedBidiagonalWord, upperStoredBidiagonalWord, hne]

@[simp] theorem storedBidiagonal_lower (a : Fin (n + 1) → Word p hp) (b : Fin n → Word p hp)
    (i : Fin n) : storedBidiagonal false a b i.succ i.castSucc = (b i).value :=
  storedBidiagonal_upper a b i

theorem storedBidiagonal_support (upper : Bool)
    (a : Fin (n + 1) → Word p hp) (b : Fin n → Word p hp) :
    bidiagonalSupport upper (storedBidiagonal upper a b) := by
  cases upper
  · intro i j hij h
    simp [storedBidiagonal, storedBidiagonalWord, upperStoredBidiagonalWord, Ne.symm hij,
      Ne.symm h, Word.value]
  · intro i j hij h
    simp [storedBidiagonal, storedBidiagonalWord, upperStoredBidiagonalWord, hij,
      Ne.symm h, Word.value]

private theorem all_abs_storedBidiagonal_le_iff (upper : Bool)
    (a : Fin (n + 1) → Word p hp) (b : Fin n → Word p hp) (t : ℝ) :
    (∀ i j, |storedBidiagonal upper a b i j| ≤ t) ↔
      (∀ i j, |storedTridiagonal a b i j| ≤ t) := by
  constructor
  · intro h i j
    have ht : 0 ≤ t := (abs_nonneg _).trans (h 0 0)
    have hb (i : Fin n) : |(b i).value| ≤ t := by
      cases upper
      · simpa using h i.succ i.castSucc
      · simpa using h i.castSucc i.succ
    by_cases hij : i = j
    · subst j
      simpa [storedTridiagonal, sturmTridiagonal_diagonal] using h i i
    · by_cases hadj : i.val + 1 = j.val ∨ j.val + 1 = i.val
      · exact sturmTridiagonal_adjacent_bound _ _ hb i j hadj
      · simpa [storedTridiagonal, sturmTridiagonal_support _ _ i j hij
          (fun h => hadj (Or.inl h)) (fun h => hadj (Or.inr h))] using ht
  · intro h i j
    have ht : 0 ≤ t := (abs_nonneg _).trans (h 0 0)
    have ha (i : Fin (n + 1)) : |(a i).value| ≤ t := by
      simpa [storedTridiagonal, sturmTridiagonal_diagonal] using h i i
    have hb (i : Fin n) : |(b i).value| ≤ t := by
      simpa [storedTridiagonal, sturmTridiagonal_upper] using h i.castSucc i.succ
    cases upper
    · simp only [storedBidiagonal, storedBidiagonalWord, Bool.false_eq_true, if_false,
        Matrix.transpose_apply, upperStoredBidiagonalWord]
      split
      · exact ha _
      · split
        · exact hb _
        · simpa [Word.value] using ht
    · simp only [storedBidiagonal, storedBidiagonalWord, if_true, upperStoredBidiagonalWord]
      split
      · exact ha _
      · split
        · exact hb _
        · simpa [Word.value] using ht

theorem bidiagonal_normalizationExponent_eq_none_iff (upper : Bool)
    (a : Fin (n + 1) → Word p hp) (b : Fin n → Word p hp) :
    normalizationExponent a b = none ↔ storedBidiagonal upper a b = 0 := by
  rw [normalizationExponent_eq_none_iff]
  have hz (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) :
      A = 0 ↔ ∀ i j, |A i j| ≤ 0 := by
    constructor
    · rintro rfl i j
      simp
    · intro h
      ext i j
      simpa [abs_nonpos_iff] using h i j
  rw [hz (storedTridiagonal a b), hz (storedBidiagonal upper a b)]
  exact (all_abs_storedBidiagonal_le_iff upper a b 0).symm

theorem bidiagonal_normalizationExponent_exists (upper : Bool)
    (a : Fin (n + 1) → Word p hp) (b : Fin n → Word p hp) :
    (∃ r, normalizationExponent a b = some r) ↔ storedBidiagonal upper a b ≠ 0 := by
  change (∃ r, normalizationExponent a b = some r) ↔ ¬ (storedBidiagonal upper a b = 0)
  rw [← bidiagonal_normalizationExponent_eq_none_iff]
  cases normalizationExponent a b <;> simp

/-- The covering exponent of the maximum entry magnitude of the original
bidiagonal input is exactly two less than the computed scale exponent. -/
theorem bidiagonal_normalizationExponent_least (upper : Bool)
    (a : Fin (n + 1) → Word p hp) (b : Fin n → Word p hp)
    {r : ℤ} (hr : normalizationExponent a b = some r) (l : ℤ) :
    (∀ i j, |storedBidiagonal upper a b i j| ≤ (2 : ℝ) ^ l) ↔ r - 2 ≤ l :=
  (all_abs_storedBidiagonal_le_iff upper a b _).trans (normalizationExponent_least a b hr l)

/-- The scale word is a positive normalized word at the input precision. -/
def bidiagonalScaleWord (p : ℕ) (hp : 2 ≤ p) (r : ℤ) : Word p hp :=
  .normal false (format p hp).minNormalMantissa (r + 1) (format p hp).minNormalMantissa_normalized

@[simp] theorem value_bidiagonalScaleWord (r : ℤ) :
    (bidiagonalScaleWord p hp r).value = (2 : ℝ) ^ r := by
  change (format p hp).normalizedValue false (format p hp).minNormalMantissa (r + 1) = _
  rw [FloatingPointFormat.normalizedValue_false_minNormalMantissa_eq]
  simp [FloatingPointFormat.betaR, format]

/-- Exact word scaling of the two packed bands before taking the real denotation. -/
noncomputable def scaledBidiagonal (upper : Bool)
    (a : Fin (n + 1) → Word p hp) (b : Fin n → Word p hp) (r : ℤ) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  storedBidiagonal upper (fun i => (a i).scale (-r)) (fun i => (b i).scale (-r))

theorem scaledBidiagonal_eq_word_values (upper : Bool)
    (a : Fin (n + 1) → Word p hp) (b : Fin n → Word p hp) (r : ℤ) :
    scaledBidiagonal upper a b r = fun i j =>
      (storedBidiagonalWord upper (fun i => (a i).scale (-r)) (fun i => (b i).scale (-r)) i j).value :=
  rfl

theorem scaledBidiagonal_eq (upper : Bool)
    (a : Fin (n + 1) → Word p hp) (b : Fin n → Word p hp) (r : ℤ) :
    scaledBidiagonal upper a b r = ((2 : ℝ) ^ r)⁻¹ • storedBidiagonal upper a b := by
  have h (i j : Fin (n + 1)) :
      (upperStoredBidiagonalWord (fun i => (a i).scale (-r))
          (fun i => (b i).scale (-r)) i j).value =
        ((2 : ℝ) ^ r)⁻¹ * (upperStoredBidiagonalWord a b i j).value := by
    by_cases hd : i = j
    · simp [upperStoredBidiagonalWord, hd, Word.value_scale, zpow_neg]
    · by_cases hs : i.val + 1 = j.val
      · simp [upperStoredBidiagonalWord, hd, hs, Word.value_scale, zpow_neg]
      · simp [upperStoredBidiagonalWord, hd, hs, Word.value]
  ext i j
  cases upper
  · exact h j i
  · exact h i j

theorem scaledBidiagonal_support (upper : Bool)
    (a : Fin (n + 1) → Word p hp) (b : Fin n → Word p hp) (r : ℤ) :
    bidiagonalSupport upper (scaledBidiagonal upper a b r) :=
  storedBidiagonal_support upper _ _

theorem scaledBidiagonal_native (upper : Bool)
    (a : Fin (n + 1) → Word p hp) (b : Fin n → Word p hp) (r : ℤ) (i j : Fin (n + 1)) :
    Native p hp (scaledBidiagonal upper a b r i j) :=
  Word.native_value (storedBidiagonalWord upper (fun i => (a i).scale (-r))
    (fun i => (b i).scale (-r)) i j)

private theorem sum_abs_le_half_of_one_offdiag {m : ℕ} (f : Fin m → ℝ) (d : Fin m)
    (hb : ∀ i, |f i| ≤ 1 / 4)
    (huniq : ∀ i j, i ≠ d → j ≠ d → f i ≠ 0 → f j ≠ 0 → i = j) :
    ∑ i, |f i| ≤ 1 / 2 := by
  rw [← Finset.sum_erase_add Finset.univ (fun i => |f i|) (Finset.mem_univ d)]
  by_cases h : ∃ i, i ≠ d ∧ f i ≠ 0
  · obtain ⟨i, hid, hi⟩ := h
    rw [Finset.sum_eq_single_of_mem i (Finset.mem_erase.mpr ⟨hid, Finset.mem_univ _⟩)]
    · linarith [hb i, hb d]
    · intro j hj hji
      apply abs_eq_zero.mpr
      by_contra hjne
      exact hji (huniq j i (Finset.ne_of_mem_erase hj) hid hjne hi)
  · push_neg at h
    rw [Finset.sum_eq_zero (fun i hi => by
      rw [h i (Finset.ne_of_mem_erase hi), abs_zero])]
    linarith [hb d]

/-- The two possible nonzero entries in each row and column give the operator bound. -/
theorem bidiagonal_operatorNorm_le_half (upper : Bool)
    (C : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (hC : bidiagonalSupport upper C)
    (he : ∀ i j, |C i j| ≤ 1 / 4) :
    realMatrixOperatorNorm C ≤ 1 / 2 := by
  apply realMatrixOperatorNorm_le_of_row_col_abs_sum_le C (by norm_num)
  · intro i
    apply sum_abs_le_half_of_one_offdiag (C i) i (he i)
    intro j l hj hl hneJ hneL
    apply Fin.ext
    cases upper
    · have hJ := not_not.mp (fun h => hneJ (hC i j (Ne.symm hj) h))
      have hL := not_not.mp (fun h => hneL (hC i l (Ne.symm hl) h))
      omega
    · have hJ := not_not.mp (fun h => hneJ (hC i j (Ne.symm hj) h))
      have hL := not_not.mp (fun h => hneL (hC i l (Ne.symm hl) h))
      omega
  · intro j
    apply sum_abs_le_half_of_one_offdiag (fun i => C i j) j (fun i => he i j)
    intro i l hi hl hneI hneL
    apply Fin.ext
    cases upper
    · have hI := not_not.mp (fun h => hneI (hC i j hi h))
      have hL := not_not.mp (fun h => hneL (hC l j hl h))
      omega
    · have hI := not_not.mp (fun h => hneI (hC i j hi h))
      have hL := not_not.mp (fun h => hneL (hC l j hl h))
      omega

/-- The actual word exponent gives the entry bound, the operator norm bound,
and the strict bound on the scale in terms of the original matrix. -/
theorem scaledBidiagonal_bounds (upper : Bool)
    (a : Fin (n + 1) → Word p hp) (b : Fin n → Word p hp)
    {r : ℤ} (hr : normalizationExponent a b = some r) :
    let C := scaledBidiagonal upper a b r
    (∀ i j, |C i j| ≤ 1 / 4) ∧ realMatrixOperatorNorm C ≤ 1 / 2 ∧
      (2 : ℝ) ^ r < 8 * realMatrixOperatorNorm (storedBidiagonal upper a b) := by
  dsimp only
  have hcov := (bidiagonal_normalizationExponent_least upper a b hr (r - 2)).mpr le_rfl
  have he (i j : Fin (n + 1)) : |scaledBidiagonal upper a b r i j| ≤ 1 / 4 := by
    rw [scaledBidiagonal_eq, Matrix.smul_apply, smul_eq_mul, abs_mul,
      abs_of_pos (by positivity : 0 < ((2 : ℝ) ^ r)⁻¹)]
    calc
      _ ≤ ((2 : ℝ) ^ r)⁻¹ * (2 : ℝ) ^ (r - 2) := by gcongr; exact hcov i j
      _ = _ := by rw [zpow_sub₀ (by norm_num : (2 : ℝ) ≠ 0)]; field_simp; norm_num
  refine ⟨he, bidiagonal_operatorNorm_le_half upper _ (scaledBidiagonal_support upper a b r) he, ?_⟩
  have hsmall : ¬ ∀ i j, |storedBidiagonal upper a b i j| ≤ (2 : ℝ) ^ (r - 3) :=
    fun h => (show ¬ r - 2 ≤ r - 3 by omega)
      ((bidiagonal_normalizationExponent_least upper a b hr (r - 3)).mp h)
  push_neg at hsmall
  obtain ⟨i, j, hij⟩ := hsmall
  calc
    (2 : ℝ) ^ r = 8 * (2 : ℝ) ^ (r - 3) := by
      rw [show r = (r - 3) + 3 by omega, zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
      norm_num [mul_comm]
    _ < 8 * |storedBidiagonal upper a b i j| :=
      mul_lt_mul_of_pos_left hij (by norm_num)
    _ ≤ _ := by gcongr; exact abs_matrix_entry_le_realMatrixOperatorNorm _ i j

end NumStability.CertifiedTridiagonalEigenpairs
