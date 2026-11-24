import ComputationalMathematics.Analysis.FloatingPointArithmetic.UnboundedBinary.ScalarOperations
import ComputationalMathematics.Analysis.MatrixStructure.SymmetricTridiagonal

/-!
# Power-of-two normalization of stored tridiagonal matrices

The input consists of the diagonal and one adjacent band in the unbounded
binary format. In the nonzero branch the largest stored magnitude determines
the least covering power of two. The scale `R` is four times that power.
-/

namespace NumStability.CertifiedTridiagonalEigenpairs

open FloatingPointFormat.UnboundedBinary

variable {p n : ℕ} {hp : 2 ≤ p}

/-- The real matrix represented by the two stored tridiagonal bands. -/
noncomputable def storedTridiagonal (a : Fin (n + 1) → Word p hp) (b : Fin n → Word p hp) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  sturmTridiagonal (fun i => (a i).value) (fun i => (b i).value)

private theorem normal_magnitude_bounds (negative : Bool) (m : ℕ) (e : ℤ)
    (hm : (format p hp).normalizedMantissa m) :
    (2 : ℝ) ^ (e - 1) ≤ |(Word.normal negative m e hm).value| ∧
      |(Word.normal negative m e hm).value| < (2 : ℝ) ^ e :=
  FloatingPointFormat.normalizedValue_abs_between_beta_powers hm

private def largerMagnitude : Word p hp → Word p hp → Word p hp
  | .zero, y => y
  | x, .zero => x
  | x@(.normal _ m e _), y@(.normal _ m' e' _) =>
      if e < e' ∨ (e = e' ∧ m ≤ m') then y else x

private theorem largerMagnitude_eq (x y : Word p hp) :
    largerMagnitude x y = x ∨ largerMagnitude x y = y := by
  cases x <;> cases y <;> simp only [largerMagnitude, true_or, or_true]
  split <;> simp

private theorem normal_magnitude_le_of_exponent_lt
    {negative negative' : Bool} {m m' : ℕ} {e e' : ℤ}
    {hm : (format p hp).normalizedMantissa m} {hm' : (format p hp).normalizedMantissa m'}
    (h : e < e') :
    |(Word.normal negative m e hm).value| ≤ |(Word.normal negative' m' e' hm').value| :=
  (normal_magnitude_bounds negative m e hm).2.le.trans
    ((zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega : e ≤ e' - 1)).trans
      (normal_magnitude_bounds negative' m' e' hm').1)

private theorem normal_magnitude_le_of_significand_le
    {negative negative' : Bool} {m m' : ℕ} {e : ℤ}
    {hm : (format p hp).normalizedMantissa m} {hm' : (format p hp).normalizedMantissa m'}
    (h : m ≤ m') :
    |(Word.normal negative m e hm).value| ≤ |(Word.normal negative' m' e hm').value| := by
  simp only [Word.value, FloatingPointFormat.normalizedValue_abs]
  exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr h)
    ((format p hp).betaR_zpow_nonneg _)

private theorem abs_largerMagnitude (x y : Word p hp) :
    |(largerMagnitude x y).value| = max |x.value| |y.value| := by
  cases x with
  | zero => simp [largerMagnitude, Word.value, abs_nonneg]
  | normal neg m e hm =>
    cases y with
    | zero => simp [largerMagnitude, Word.value, abs_nonneg]
    | normal neg' m' e' hm' =>
      dsimp only [largerMagnitude]
      split
      · rename_i h
        apply (max_eq_right _).symm
        rcases h with he | ⟨rfl, h⟩
        · exact normal_magnitude_le_of_exponent_lt he
        · exact normal_magnitude_le_of_significand_le h
      · rename_i h
        apply (max_eq_left _).symm
        by_cases he : e = e'
        · subst e'
          exact normal_magnitude_le_of_significand_le (by omega)
        · exact normal_magnitude_le_of_exponent_lt (by omega)

/-- A stored entry of largest absolute value, found by a single scan of the
diagonal and adjacent band. -/
def largestStoredEntry (a : Fin (n + 1) → Word p hp) (b : Fin n → Word p hp) : Word p hp :=
  (List.ofFn a ++ List.ofFn b).foldr largerMagnitude .zero

private theorem le_abs_fold_larger {x : Word p hp} {xs : List (Word p hp)} (hx : x ∈ xs) :
    |x.value| ≤ |(xs.foldr largerMagnitude .zero).value| := by
  induction xs with
  | nil => simp at hx
  | cons y ys ih =>
    rw [List.foldr_cons, abs_largerMagnitude]
    rcases List.mem_cons.mp hx with rfl | h
    · exact le_max_left _ _
    · exact (ih h).trans (le_max_right _ _)

private theorem fold_larger_eq_zero_or_mem (xs : List (Word p hp)) :
    xs.foldr largerMagnitude .zero = .zero ∨ xs.foldr largerMagnitude .zero ∈ xs := by
  induction xs with
  | nil => simp
  | cons y ys ih =>
    rw [List.foldr_cons]
    rcases largerMagnitude_eq y (ys.foldr largerMagnitude .zero) with H | H
    · rw [H]
      exact Or.inr List.mem_cons_self
    · rw [H]
      exact ih.imp_right (List.mem_cons_of_mem _)

theorem abs_entry_le_largestStoredEntry
    (a : Fin (n + 1) → Word p hp) (b : Fin n → Word p hp)
    (i j : Fin (n + 1)) : |storedTridiagonal a b i j| ≤ |(largestStoredEntry a b).value| := by
  have ha (i : Fin (n + 1)) : |(a i).value| ≤ |(largestStoredEntry a b).value| :=
    le_abs_fold_larger (List.mem_append_left _ (List.mem_ofFn.mpr ⟨i, rfl⟩))
  have hb (i : Fin n) : |(b i).value| ≤ |(largestStoredEntry a b).value| :=
    le_abs_fold_larger (List.mem_append_right _ (List.mem_ofFn.mpr ⟨i, rfl⟩))
  by_cases hij : i = j
  · subst j
    simpa only [storedTridiagonal, sturmTridiagonal_diagonal] using ha i
  · by_cases hadj : i.val + 1 = j.val ∨ j.val + 1 = i.val
    · exact sturmTridiagonal_adjacent_bound _ _ hb i j hadj
    · rw [storedTridiagonal, sturmTridiagonal_support _ _ i j hij
        (fun h => hadj (Or.inl h)) (fun h => hadj (Or.inr h)), abs_zero]
      exact abs_nonneg _

/-- The scanned magnitude is attained at an entry of the represented matrix. -/
theorem largestStoredEntry_attained
    (a : Fin (n + 1) → Word p hp) (b : Fin n → Word p hp) :
    ∃ i j, |storedTridiagonal a b i j| = |(largestStoredEntry a b).value| := by
  rcases fold_larger_eq_zero_or_mem (List.ofFn a ++ List.ofFn b) with H | H
  · change largestStoredEntry a b = .zero at H
    refine ⟨0, 0, le_antisymm (abs_entry_le_largestStoredEntry a b 0 0) ?_⟩
    simp [H, Word.value]
  · change largestStoredEntry a b ∈ List.ofFn a ++ List.ofFn b at H
    rcases List.mem_append.mp H with ha | hb
    · obtain ⟨i, hi⟩ := List.mem_ofFn.mp ha
      exact ⟨i, i, by rw [← hi, storedTridiagonal, sturmTridiagonal_diagonal]⟩
    · obtain ⟨i, hi⟩ := List.mem_ofFn.mp hb
      exact ⟨i.castSucc, i.succ, by rw [← hi, storedTridiagonal, sturmTridiagonal_upper]⟩

theorem abs_largestStoredEntry_le_operatorNorm
    (a : Fin (n + 1) → Word p hp) (b : Fin n → Word p hp) :
    |(largestStoredEntry a b).value| ≤ realMatrixOperatorNorm (storedTridiagonal a b) := by
  obtain ⟨i, j, h⟩ := largestStoredEntry_attained a b
  rw [← h]
  exact abs_matrix_entry_le_realMatrixOperatorNorm _ i j

/-- Exponent of the least power of two covering the word's absolute value.
Zero is handled separately since it has no least positive covering power. -/
def coveringExponent : Word p hp → Option ℤ
  | .zero => none
  | .normal _ m e _ => some (if m = (format p hp).minNormalMantissa then e - 1 else e)

theorem coveringExponent_bounds {w : Word p hp} {k : ℤ}
    (hk : coveringExponent w = some k) :
    (2 : ℝ) ^ (k - 1) < |w.value| ∧ |w.value| ≤ (2 : ℝ) ^ k := by
  cases w with
  | zero => simp [coveringExponent] at hk
  | normal negative m e hm =>
    simp only [coveringExponent, Option.some.injEq] at hk
    split at hk
    · rename_i h
      subst k
      subst m
      have heq : |(Word.normal negative _ e hm).value| = (2 : ℝ) ^ (e - 1) :=
        FloatingPointFormat.normalizedValue_minNormalMantissa_abs_eq _ _ _
      rw [heq]
      exact ⟨zpow_lt_zpow_right₀ (by norm_num) (by omega), le_rfl⟩
    · rename_i h
      subst k
      refine ⟨?_, (normal_magnitude_bounds negative m e hm).2.le⟩
      change (format p hp).betaR ^ (e - 1) < |(format p hp).normalizedValue negative m e|
      rw [← FloatingPointFormat.minNormalMantissa_scale_eq (format p hp) e,
        FloatingPointFormat.normalizedValue_abs]
      exact mul_lt_mul_of_pos_right (Nat.cast_lt.mpr (lt_of_le_of_ne hm.1 (Ne.symm h)))
        ((format p hp).betaR_zpow_pos _)

theorem coveringExponent_least {w : Word p hp} {k : ℤ} (hk : coveringExponent w = some k)
    (l : ℤ) : |w.value| ≤ (2 : ℝ) ^ l ↔ k ≤ l := by
  have h := coveringExponent_bounds hk
  constructor
  · intro hl
    by_contra! hkl
    exact h.1.not_ge (hl.trans (zpow_le_zpow_right₀ (by norm_num) (by omega)))
  · intro hkl
    exact h.2.trans (zpow_le_zpow_right₀ (by norm_num) hkl)

/-- The exponent of `R = 4P`, absent when all stored entries are zero. -/
def normalizationExponent (a : Fin (n + 1) → Word p hp) (b : Fin n → Word p hp) :
    Option ℤ :=
  (coveringExponent (largestStoredEntry a b)).map (· + 2)


theorem normalizationExponent_eq_none_iff (a : Fin (n + 1) → Word p hp)
    (b : Fin n → Word p hp) : normalizationExponent a b = none ↔ storedTridiagonal a b = 0 := by
  unfold normalizationExponent
  cases H : largestStoredEntry a b with
  | zero =>
    simp only [coveringExponent, Option.map_none, true_iff]
    ext i j
    have hij := abs_entry_le_largestStoredEntry a b i j
    simpa [H, Word.value] using hij
  | normal negative m e hm =>
    simp only [coveringExponent, Option.map_some, reduceCtorEq, false_iff]
    intro hz
    have h := abs_largestStoredEntry_le_operatorNorm a b
    rw [H, hz] at h
    have hn : realMatrixOperatorNorm (0 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) = 0 := by
      unfold realMatrixOperatorNorm
      simp [realMatrixContinuousLinearMap]
    rw [hn] at h
    exact (not_le_of_gt (show 0 < |(Word.normal negative m e hm).value| from
      (by positivity : 0 < (2 : ℝ) ^ (e - 1)).trans_le
        (normal_magnitude_bounds negative m e hm).1)) h

private theorem normalizationExponent_eq_some
    {a : Fin (n + 1) → Word p hp} {b : Fin n → Word p hp} {r : ℤ}
    (hr : normalizationExponent a b = some r) :
    ∃ k, coveringExponent (largestStoredEntry a b) = some k ∧ r = k + 2 := by
  unfold normalizationExponent at hr
  cases H : coveringExponent (largestStoredEntry a b) with
  | none => simp [H] at hr
  | some k =>
    rw [H, Option.map_some, Option.some.injEq] at hr
    exact ⟨k, rfl, hr.symm⟩

/-- The scale is four times the least power covering every entry magnitude. -/
theorem normalizationExponent_least
    (a : Fin (n + 1) → Word p hp) (b : Fin n → Word p hp)
    {r : ℤ} (hr : normalizationExponent a b = some r) (l : ℤ) :
    (∀ i j, |storedTridiagonal a b i j| ≤ (2 : ℝ) ^ l) ↔ r - 2 ≤ l := by
  obtain ⟨k, hk, rfl⟩ := normalizationExponent_eq_some hr
  rw [add_sub_cancel_right, ← coveringExponent_least hk]
  obtain ⟨i, j, h⟩ := largestStoredEntry_attained a b
  exact ⟨fun H => h ▸ H i j, fun H i j => (abs_entry_le_largestStoredEntry a b i j).trans H⟩

/-- Exact representation-level division of both bands by `2^r`. -/
noncomputable def normalizedTridiagonal
    (a : Fin (n + 1) → Word p hp) (b : Fin n → Word p hp) (r : ℤ) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  storedTridiagonal (fun i => (a i).scale (-r)) (fun i => (b i).scale (-r))

theorem normalizedTridiagonal_eq
    (a : Fin (n + 1) → Word p hp) (b : Fin n → Word p hp) (r : ℤ) :
    normalizedTridiagonal a b r = ((2 : ℝ) ^ r)⁻¹ • storedTridiagonal a b := by
  ext i j
  simp only [normalizedTridiagonal, storedTridiagonal, Word.value_scale, zpow_neg,
    sturmTridiagonal, Matrix.smul_apply, smul_eq_mul, Matrix.add_apply, Matrix.sum_apply,
    mul_add, Finset.mul_sum]
  congr 1
  · by_cases h : i = j <;> simp [h]
  · apply Finset.sum_congr rfl
    intro k _
    simp only [Matrix.single_apply]
    split <;> split <;> simp

/-- The paper's simultaneous entry, Schur and strict scale bounds. -/
theorem normalizedTridiagonal_bounds
    (a : Fin (n + 1) → Word p hp) (b : Fin n → Word p hp)
    {r : ℤ} (hr : normalizationExponent a b = some r) :
    let S := normalizedTridiagonal a b r
    let rowMax := Finset.univ.sup' Finset.univ_nonempty
      (fun i => ∑ j, |S i j|)
    (∀ i j, |S i j| ≤ 1 / 4) ∧ realMatrixOperatorNorm S ≤ rowMax ∧
      rowMax ≤ 3 / 4 ∧ (2 : ℝ) ^ r < 8 * realMatrixOperatorNorm (storedTridiagonal a b) := by
  dsimp only
  let S := normalizedTridiagonal a b r
  let rowMax := Finset.univ.sup' Finset.univ_nonempty (fun i => ∑ j, |S i j|)
  have hrpos : 0 < (2 : ℝ) ^ r := by positivity
  have hcov (i j : Fin (n + 1)) :
      |storedTridiagonal a b i j| ≤ (2 : ℝ) ^ (r - 2) :=
    (normalizationExponent_least a b hr (r - 2)).mpr le_rfl i j
  have hent (i j : Fin (n + 1)) : |S i j| ≤ 1 / 4 := by
    change |normalizedTridiagonal a b r i j| ≤ 1 / 4
    rw [normalizedTridiagonal_eq, Matrix.smul_apply, smul_eq_mul, abs_mul,
      abs_of_pos (inv_pos.mpr hrpos)]
    calc
      _ ≤ ((2 : ℝ) ^ r)⁻¹ * (2 : ℝ) ^ (r - 2) :=
        mul_le_mul_of_nonneg_left (hcov i j) (inv_nonneg.mpr hrpos.le)
      _ = _ := by rw [zpow_sub₀ (by norm_num : (2 : ℝ) ≠ 0)]; field_simp; norm_num
  have hrow (i : Fin (n + 1)) : ∑ j, |S i j| ≤ 3 / 4 := by
    calc
      _ ≤ 1 / 4 + 2 * (1 / 4) :=
        tridiagonal_abs_row_sum_le S (by norm_num)
          (sturmTridiagonal_band _ _) (fun i => hent i i) (fun i j _ => hent i j) i
      _ = _ := by norm_num
  have hs (i j : Fin (n + 1)) : S i j = S j i := by
    have H := sturmTridiagonal_isHermitian
      (fun i => ((a i).scale (-r)).value) (fun i => ((b i).scale (-r)).value)
    exact (congrArg (fun A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ => A i j) H).symm
  have hrowMax (i : Fin (n + 1)) : ∑ j, |S i j| ≤ rowMax :=
    Finset.le_sup' (fun i => ∑ j, |S i j|) (Finset.mem_univ i)
  have hop : realMatrixOperatorNorm S ≤ rowMax := by
    refine realMatrixOperatorNorm_le_of_row_col_abs_sum_le S ?_ hrowMax ?_
    · exact (Finset.sum_nonneg (fun _ _ => abs_nonneg _)).trans (hrowMax 0)
    · intro j
      simpa only [hs] using hrowMax j
  refine ⟨hent, hop, Finset.sup'_le _ _ (fun i _ => hrow i), ?_⟩
  obtain ⟨k, hk, rfl⟩ := normalizationExponent_eq_some hr
  calc
    (2 : ℝ) ^ (k + 2) = 8 * (2 : ℝ) ^ (k - 1) := by
      rw [show k + 2 = (k - 1) + 3 by omega, zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
      norm_num [mul_comm]
    _ < 8 * |(largestStoredEntry a b).value| := by
      gcongr
      exact (coveringExponent_bounds hk).1
    _ ≤ _ := by gcongr; exact abs_largestStoredEntry_le_operatorNorm a b

end NumStability.CertifiedTridiagonalEigenpairs
