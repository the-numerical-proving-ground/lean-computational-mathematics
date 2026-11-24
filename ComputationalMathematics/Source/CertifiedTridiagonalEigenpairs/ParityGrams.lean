import ComputationalMathematics.Analysis.MatrixStructure.Bipartite.MassParityGrams
import ComputationalMathematics.Analysis.MatrixStructure.Bipartite.MassShiftSpectral
import ComputationalMathematics.Analysis.MatrixInequalities.NormalizedGram
import ComputationalMathematics.HDP.Matrix.ReindexSpectral

/-!
# Parity Grams from a common mass-shifted witness

Section 8 of the certified tridiagonal eigenpair paper groups the right
parities into high positive and low negative columns. The two arrays
below retain the selected columns of the same orthonormal witness.
-/

open Matrix
open scoped Matrix.Norms.L2Operator

namespace NumStability.CertifiedTridiagonalEigenpairs

open Matrix.Bipartite Matrix.Bipartite.MassParityGrams NormalizedGram

private theorem magnitude_mono (α : ℝ) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    massMagnitude α s ≤ massMagnitude α t := by
  exact Real.sqrt_le_sqrt (by nlinarith [mul_nonneg (sub_nonneg.mpr hst) (by linarith : 0 ≤ t + s)])

private theorem magnitude_le_sqrt_two_mul {α s : ℝ} (hα : 0 < α) (hs : α ≤ s) :
    massMagnitude α s ≤ Real.sqrt 2 * s := by
  apply (sq_le_sq₀ (massMagnitude_nonneg α s) (mul_nonneg (Real.sqrt_nonneg 2) (hα.le.trans hs))).1
  rw [massMagnitude_sq, mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  nlinarith [mul_nonneg (sub_nonneg.mpr hs) (by linarith : 0 ≤ s + α)]

/-- The mass magnitudes across a bin of width `α` above `α` are separated by
at least `α / √2`. -/
theorem parity_bin_magnitude_gap {α cut : ℝ} (hα : 0 < α) (hcut : α ≤ cut) :
    α / Real.sqrt 2 ≤ massMagnitude α (cut + α) - massMagnitude α cut := by
  let h := massMagnitude α (cut + α)
  let l := massMagnitude α cut
  let q := Real.sqrt 2
  have hq : 0 < q := by dsimp [q]; positivity
  have hs : 0 < h + l := add_pos
    (hα.trans_le (le_massMagnitude hα.le _)) (hα.trans_le (le_massMagnitude hα.le _))
  have hmul : (h - l) * (h + l) = α * (cut + α + cut) := by
    dsimp [h, l]
    nlinarith only [massMagnitude_sq α (cut + α), massMagnitude_sq α cut]
  have hsum : h + l ≤ q * (cut + α + cut) := by
    have hh := magnitude_le_sqrt_two_mul hα (show α ≤ cut + α by linarith)
    have hl := magnitude_le_sqrt_two_mul hα hcut
    change h ≤ q * (cut + α) at hh
    change l ≤ q * cut at hl
    linarith only [hh, hl]
  have hc : α * (h + l) ≤ ((h - l) * q) * (h + l) := calc
    _ ≤ α * (q * (cut + α + cut)) := mul_le_mul_of_nonneg_left hsum hα.le
    _ = q * ((h - l) * (h + l)) := by rw [hmul]; ring
    _ = _ := by ring
  exact (div_le_iff₀ hq).2 ((mul_le_mul_iff_of_pos_right hs).1 hc)

/-- Positive assigned labels and a high/low cut in one common orthonormal
witness give both raw Gram estimates. Right columns are grouped high before low. -/
theorem parity_gram_deviations_of_common_witness {n r k h l : ℕ}
    (C : Matrix (Fin n) (Fin n) ℝ) (α η cut : ℝ)
    (W : Matrix (Fin n ⊕ Fin n) (Fin r) ℝ) (labels : Fin r → ℝ)
    (eP : Fin k ↪ Fin r) (eH : Fin h ↪ Fin r) (eL : Fin l ↪ Fin r)
    (sP : Fin k → ℝ) (sH : Fin h → ℝ) (sL : Fin l → ℝ)
    (hα : 0 < α) (hη : 0 ≤ η) (hcut : α ≤ cut)
    (hsH : ∀ i, cut + α ≤ sH i) (hsL0 : ∀ j, 0 ≤ sL j) (hsL : ∀ j, sL j ≤ cut)
    (hW : Wᵀ * W = 1)
    (hlabelsP : ∀ i, labels (eP i) = massMagnitude α (sP i))
    (hlabelsH : ∀ i, labels (eH i) = massMagnitude α (sH i))
    (hlabelsL : ∀ j, labels (eL j) = -massMagnitude α (sL j))
    (hE : ‖massShift C α * W - W * diagonal labels‖ ≤ η) :
    let X := left (columns W eP)
    let Y := mixedRight (columns W eH) (columns W eL)
    let dX := fun i => (1 + α / massMagnitude α (sP i)) / 2
    let dY := Sum.elim (fun i => (1 - α / massMagnitude α (sH i)) / 2)
      (fun j => (1 + α / massMagnitude α (sL j)) / 2)
    ‖Xᵀ * X - diagonal dX‖ ≤ η / (2 * α) ∧
      ‖Yᵀ * Y - diagonal dY‖ ≤ (1 / 2 + Real.sqrt 2) * (η / α) := by
  dsimp only
  have hHL : ∀ i j, eH i ≠ eL j := by
    intro i j hij
    have hp := le_massMagnitude hα.le (sH i)
    have hn := le_massMagnitude hα.le (sL j)
    have he : massMagnitude α (sH i) = -massMagnitude α (sL j) := by
      rw [← hlabelsH, ← hlabelsL, hij]
    linarith
  have hsel (d : ℕ) (e : Fin d ↪ Fin r) :
      ‖massShift C α * columns W e - columns W e * diagonal (labels ∘ e)‖ ≤ η := by
    rw [residual_columns]
    exact (columns_norm_le _ e).trans hE
  have hEP : ‖massShift C α * columns W eP -
      columns W eP * diagonal (fun i => massMagnitude α (sP i))‖ ≤ η := by
    simpa only [Function.comp_def, hlabelsP] using hsel k eP
  have hEH : ‖massShift C α * columns W eH -
      columns W eH * diagonal (fun i => massMagnitude α (sH i))‖ ≤ η := by
    simpa only [Function.comp_def, hlabelsH] using hsel h eH
  have hEL : ‖massShift C α * columns W eL -
      columns W eL * diagonal (fun j => -massMagnitude α (sL j))‖ ≤ η := by
    simpa only [Function.comp_def, hlabelsL] using hsel l eL
  constructor
  · exact positive_left_gram_deviation C α η (columns W eP) _
      hα hη (fun i => le_massMagnitude hα.le _) (columns_orthonormal W hW eP) hEP
  · have h := mixedRight_gram_deviation C α η (columns W eH) (columns W eL)
      (fun i => massMagnitude α (sH i)) (fun j => massMagnitude α (sL j))
      (massMagnitude α (cut + α)) (massMagnitude α cut) (α / Real.sqrt 2)
      hα hη (columns_orthonormal W hW eH) (columns_orthonormal W hW eL)
      (columns_cross_zero W hW eH eL hHL) (by positivity)
      (parity_bin_magnitude_gap hα hcut)
      (fun i => magnitude_mono α (by linarith) (hsH i))
      (fun j => magnitude_mono α (hsL0 j) (hsL j))
      (fun i => le_massMagnitude hα.le _) (fun j => le_massMagnitude hα.le _) hEH hEL
    convert h using 1
    rw [div_div_eq_mul_div]
    ring

/-- At the paper's residual budget, each raw Gram operator error is bounded
by `u/8` and each ideal diagonal is at least one quarter. -/
theorem parity_raw_gram_budgets {n r k h l : ℕ}
    (C : Matrix (Fin n) (Fin n) ℝ) (α η cut u : ℝ)
    (W : Matrix (Fin n ⊕ Fin n) (Fin r) ℝ) (labels : Fin r → ℝ)
    (eP : Fin k ↪ Fin r) (eH : Fin h ↪ Fin r) (eL : Fin l ↪ Fin r)
    (sP : Fin k → ℝ) (sH : Fin h → ℝ) (sL : Fin l → ℝ)
    (hα : 0 < α) (hη : 0 ≤ η) (hcut : α ≤ cut) (hu : 0 < u) (hbudget : η / α = u / 16)
    (hsH : ∀ i, cut + α ≤ sH i) (hsL0 : ∀ j, 0 ≤ sL j) (hsL : ∀ j, sL j ≤ cut)
    (hW : Wᵀ * W = 1)
    (hlabelsP : ∀ i, labels (eP i) = massMagnitude α (sP i))
    (hlabelsH : ∀ i, labels (eH i) = massMagnitude α (sH i))
    (hlabelsL : ∀ j, labels (eL j) = -massMagnitude α (sL j))
    (hE : ‖massShift C α * W - W * diagonal labels‖ ≤ η) :
    let X := left (columns W eP)
    let Y := mixedRight (columns W eH) (columns W eL)
    let dX := fun i => (1 + α / massMagnitude α (sP i)) / 2
    let dY := Sum.elim (fun i => (1 - α / massMagnitude α (sH i)) / 2)
      (fun j => (1 + α / massMagnitude α (sL j)) / 2)
    (∀ i, (1 / 4 : ℝ) ≤ dX i) ∧ (∀ j, (1 / 4 : ℝ) ≤ dY j) ∧
      ‖Xᵀ * X - diagonal dX‖ ≤ u / 32 ∧ ‖Yᵀ * Y - diagonal dY‖ < u / 8 := by
  have h := parity_gram_deviations_of_common_witness C α η cut W labels eP eH eL
    sP sH sL hα hη hcut hsH hsL0 hsL hW hlabelsP hlabelsH hlabelsL hE
  dsimp only at h ⊢
  have hfloor (s : ℝ) : (1 / 4 : ℝ) ≤ (1 + α / massMagnitude α s) / 2 := by
    have hb := div_nonneg hα.le (massMagnitude_nonneg α s)
    linarith
  refine ⟨fun i => hfloor (sP i), ?_, ?_, ?_⟩
  · intro j
    cases j with
    | inl i =>
      change (1 / 4 : ℝ) ≤ (1 - α / massMagnitude α (sH i)) / 2
      have hs : 2 * α ≤ sH i := by linarith [hsH i]
      have hsm : sH i ≤ massMagnitude α (sH i) := by
        exact (sq_le_sq₀ (by linarith : 0 ≤ sH i) (massMagnitude_nonneg α _)).1 (by
          rw [massMagnitude_sq]; linarith only [sq_nonneg α])
      have hm := (hα.trans_le (le_massMagnitude hα.le (sH i)))
      have hb : α / massMagnitude α (sH i) ≤ 1 / 2 := by
        apply (div_le_iff₀ hm).2
        linarith
      linarith
    | inr j => exact hfloor (sL j)
  · rw [mul_comm (2 : ℝ) α, div_mul_eq_div_div, hbudget] at h
    exact h.1.trans_eq (by ring)
  · have hdu : 0 < u / 16 := by positivity
    have hsqrt : Real.sqrt 2 < 3 / 2 := by
      apply (sq_lt_sq₀ (Real.sqrt_nonneg 2) (by norm_num)).1
      rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
      norm_num
    calc
      _ ≤ (1 / 2 + Real.sqrt 2) * (u / 16) := hbudget ▸ h.2
      _ < (1 / 2 + 3 / 2) * (u / 16) :=
        mul_lt_mul_of_pos_right (add_lt_add_right hsqrt _) hdu
      _ = _ := by ring

/-- Reordering the raw parity columns into requested-rank order preserves the
Gram error with the ideal diagonal in that same order. -/
theorem parity_gram_deviation_reindex {m ι κ : Type*}
    [Fintype m] [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (X : Matrix m ι ℝ) (d : ι → ℝ) (e : κ ≃ ι) :
    ‖(X.submatrix id e)ᵀ * X.submatrix id e - diagonal (d ∘ e)‖ =
      ‖Xᵀ * X - diagonal d‖ := by
  rw [Matrix.transpose_submatrix, ← Matrix.submatrix_mul Xᵀ X e id e Function.bijective_id]
  have he : (Xᵀ * X).submatrix e e - diagonal (d ∘ e) =
      Matrix.reindex e.symm e.symm (Xᵀ * X - diagonal d) := by
    rw [Matrix.reindex_apply, Equiv.symm_symm, ← Matrix.submatrix_diagonal_equiv]
    rfl
  rw [he, NumStability.HDP.Matrix.l2_opNorm_reindex]

/-- Column normalization gives unit columns, the paper's pairwise and operator
Gram bounds, and the corresponding operator norm bound. This applies to either
raw parity using `parity_raw_gram_budgets`. -/
theorem parity_normalized_gram_budgets {m ι : Type*} [Fintype m] [Fintype ι] [DecidableEq ι]
    (X : Matrix m ι ℝ) (d : ι → ℝ) (u : ℝ) (hu : u ≤ 1 / 256)
    (hd : ∀ i, (1 / 4 : ℝ) ≤ d i) (hF : ‖Xᵀ * X - diagonal d‖ ≤ u / 8) :
    let N := normalizeColumns X
    (∀ i, (1 / 3 : ℝ) ≤ columnNorm X i) ∧
    (∀ i, (Nᵀ * N) i i = 1) ∧
    (∀ i j, i ≠ j → |(Nᵀ * N) i j| ≤ 9 * u / 8) ∧
    ‖Nᵀ * N - 1‖ ≤ 9 * u / 4 ∧ ‖N‖ ≤ 1 + 9 * u / 8 := by
  dsimp only
  have hu0 : 0 ≤ u := by linarith only [norm_nonneg (Xᵀ * X - diagonal d), hF]
  have hc : (0 : ℝ) < 1 / 3 := by norm_num
  have hcol : ∀ i, (1 / 3 : ℝ) ≤ columnNorm X i :=
    le_columnNorm_of_gram X d hc.le (by intro i; nlinarith [hd i]) hF
  have hop := normalize_gram_norm_le X d hc hcol hF
  have hop' : ‖(normalizeColumns X)ᵀ * normalizeColumns X - 1‖ ≤ 9 * u / 4 :=
    hop.trans_eq (by ring)
  refine ⟨hcol, fun i => normalize_gram_diag X (hc.trans_le (hcol i)), ?_, hop', ?_⟩
  · intro i j hij
    exact (abs_normalize_gram_apply_le X d hc hcol hF hij).trans_eq (by ring)
  · let N := normalizeColumns X
    have h1 : ‖(1 : Matrix ι ι ℝ)‖ ≤ 1 := by
      rw [← Matrix.diagonal_one, Matrix.l2_opNorm_diagonal]
      exact (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)).2 (by intro i; simp)
    have hnorm : ‖N‖ * ‖N‖ ≤ 1 + 9 * u / 4 := by
      rw [← Matrix.l2_opNorm_conjTranspose_mul_self, Matrix.conjTranspose_eq_transpose_of_trivial]
      conv_lhs => rw [← sub_add_cancel ((Nᵀ) * N) 1]
      exact (norm_add_le _ _).trans (by linarith only [hop', h1])
    apply (sq_le_sq₀ (norm_nonneg N) (by positivity : 0 ≤ 1 + 9 * u / 8)).1
    nlinarith only [hnorm, sq_nonneg u]

end NumStability.CertifiedTridiagonalEigenpairs
