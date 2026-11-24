import ComputationalMathematics.Analysis.SingularValues.FullRealSVD.Unsorted
import ComputationalMathematics.Analysis.FloatingPointArithmetic.UnboundedBinary.VectorNormalization
import ComputationalMathematics.Source.CertifiedTridiagonalEigenpairs.BidiagonalSVDPrecision
import ComputationalMathematics.Source.CertifiedTridiagonalEigenpairs.BidiagonalSVDResiduals
import ComputationalMathematics.Analysis.OperatorNorms.RealComplexification

/-!
# Rounding and rescaling the bidiagonal SVD output

These estimates control the changes between the exactly normalized parities,
the stored singular-vector columns and the final singular-value labels.
-/

open Matrix
open scoped Matrix.Norms.L2Operator RealInnerProductSpace

namespace NumStability.CertifiedTridiagonalEigenpairs

open FloatingPointFormat.UnboundedBinary NormalizedGram

noncomputable section

/-- The guard controls the auxiliary roundoff and the combined column error
from raw storage, auxiliary normalization and final precision. -/
theorem svd_normalization_roundoff_budget {n k p : ℕ} (hn : 2 ≤ n)
    (hguard : precisionGuard n p) :
    let u := unitRoundoff p
    let ε := unitRoundoff (svdAuxiliaryPrecision k p)
    (n : ℝ) * ε ≤ u / (131072 * svdKappa k) ∧
      u ≤ 1 / 256 ∧ (n : ℝ) * ε ≤ 1 / 128 ∧
      4 * ε < 1 / 3 ∧ 24 * ε + 4 * n * ε + u * (1 + 4 * n * ε) < 2 * u := by
  let u := unitRoundoff p
  let ε := unitRoundoff (svdAuxiliaryPrecision k p)
  let κ : ℝ := svdKappa k
  have hu : 0 < u := unitRoundoff_pos _
  have he : 0 < ε := unitRoundoff_pos _
  have hκ : 1 ≤ κ := by
    unfold κ svdKappa
    exact_mod_cast (show 1 ≤ 2 ^ Nat.clog 2 k by exact Nat.one_le_pow _ _ (by decide))
  have hκ₀ : 0 < 1024 * κ := by positivity
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  change (n : ℝ) * u ≤ 1 / 128 at hguard
  have hup : u ≤ 1 / 256 := by nlinarith only [hguard, mul_le_mul_of_nonneg_right hn' hu.le]
  have hε : ε = u ^ 2 / (1024 * κ) := svd_unitRoundoff_auxiliary_eq k p
  have hnε : (n : ℝ) * ε ≤ u / (131072 * κ) := by
    rw [hε]
    calc
      _ = ((n : ℝ) * u * u) / (1024 * κ) := by ring
      _ ≤ ((1 / 128) * u) / (1024 * κ) := by gcongr
      _ = _ := by ring
  have hnε' : (n : ℝ) * ε ≤ u / 131072 := by
    refine hnε.trans ?_
    apply div_le_div_of_nonneg_left hu.le (by norm_num)
    linarith only [hκ]
  have he' : ε ≤ (n : ℝ) * ε := by
    nlinarith only [mul_le_mul_of_nonneg_right hn' he.le, he]
  have hmul : u * (4 * n * ε) ≤ (1 / 256) * (4 * n * ε) := by gcongr
  refine ⟨hnε, hup, ?_, ?_, ?_⟩
  · linarith only [hnε', hup]
  · linarith only [he', hnε', hup]
  · nlinarith only [he', hnε', hmul, hu]

/-- Binary rounding preserves the label order and the stated error budget. -/
theorem svd_rounded_labels {k p : ℕ} (hp : 2 ≤ p) (s : Fin k → ℝ)
    (hs : Monotone s) (hs₀ : ∀ j, 0 ≤ s j) (hs₁ : ∀ j, s j ≤ 3 / 4) :
    let μ := fun j => roundToEven p hp (s j)
    Monotone μ ∧ (∀ j, 0 ≤ μ j ∧ μ j < 1 ∧ |μ j - s j| ≤ unitRoundoff p) := by
  refine ⟨(roundToEven_monotone p hp).comp hs, fun j => ?_⟩
  have hμ₀ := roundToEven_monotone p hp (hs₀ j)
  have he := abs_roundToEven_sub_le p hp (s j)
  rw [abs_of_nonneg (hs₀ j)] at he
  have hub := unitRoundoff_le_quarter p hp
  have he' : |roundToEven p hp (s j) - s j| ≤ (1 / 4) * (3 / 4) := by
    calc
      _ ≤ unitRoundoff p * s j := he
      _ ≤ _ := mul_le_mul hub (hs₁ j) (hs₀ j) (by norm_num)
  have hj : s j ≤ 1 := by linarith only [hs₁ j]
  have hm := mul_le_mul_of_nonneg_left hj (unitRoundoff_pos p).le
  exact ⟨by simpa [roundToEven] using hμ₀, by linarith only [(abs_le.mp he').2, hs₁ j],
    he.trans (by simpa only [mul_one] using hm)⟩

private theorem svd_rescale_label_error {R μ s σ normB : ℝ} {k p : ℕ}
    (hR : 0 < R) (hscale : R < 8 * normB)
    (hμ : |μ - s| ≤ unitRoundoff p)
    (hs : |s - σ| ≤ unitRoundoff (svdAuxiliaryPrecision k p) / 64) :
    |R * μ - R * σ| < 16 * unitRoundoff p * normB := by
  let u := unitRoundoff p
  let ε := unitRoundoff (svdAuxiliaryPrecision k p)
  have hu : 0 < u := unitRoundoff_pos _
  have hε : ε ≤ u := by
    simp only [ε, u, unitRoundoff, _root_.zpow_neg, zpow_natCast]
    apply inv_anti₀ (by positivity)
    apply pow_le_pow_right₀ (by norm_num)
    unfold svdAuxiliaryPrecision
    omega
  rw [← mul_sub, abs_mul, abs_of_pos hR]
  have hσ : |μ - σ| ≤ u + ε / 64 := calc
    _ = |(μ - s) + (s - σ)| := by ring_nf
    _ ≤ |μ - s| + |s - σ| := abs_add_le ..
    _ ≤ _ := add_le_add hμ hs
  calc
    _ ≤ R * (u + ε / 64) := by gcongr
    _ < R * (2 * u) := by
      apply mul_lt_mul_of_pos_left _ hR
      linarith only [hε, hu]
    _ < _ := by nlinarith only [mul_lt_mul_of_pos_right hscale (show 0 < 2 * u by positivity)]

/-- Rescaling a pair of stored vectors and its label gives both original-scale
residual bounds. The label error estimate uses the exact scaled singular label. -/
theorem svd_rescaled_output_bounds {n : ℕ} (B C : Matrix (Fin n) (Fin n) ℝ)
    (xHat yHat : EuclideanSpace ℝ (Fin n)) {R μ s σ : ℝ} {k p : ℕ}
    (hB : B = R • C) (hR : 0 < R) (hscale : R < 8 * ‖B‖)
    (hμ : |μ - s| ≤ unitRoundoff p)
    (hs : |s - σ| ≤ unitRoundoff (svdAuxiliaryPrecision k p) / 64)
    (hL : ‖C.toEuclideanLin yHat - μ • xHat‖ ≤ 20 * unitRoundoff p)
    (hRt : ‖Cᵀ.toEuclideanLin xHat - μ • yHat‖ ≤ 20 * unitRoundoff p) :
    ‖B.toEuclideanLin yHat - (R * μ) • xHat‖ ≤ 160 * unitRoundoff p * ‖B‖ ∧
      ‖Bᵀ.toEuclideanLin xHat - (R * μ) • yHat‖ ≤ 160 * unitRoundoff p * ‖B‖ ∧
      |R * μ - R * σ| < 16 * unitRoundoff p * ‖B‖ := by
  let u := unitRoundoff p
  have hu : 0 < u := unitRoundoff_pos _
  have hbound : R * (20 * u) ≤ 160 * u * ‖B‖ := by
    have he := mul_le_mul_of_nonneg_right hscale.le (show 0 ≤ 20 * u by positivity)
    nlinarith only [he]
  have scaleResidual (A : Matrix (Fin n) (Fin n) ℝ)
      (x y : EuclideanSpace ℝ (Fin n)) :
      ‖(R • A).toEuclideanLin y - (R * μ) • x‖ =
        R * ‖A.toEuclideanLin y - μ • x‖ := by
    rw [map_smul, LinearMap.smul_apply, ← smul_smul, ← smul_sub, norm_smul,
      Real.norm_eq_abs, abs_of_pos hR]
  refine ⟨?_, ?_, ?_⟩
  · conv_lhs => rw [hB, scaleResidual]
    exact (mul_le_mul_of_nonneg_left hL hR.le).trans hbound
  · conv_lhs => rw [hB, Matrix.transpose_smul, scaleResidual]
    exact (mul_le_mul_of_nonneg_left hRt hR.le).trans hbound
  · exact svd_rescale_label_error hR hscale hμ hs

/-- The actual auxiliary and final rounding operations produce a column
within the source's twice-unit-roundoff budget. -/
theorem svd_computed_normalized_column {n k p : ℕ} (hp : 2 ≤ p) (hn : 2 ≤ n)
    (hguard : precisionGuard n p) {hq : 2 ≤ svdAuxiliaryPrecision k p}
    (x : Fin n → Word (svdAuxiliaryPrecision k p) hq)
    (z : EuclideanSpace ℝ (Fin n)) (hz : 1 / 3 ≤ ‖z‖)
    (hx : ‖Word.euclidean x - z‖ ≤ 4 * unitRoundoff (svdAuxiliaryPrecision k p)) :
    ∃ hne : Word.euclidean x ≠ 0,
      ‖Word.euclidean (Word.normalizeTo p hp x hne) - ‖z‖⁻¹ • z‖ < 2 * unitRoundoff p := by
  obtain ⟨_, _, he, he', hbudget⟩ := svd_normalization_roundoff_budget (k := k) hn hguard
  have hz' : 0 < ‖z‖ := by linarith only [hz]
  have hne : Word.euclidean x ≠ 0 := by
    intro h
    rw [h, zero_sub, norm_neg] at hx
    linarith only [hz, hx, he']
  refine ⟨hne, ?_⟩
  have h := Word.normalizeTo_error p hp x hne (norm_pos_iff.mp hz') (by omega) he
  have hdist : 2 * ‖Word.euclidean x - z‖ / ‖z‖ ≤ 24 * unitRoundoff (svdAuxiliaryPrecision k p) := by
    apply (div_le_iff₀ hz').2
    have hh := mul_le_mul_of_nonneg_left hz
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 24) (unitRoundoff_pos (svdAuxiliaryPrecision k p)).le)
    nlinarith only [hx, hh]
  exact h.trans_lt (lt_of_le_of_lt (by linarith only [hdist]) hbudget)

private theorem operatorNorm_le_sqrt_columns {n k : ℕ}
    (A : Matrix (Fin n) (Fin k) ℝ) {δ : ℝ} (hδ : 0 ≤ δ)
    (h : ∀ j, columnNorm A j ≤ δ) : ‖A‖ ≤ Real.sqrt k * δ := by
  change realMatrixOperatorNorm A ≤ _
  refine (realMatrixOperatorNorm_le_frobNormRect A).trans ?_
  apply (sq_le_sq₀ (Real.sqrt_nonneg _) (by positivity)).1
  change frobNormRect A ^ 2 ≤ _
  rw [frobNormRect_sq, mul_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
  unfold frobNormSqRect
  rw [Finset.sum_comm]
  calc
    _ = ∑ j, columnNorm A j ^ 2 := by
      simp [columnNorm, EuclideanSpace.norm_sq_eq, Real.norm_eq_abs, sq_abs]
    _ ≤ ∑ _j : Fin k, δ ^ 2 :=
      Finset.sum_le_sum (fun j _ => (sq_le_sq₀ (norm_nonneg _) hδ).2 (h j))
    _ = _ := by simp

private abbrev outputCol {n k : ℕ} (A : Matrix (Fin n) (Fin k) ℝ) (j : Fin k) :
    EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 (fun i => A i j)

private theorem output_gram_entry {n k : ℕ} (A : Matrix (Fin n) (Fin k) ℝ)
    (i j : Fin k) : (Aᵀ * A) i j = ⟪outputCol A i, outputCol A j⟫ := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, outputCol, PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro a _
  change A a i * A a j = A a j * A a i
  exact mul_comm _ _

/-- Perturbing unit columns by at most twice unit roundoff gives the source
norm, pairwise, array-error and operator Gram bounds for either parity array. -/
theorem svd_rounded_gram_bounds {n k : ℕ} (A Ahat : Matrix (Fin n) (Fin k) ℝ) {u : ℝ}
    (hk : 1 ≤ k) (hkn : k ≤ n) (hu : 0 < u) (huMax : u ≤ 1 / 256) (hnu : n * u ≤ 1 / 128)
    (hunit : ∀ j, columnNorm A j = 1)
    (hpair : ∀ i j, i ≠ j → |(Aᵀ * A) i j| ≤ 9 * u / 8)
    (hgram : ‖Aᵀ * A - 1‖ ≤ 9 * u / 4) (hA : ‖A‖ ≤ 1 + 9 * u / 8)
    (herr : ∀ j, columnNorm (Ahat - A) j ≤ 2 * u) :
    (∀ j, |columnNorm Ahat j - 1| ≤ 2 * u) ∧
      (∀ i j, i ≠ j → |(Ahatᵀ * Ahat) i j| ≤ 6 * u) ∧
      ‖Ahat - A‖ ≤ 2 * Real.sqrt k * u ∧
      ‖Ahatᵀ * Ahat - 1‖ < 7 * Real.sqrt k * u ∧
      7 * Real.sqrt k * u ≤ 7 / 128 := by
  let E := Ahat - A
  let w := Real.sqrt k * u
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hw' : 1 ≤ Real.sqrt (k : ℝ) := by simpa using Real.sqrt_le_sqrt hk'
  have huw : u ≤ w := by
    dsimp [w]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hw' hu.le
  have hw : 0 < w := hu.trans_le huw
  have hwm : w ≤ 1 / 128 := calc
    _ ≤ (k : ℝ) * u := by
      apply mul_le_mul_of_nonneg_right _ hu.le
      apply (sq_le_sq₀ (Real.sqrt_nonneg _) (Nat.cast_nonneg _)).1
      rw [Real.sq_sqrt (Nat.cast_nonneg _)]
      nlinarith only [mul_le_mul_of_nonneg_right hk' (Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
    _ ≤ (n : ℝ) * u := mul_le_mul_of_nonneg_right (by exact_mod_cast hkn) hu.le
    _ ≤ _ := hnu
  have hE : ‖E‖ ≤ 2 * w := (operatorNorm_le_sqrt_columns E (by positivity) herr).trans_eq (by
    dsimp [w]
    ring)
  have htr {m l : ℕ} (M : Matrix (Fin m) (Fin l) ℝ) : ‖Mᵀ‖ = ‖M‖ := by
    rw [← Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.l2_opNorm_conjTranspose]
  have hadd : Ahat = A + E := by dsimp [E]; abel
  have hcol (j : Fin k) : outputCol Ahat j = outputCol A j + outputCol E j := by
    ext i
    exact congrArg (fun Q : Matrix (Fin n) (Fin k) ℝ => Q i j) hadd
  refine ⟨?_, ?_, hE.trans_eq (by dsimp [w]; ring), ?_,
    by rw [mul_assoc]; change 7 * w ≤ _; linarith only [hwm]⟩
  · intro j
    have hsub : outputCol Ahat j - outputCol A j = outputCol E j := by
      rw [hcol, add_sub_cancel_left]
    change |‖outputCol Ahat j‖ - 1| ≤ 2 * u
    rw [← hunit j]
    exact (abs_norm_sub_norm_le _ _).trans (by rw [hsub]; exact herr j)
  · intro i j hij
    let a := ⟪outputCol A i, outputCol A j⟫
    let b := ⟪outputCol A i, outputCol E j⟫
    let c := ⟪outputCol E i, outputCol A j⟫
    let d := ⟪outputCol E i, outputCol E j⟫
    have h₁ : |b| ≤ columnNorm A i * columnNorm E j :=
      abs_real_inner_le_norm (outputCol A i) (outputCol E j)
    have h₂ : |c| ≤ columnNorm E i * columnNorm A j :=
      abs_real_inner_le_norm (outputCol E i) (outputCol A j)
    have h₃ : |d| ≤ columnNorm E i * columnNorm E j :=
      abs_real_inner_le_norm (outputCol E i) (outputCol E j)
    rw [hunit i, one_mul] at h₁
    rw [hunit j, mul_one] at h₂
    have h₄ : columnNorm E i * columnNorm E j ≤ (2 * u) * (2 * u) :=
      mul_le_mul (herr i) (herr j) (norm_nonneg _) (by positivity)
    have hb : |a| ≤ 9 * u / 8 := by
      dsimp only [a]
      rw [← output_gram_entry]
      exact hpair i j hij
    rw [output_gram_entry, hcol i, hcol j, inner_add_left, inner_add_right, inner_add_right]
    change |(a + b) + (c + d)| ≤ 6 * u
    have hquad : 4 * u ^ 2 ≤ (4 / 256) * u := by
      nlinarith only [mul_le_mul_of_nonneg_right huMax hu.le]
    linarith only [abs_add_le (a + b) (c + d), abs_add_le a b, abs_add_le c d,
      hb, h₁, h₂, h₃, h₄, hquad, herr i, herr j, hu]
  · have hsplit : Ahatᵀ * Ahat - 1 =
        (Aᵀ * A - 1) + Aᵀ * E + Eᵀ * A + Eᵀ * E := by
      rw [hadd]
      simp only [Matrix.transpose_add, Matrix.add_mul, Matrix.mul_add]
      abel
    have hcross : ‖Aᵀ * E‖ ≤ (1 + 9 * u / 8) * (2 * w) := calc
      _ ≤ ‖Aᵀ‖ * ‖E‖ := Matrix.l2_opNorm_mul ..
      _ ≤ _ := by rw [htr]; gcongr
    have hcross' : ‖Eᵀ * A‖ ≤ (1 + 9 * u / 8) * (2 * w) := by
      rw [← Matrix.transpose_transpose (Eᵀ * A), Matrix.transpose_mul,
        Matrix.transpose_transpose, htr]
      exact hcross
    have hself : ‖Eᵀ * E‖ ≤ (2 * w) * (2 * w) := calc
      _ ≤ ‖Eᵀ‖ * ‖E‖ := Matrix.l2_opNorm_mul ..
      _ ≤ _ := by rw [htr]; gcongr
    rw [hsplit]
    have huw' := mul_le_mul_of_nonneg_right huMax hw.le
    have hww := mul_le_mul_of_nonneg_right hwm hw.le
    rw [mul_assoc]
    change _ < 7 * w
    nlinarith only [hgram, hcross, hcross', hself, huw, huw', hww, hw,
      norm_add_le (Aᵀ * A - 1) (Aᵀ * E),
      norm_add_le ((Aᵀ * A - 1) + Aᵀ * E) (Eᵀ * A),
      norm_add_le ((Aᵀ * A - 1) + Aᵀ * E + Eᵀ * A) (Eᵀ * E)]

/-- With the raw Gram budget and raw storage error, normalizing the stored
parities at auxiliary precision and rounding them to output precision gives
the columnwise and operator estimates on the actual stored array. -/
theorem svd_computed_parity_array {n k p : ℕ} (hp : 2 ≤ p) (hn : 2 ≤ n)
    (hk : 1 ≤ k) (hkn : k ≤ n) (hguard : precisionGuard n p)
    {hq : 2 ≤ svdAuxiliaryPrecision k p}
    (X : Matrix (Fin n) (Fin k) ℝ) (d : Fin k → ℝ)
    (x : Fin k → Fin n → Word (svdAuxiliaryPrecision k p) hq)
    (hd : ∀ j, (1 / 4 : ℝ) ≤ d j)
    (hgram : ‖Xᵀ * X - diagonal d‖ ≤ unitRoundoff p / 8)
    (hx : ∀ j, ‖Word.euclidean (x j) - WithLp.toLp 2 (fun i => X i j)‖ ≤
      4 * unitRoundoff (svdAuxiliaryPrecision k p)) :
    ∃ hne : ∀ j, Word.euclidean (x j) ≠ 0,
      let A := normalizeColumns X
      let Ahat : Matrix (Fin n) (Fin k) ℝ :=
        fun i j => (Word.normalizeTo p hp (x j) (hne j) i).value
      let u := unitRoundoff p
      (∀ j, columnNorm (Ahat - A) j < 2 * u) ∧
      (∀ j, |columnNorm Ahat j - 1| ≤ 2 * u) ∧
      (∀ i j, i ≠ j → |(Ahatᵀ * Ahat) i j| ≤ 6 * u) ∧
      ‖Ahat - A‖ ≤ 2 * Real.sqrt k * u ∧
      ‖Ahatᵀ * Ahat - 1‖ < 7 * Real.sqrt k * u ∧
      7 * Real.sqrt k * u ≤ 7 / 128 := by
  let u := unitRoundoff p
  let A := normalizeColumns X
  have hu := (svd_normalization_roundoff_budget (k := k) hn hguard).2.1
  obtain ⟨hX, hdiag, hpair, hgram', hA⟩ := parity_normalized_gram_budgets X d u hu hd hgram
  choose hne he using fun j =>
    svd_computed_normalized_column hp hn hguard (x j) (outputCol X j) (hX j) (hx j)
  let Ahat : Matrix (Fin n) (Fin k) ℝ := fun i j => (Word.normalizeTo p hp (x j) (hne j) i).value
  refine ⟨hne, ?_⟩
  have he' (j : Fin k) : columnNorm (Ahat - A) j < 2 * u := by
    have hnormalized : outputCol A j = ‖outputCol X j‖⁻¹ • outputCol X j := by
      ext i
      simp [A, outputCol, normalizeColumns, columnNorm, Matrix.mul_diagonal, mul_comm]
    have hj := he j
    rw [← hnormalized] at hj
    exact hj
  have hnorm (j : Fin k) : columnNorm A j = 1 := by
    apply (sq_eq_sq₀ (norm_nonneg _) (by norm_num)).1
    change columnNorm A j ^ 2 = 1 ^ 2
    rw [one_pow, ← gram_diag]
    exact hdiag j
  exact ⟨he', svd_rounded_gram_bounds A Ahat hk hkn (unitRoundoff_pos p) hu hguard
    hnorm hpair hgram' hA (fun j => (he' j).le)⟩

/-- The computed normalizations and rounded label satisfy both coupled
residual bounds before and after the exact scaling. -/
theorem svd_computed_pair_residuals {n k p : ℕ} (hp : 2 ≤ p) (hn : 2 ≤ n)
    (hguard : precisionGuard n p) {hq : 2 ≤ svdAuxiliaryPrecision k p}
    (B C : Matrix (Fin n) (Fin n) ℝ)
    (x y : EuclideanSpace ℝ (Fin n)) (xRaw yRaw : Fin n → Word (svdAuxiliaryPrecision k p) hq)
    {s σ R : ℝ} (hR : 0 < R) (hB : B = R • C) (hscale : R < 8 * ‖B‖)
    (hC : ‖C‖ ≤ 1 / 2) (hs₀ : 0 ≤ s) (hs₁ : s ≤ 3 / 4)
    (hs : |s - σ| ≤ unitRoundoff (svdAuxiliaryPrecision k p) / 64)
    (hx : 1 / 3 ≤ ‖x‖) (hy : 1 / 3 ≤ ‖y‖)
    (hxRaw : ‖Word.euclidean xRaw - x‖ ≤ 4 * unitRoundoff (svdAuxiliaryPrecision k p))
    (hyRaw : ‖Word.euclidean yRaw - y‖ ≤ 4 * unitRoundoff (svdAuxiliaryPrecision k p))
    (hL : ‖C.toEuclideanLin (‖y‖⁻¹ • y) - s • (‖x‖⁻¹ • x)‖ ≤ 15 * unitRoundoff p)
    (hRt : ‖Cᵀ.toEuclideanLin (‖x‖⁻¹ • x) - s • (‖y‖⁻¹ • y)‖ ≤ 15 * unitRoundoff p) :
    ∃ (hx' : Word.euclidean xRaw ≠ 0) (hy' : Word.euclidean yRaw ≠ 0),
      let xHat := Word.euclidean (Word.normalizeTo p hp xRaw hx')
      let yHat := Word.euclidean (Word.normalizeTo p hp yRaw hy')
      let μ := roundToEven p hp s
      let u := unitRoundoff p
      ‖C.toEuclideanLin yHat - μ • xHat‖ ≤ 20 * u ∧
      ‖Cᵀ.toEuclideanLin xHat - μ • yHat‖ ≤ 20 * u ∧
      ‖B.toEuclideanLin yHat - (R * μ) • xHat‖ ≤ 160 * u * ‖B‖ ∧
      ‖Bᵀ.toEuclideanLin xHat - (R * μ) • yHat‖ ≤ 160 * u * ‖B‖ ∧
      |R * μ - R * σ| < 16 * u * ‖B‖ := by
  obtain ⟨hx', hxErr⟩ := svd_computed_normalized_column hp hn hguard xRaw x hx hxRaw
  obtain ⟨hy', hyErr⟩ := svd_computed_normalized_column hp hn hguard yRaw y hy hyRaw
  let xHat := Word.euclidean (Word.normalizeTo p hp xRaw hx')
  let yHat := Word.euclidean (Word.normalizeTo p hp yRaw hy')
  have unit_of_floor (v : EuclideanSpace ℝ (Fin n)) (hv : 1 / 3 ≤ ‖v‖) :
      ‖‖v‖⁻¹ • v‖ = 1 := by
    have hpos : 0 < ‖v‖ := by linarith only [hv]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hpos), inv_mul_cancel₀ hpos.ne']
  obtain ⟨hμ₀, hμ₁, hμ⟩ :=
    (svd_rounded_labels (k := 1) hp (fun _ => s) monotone_const (fun _ => hs₀)
      (fun _ => hs₁)).2 0
  have he := svd_rounded_residuals C (‖x‖⁻¹ • x) (‖y‖⁻¹ • y) xHat yHat
    hC (unit_of_floor x hx) (unit_of_floor y hy) hμ₀ hμ₁.le hμ hxErr.le hyErr.le hL hRt
  exact ⟨hx', hy', he.1, he.2, svd_rescaled_output_bounds B C xHat yHat hB hR hscale hμ hs he.1 he.2⟩

private theorem ascending_spectrum_scale {n : ℕ} (C : Matrix (Fin n) (Fin n) ℝ)
    {R : ℝ} (hR : 0 ≤ R) :
    ascendingRealSpectrum (R • C) = fun i => R * ascendingRealSpectrum C i := by
  obtain ⟨U, V, hm, hn, hC⟩ := exists_orthonormalBases_ascendingRealSpectrum C
  let t := fun i => R * ascendingRealSpectrum C i
  have ht : Monotone t := fun _ _ hij => mul_le_mul_of_nonneg_left (hm hij) hR
  have ht₀ : ∀ i, 0 ≤ t i := fun i => mul_nonneg hR (hn i)
  have htA : R • C = orthonormalBasisMatrix U * diagonal t * (orthonormalBasisMatrix V)ᵀ := by
    calc
      R • C = R • (orthonormalBasisMatrix U * diagonal (ascendingRealSpectrum C) *
          (orthonormalBasisMatrix V)ᵀ) := congrArg (R • ·) hC
      _ = _ := by
        change _ = orthonormalBasisMatrix U * diagonal (R • ascendingRealSpectrum C) *
          (orthonormalBasisMatrix V)ᵀ
        rw [Matrix.diagonal_smul, Matrix.mul_smul, Matrix.smul_mul]
  have hEq := multiset_ascendingRealSpectrum_of_orthogonal_factorization _
    (orthonormalBasisMatrix U) (orthonormalBasisMatrix V) t
    (orthonormalBasisMatrix_transpose_mul_self U)
    (orthonormalBasisMatrix_transpose_mul_self V) ht₀ htA
  have hp : (List.ofFn (ascendingRealSpectrum (R • C))).Perm (List.ofFn t) := by
    apply Multiset.coe_eq_coe.mp
    simpa only [Fin.univ_val_map] using hEq
  obtain ⟨_, _, hm', _, _⟩ := exists_orthonormalBases_ascendingRealSpectrum (R • C)
  exact List.ofFn_inj.mp (hp.eq_of_pairwise' hm'.sortedLE_ofFn.pairwise ht.sortedLE_ofFn.pairwise)

private theorem ascending_spectrum_le_norm {n : ℕ} (C : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) :
    ascendingRealSpectrum C i ≤ ‖C‖ := by
  obtain ⟨U, V, _, hn, hC⟩ := exists_orthonormalBases_ascendingRealSpectrum C
  let U₀ := orthonormalBasisMatrix U
  let V₀ := orthonormalBasisMatrix V
  have hD : diagonal (ascendingRealSpectrum C) = U₀ᵀ * C * V₀ := by
    calc
      _ = (U₀ᵀ * U₀) * diagonal (ascendingRealSpectrum C) * (V₀ᵀ * V₀) := by
        simp [U₀, V₀, orthonormalBasisMatrix_transpose_mul_self]
      _ = _ := by
        conv_rhs => rw [hC]
        simp only [U₀, V₀, Matrix.mul_assoc]
  have hU : ‖U₀ᵀ‖ ≤ 1 :=
    Matrix.Bipartite.MassParityGrams.norm_le_one_of_orthonormal _
      (by simpa [U₀] using orthonormalBasisMatrix_mul_transpose U)
  have hV : ‖V₀‖ ≤ 1 :=
    Matrix.Bipartite.MassParityGrams.norm_le_one_of_orthonormal _
      (orthonormalBasisMatrix_transpose_mul_self V)
  have hentry := NormalizedGram.abs_apply_le_norm (diagonal (ascendingRealSpectrum C)) i i
  rw [Matrix.diagonal_apply_eq, abs_of_nonneg (hn i), hD] at hentry
  calc
    _ ≤ ‖U₀ᵀ * C * V₀‖ := hentry
    _ ≤ ‖U₀ᵀ‖ * ‖C‖ * ‖V₀‖ := by
      grw [Matrix.l2_opNorm_mul, Matrix.l2_opNorm_mul]
    _ ≤ 1 * ‖C‖ * 1 := by gcongr
    _ = _ := by ring

/-- The original-scale value bound compares the reported label to the
canonical singular value at the same requested index. -/
theorem svd_rescaled_indexed_label_error {n k p : ℕ} (hp : 2 ≤ p)
    (B C : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) {R s : ℝ}
    (hB : B = R • C) (hR : 0 < R) (hscale : R < 8 * ‖B‖)
    (hC : ‖C‖ ≤ 1 / 2) (hs₀ : 0 ≤ s)
    (hs : |s - ascendingRealSpectrum C i| ≤ unitRoundoff (svdAuxiliaryPrecision k p) / 64) :
    |R * roundToEven p hp s - ascendingRealSpectrum B i| < 16 * unitRoundoff p * ‖B‖ := by
  have hε : unitRoundoff (svdAuxiliaryPrecision k p) ≤ unitRoundoff p := by
    simp only [unitRoundoff, _root_.zpow_neg, zpow_natCast]
    apply inv_anti₀ (by positivity)
    apply pow_le_pow_right₀ (by norm_num)
    unfold svdAuxiliaryPrecision
    omega
  have hs' : s ≤ 3 / 4 := by
    linarith only [(abs_le.mp hs).2, ascending_spectrum_le_norm C i, hC, hε,
      unitRoundoff_le_quarter p hp]
  obtain ⟨_, _, hμ⟩ :=
    (svd_rounded_labels (k := 1) hp (fun _ => s) monotone_const
      (fun _ => hs₀) (fun _ => hs')).2 0
  have hσ : ascendingRealSpectrum B i = R * ascendingRealSpectrum C i := by
    rw [hB, ascending_spectrum_scale C hR.le]
  rw [hσ]
  exact svd_rescale_label_error hR hscale hμ hs

end
end NumStability.CertifiedTridiagonalEigenpairs
