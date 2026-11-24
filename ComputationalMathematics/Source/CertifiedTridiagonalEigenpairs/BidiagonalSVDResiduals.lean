import ComputationalMathematics.Source.CertifiedTridiagonalEigenpairs.ParityGrams
import ComputationalMathematics.Analysis.MatrixStructure.Bipartite.MassParityGrams
import ComputationalMathematics.Analysis.MatrixInequalities.NormalizedGram
import ComputationalMathematics.Analysis.MatrixStructure.Bipartite.MassShiftSpectral
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Tactic

/-!
# Coupled residuals of mass-shifted singular vectors

Section 8 of the certified tridiagonal eigenpair paper normalizes the two
parities of its selected signed eigenvectors and pairs them at a common
singular-value label.
-/

open Matrix
open scoped Matrix.Norms.L2Operator

namespace NumStability.CertifiedTridiagonalEigenpairs

open Matrix.Bipartite

noncomputable section

private def unitVector {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) :=
  ‖x‖⁻¹ • x

private theorem unitVector_norm {n : ℕ} {x : EuclideanSpace ℝ (Fin n)}
    (hx : 0 < ‖x‖) : ‖unitVector x‖ = 1 := by
  rw [unitVector, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hx), inv_mul_cancel₀ hx.ne']

private theorem massMagnitude_le_add {α s : ℝ} (hα : 0 < α) (hs : 0 ≤ s) :
    massMagnitude α s ≤ α + s := by
  apply (sq_le_sq₀ (massMagnitude_nonneg _ _) (by positivity)).1
  rw [massMagnitude_sq]
  nlinarith only [mul_nonneg hα.le hs]

private theorem norm_ideal_error {l l₀ u : ℝ}
    (hl : 1 / 3 ≤ l) (hl₀ : 1 / 2 ≤ l₀) (h : |l ^ 2 - l₀ ^ 2| ≤ u / 8) :
    |l - l₀| ≤ u / 4 := by
  have hb : (1 / 2 : ℝ) ≤ l + l₀ := by linarith
  have he : |l ^ 2 - l₀ ^ 2| = |l - l₀| * (l + l₀) := by
    rw [show l ^ 2 - l₀ ^ 2 = (l - l₀) * (l + l₀) by ring, abs_mul,
      abs_of_nonneg (by linarith : 0 ≤ l + l₀)]
  rw [he] at h
  linarith only [h, mul_le_mul_of_nonneg_left hb (abs_nonneg (l - l₀))]

private theorem ratio_error {l r l₀ r₀ u : ℝ}
    (hr : 1 / 3 ≤ r) (hl₀ : 0 ≤ l₀) (hl₁ : l₀ ≤ 1) (hr₀ : 1 / 2 ≤ r₀)
    (hl : |l - l₀| ≤ u / 4) (he : |r - r₀| ≤ u / 4) :
    |l / r - l₀ / r₀| ≤ 3 * u := by
  have hrp : 0 < r := by linarith
  have hr₀p : 0 < r₀ := by linarith
  have hi : r⁻¹ ≤ 3 := by
    rw [← one_div, div_le_iff₀ hrp]
    linarith
  have hi₀ : r₀⁻¹ ≤ 2 := by
    rw [← one_div, div_le_iff₀ hr₀p]
    linarith
  have hu : 0 ≤ u / 4 := (abs_nonneg _).trans hl
  have hsplit : l / r - l₀ / r₀ = (l - l₀) / r + l₀ * ((r₀ - r) / r / r₀) := by
    field_simp
    ring
  rw [hsplit]
  calc
    _ ≤ |(l - l₀) / r| + |l₀ * ((r₀ - r) / r / r₀)| := abs_add_le ..
    _ = |l - l₀| * r⁻¹ + l₀ * (|r - r₀| * r⁻¹ * r₀⁻¹) := by
      rw [abs_mul, abs_div, abs_div, abs_div, abs_of_nonneg hl₀,
        abs_of_pos hrp, abs_of_pos hr₀p, abs_sub_comm r₀ r]
      simp only [div_eq_mul_inv]
    _ ≤ (u / 4) * 3 + 1 * ((u / 4) * 3 * 2) := by gcongr
    _ ≤ _ := by linarith only [(abs_nonneg (l - l₀)).trans hl]

private theorem high_ideal_ratio {α s : ℝ} (hα : 0 < α) (hs : 2 * α ≤ s) :
    let a := massMagnitude α s
    let l₀ := Real.sqrt ((1 + α / a) / 2)
    let r₀ := Real.sqrt ((1 - α / a) / 2)
    1 / 2 ≤ l₀ ∧ l₀ ≤ 1 ∧ 1 / 2 ≤ r₀ ∧ r₀ ≤ 1 ∧
      (a - α) * (l₀ / r₀) = s ∧ (a + α) * (r₀ / l₀) = s := by
  dsimp only
  let a := massMagnitude α s
  let l := Real.sqrt ((1 + α / a) / 2)
  let r := Real.sqrt ((1 - α / a) / 2)
  change 1 / 2 ≤ l ∧ l ≤ 1 ∧ 1 / 2 ≤ r ∧ r ≤ 1 ∧
    (a - α) * (l / r) = s ∧ (a + α) * (r / l) = s
  have ha : 0 < a := hα.trans_le (le_massMagnitude hα.le s)
  have hs₀ : 0 ≤ s := by linarith
  have hsa : s ≤ a := (sq_le_sq₀ hs₀ ha.le).1 (by
    dsimp [a]; rw [massMagnitude_sq]; linarith only [sq_nonneg α])
  have had : α / a ≤ 1 / 2 := (div_le_iff₀ ha).2 (by linarith)
  have had₀ : 0 ≤ α / a := div_nonneg hα.le ha.le
  have hl : l ^ 2 = (1 + α / a) / 2 := Real.sq_sqrt (by linarith)
  have hr : r ^ 2 = (1 - α / a) / 2 := Real.sq_sqrt (by linarith)
  have hl₀ : 0 ≤ l := Real.sqrt_nonneg _
  have hr₀ : 0 ≤ r := Real.sqrt_nonneg _
  have hlf : 1 / 2 ≤ l := (sq_le_sq₀ (by norm_num) hl₀).1 (by linarith)
  have hrf : 1 / 2 ≤ r := (sq_le_sq₀ (by norm_num) hr₀).1 (by linarith)
  have hlp : 0 < l := by linarith
  have hrp : 0 < r := by linarith
  have hmass : (a - α) * (a + α) = s ^ 2 := by
    dsimp [a]; nlinarith only [massMagnitude_sq α s]
  have hab : (a - α) * l ^ 2 = (a + α) * r ^ 2 := by
    rw [hl, hr]
    field_simp
  refine ⟨hlf, (sq_le_sq₀ hl₀ (by norm_num)).1 (by linarith),
    hrf, (sq_le_sq₀ hr₀ (by norm_num)).1 (by linarith), ?_, ?_⟩
  · apply (sq_eq_sq₀ (mul_nonneg (sub_nonneg.mpr (le_massMagnitude hα.le s))
      (div_nonneg hl₀ hr₀)) hs₀).1
    field_simp
    nlinarith only [congrArg ((a - α) * ·) hab, congrArg (· * r ^ 2) hmass]
  · apply (sq_eq_sq₀ (by positivity : 0 ≤ (a + α) * (r / l)) hs₀).1
    field_simp
    nlinarith only [congrArg ((a + α) * ·) hab, congrArg (· * l ^ 2) hmass]

private theorem high_normalize_one {n : ℕ} (T : EuclideanSpace ℝ (Fin n) →ₗ[ℝ]
    EuclideanSpace ℝ (Fin n)) (x y : EuclideanSpace ℝ (Fin n)) {b s η u l₀ r₀ : ℝ}
    (hb : 0 ≤ b) (hb₁ : b ≤ 1) (hη : η < u / 3)
    (hx : 1 / 3 ≤ ‖x‖) (hy : 1 / 3 ≤ ‖y‖)
    (hl₀ : 1 / 2 ≤ l₀) (hl₁ : l₀ ≤ 1) (hr₀ : 1 / 2 ≤ r₀)
    (hl : |‖x‖ ^ 2 - l₀ ^ 2| ≤ u / 8) (hr : |‖y‖ ^ 2 - r₀ ^ 2| ≤ u / 8)
    (hs : b * (l₀ / r₀) = s) (he : ‖T y - b • x‖ ≤ η) :
    ‖T (unitVector y) - s • unitVector x‖ < 4 * u := by
  have hxp : 0 < ‖x‖ := by linarith
  have hyp : 0 < ‖y‖ := by linarith
  have hratio := ratio_error hy (by linarith) hl₁ hr₀
    (norm_ideal_error hx hl₀ hl) (norm_ideal_error hy hr₀ hr)
  have hi : ‖y‖⁻¹ ≤ 3 := by rw [← one_div, div_le_iff₀ hyp]; linarith
  have hsplit : T (unitVector y) - s • unitVector x =
      ‖y‖⁻¹ • (T y - b • x) + (b * (‖x‖ / ‖y‖) - s) • unitVector x := by
    simp only [unitVector, map_smul, smul_sub, smul_smul, sub_mul, sub_smul]
    have h : b * (‖x‖ / ‖y‖) * ‖x‖⁻¹ = ‖y‖⁻¹ * b := by field_simp
    rw [h]
    abel
  rw [hsplit]
  calc
    _ ≤ ‖‖y‖⁻¹ • (T y - b • x)‖ +
        ‖(b * (‖x‖ / ‖y‖) - s) • unitVector x‖ := norm_add_le ..
    _ = ‖y‖⁻¹ * ‖T y - b • x‖ + b * |‖x‖ / ‖y‖ - l₀ / r₀| := by
      rw [norm_smul, norm_smul, unitVector_norm hxp, mul_one, Real.norm_eq_abs,
        Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hyp), ← hs, ← mul_sub, abs_mul,
        abs_of_nonneg hb]
    _ ≤ 3 * η + 1 * (3 * u) := by gcongr
    _ < _ := by linarith

private theorem low_normalize_one {n : ℕ} (T : EuclideanSpace ℝ (Fin n) →ₗ[ℝ]
    EuclideanSpace ℝ (Fin n)) (x y z : EuclideanSpace ℝ (Fin n)) {b s η u : ℝ}
    (hb : |b| ≤ 4 * u) (hs : 0 ≤ s) (hsu : s ≤ 2 * u) (hη : η < u / 3)
    (hx : 1 / 3 ≤ ‖x‖) (hy : 1 / 3 ≤ ‖y‖) (hz : ‖z‖ ≤ 1)
    (he : ‖T y - b • z‖ ≤ η) : ‖T (unitVector y) - s • unitVector x‖ < 15 * u := by
  have hxp : 0 < ‖x‖ := by linarith
  have hyp : 0 < ‖y‖ := by linarith
  have hi : ‖y‖⁻¹ ≤ 3 := by rw [← one_div, div_le_iff₀ hyp]; linarith
  have hu : 0 ≤ 4 * u := (abs_nonneg _).trans hb
  have ht : ‖T y‖ ≤ η + 4 * u := calc
    _ = ‖(T y - b • z) + b • z‖ := by rw [sub_add_cancel]
    _ ≤ ‖T y - b • z‖ + ‖b • z‖ := norm_add_le ..
    _ = ‖T y - b • z‖ + |b| * ‖z‖ := by rw [norm_smul, Real.norm_eq_abs]
    _ ≤ η + 4 * u * 1 := by gcongr
    _ = _ := by ring
  calc
    _ ≤ ‖T (unitVector y)‖ + ‖s • unitVector x‖ := norm_sub_le ..
    _ = ‖y‖⁻¹ * ‖T y‖ + s := by
      rw [show T (unitVector y) = ‖y‖⁻¹ • T y by simp [unitVector], norm_smul,
        norm_smul, unitVector_norm hxp, mul_one, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_pos (inv_pos.mpr hyp), abs_of_nonneg hs]
    _ ≤ 3 * (η + 4 * u) + 2 * u := by gcongr
    _ < _ := by linarith

/-- Both residuals of a high pair use the two parities of the same positive
column and the ideal norm ratios at its assigned singular-value label. -/
theorem svd_high_normalized_residuals {n : ℕ} (C : Matrix (Fin n) (Fin n) ℝ)
    (x y : EuclideanSpace ℝ (Fin n)) {α s u η : ℝ}
    (hα : 0 < α) (hs : 2 * α ≤ s) (ha : massMagnitude α s + α ≤ 1)
    (hη : η < u / 3) (hx : 1 / 3 ≤ ‖x‖) (hy : 1 / 3 ≤ ‖y‖)
    (hl : |‖x‖ ^ 2 - (1 + α / massMagnitude α s) / 2| ≤ u / 8)
    (hr : |‖y‖ ^ 2 - (1 - α / massMagnitude α s) / 2| ≤ u / 8)
    (hL : ‖C.toEuclideanLin y - (massMagnitude α s - α) • x‖ ≤ η)
    (hR : ‖Cᵀ.toEuclideanLin x - (massMagnitude α s + α) • y‖ ≤ η) :
    ‖C.toEuclideanLin (‖y‖⁻¹ • y) - s • (‖x‖⁻¹ • x)‖ < 4 * u ∧
      ‖Cᵀ.toEuclideanLin (‖x‖⁻¹ • x) - s • (‖y‖⁻¹ • y)‖ < 4 * u := by
  let a := massMagnitude α s
  let l₀ := Real.sqrt ((1 + α / a) / 2)
  let r₀ := Real.sqrt ((1 - α / a) / 2)
  have hal : α ≤ a := le_massMagnitude hα.le s
  have had : 0 ≤ α / a := div_nonneg hα.le (hα.le.trans hal)
  have had₁ : α / a ≤ 1 := (div_le_one (hα.trans_le hal)).2 hal
  have hl₀ : l₀ ^ 2 = (1 + α / a) / 2 := Real.sq_sqrt (by linarith)
  have hr₀ : r₀ ^ 2 = (1 - α / a) / 2 := Real.sq_sqrt (by linarith)
  have hl' : |‖x‖ ^ 2 - l₀ ^ 2| ≤ u / 8 := by rwa [hl₀]
  have hr' : |‖y‖ ^ 2 - r₀ ^ 2| ≤ u / 8 := by rwa [hr₀]
  obtain ⟨hll, hlu, hrl, hru, hrL, hrR⟩ := high_ideal_ratio hα hs
  exact ⟨high_normalize_one C.toEuclideanLin x y (sub_nonneg.mpr hal)
      (by linarith only [ha, hα]) hη hx hy hll hlu hrl
      hl' hr' hrL hL,
    high_normalize_one Cᵀ.toEuclideanLin y x (by linarith only [hal, hα])
      ha hη hy hx hrl hru hll
      hr' hl' hrR hR⟩

/-- Both residuals of a low pair combine the positive column's left parity
with the negative column's right parity. The other two parities only enter
through the signed eigenvector equations and a unit upper bound. -/
theorem svd_low_normalized_residuals {n : ℕ} (C : Matrix (Fin n) (Fin n) ℝ)
    (x y xNeg yPos : EuclideanSpace ℝ (Fin n)) {α s u η : ℝ}
    (hα : 0 < α) (hαu : α ≤ u) (hs : 0 ≤ s) (hsu : s ≤ 2 * u)
    (hη : η < u / 3) (hx : 1 / 3 ≤ ‖x‖) (hy : 1 / 3 ≤ ‖y‖)
    (hxNeg : ‖xNeg‖ ≤ 1) (hyPos : ‖yPos‖ ≤ 1)
    (hL : ‖C.toEuclideanLin y - (-massMagnitude α s - α) • xNeg‖ ≤ η)
    (hR : ‖Cᵀ.toEuclideanLin x - (massMagnitude α s + α) • yPos‖ ≤ η) :
    ‖C.toEuclideanLin (‖y‖⁻¹ • y) - s • (‖x‖⁻¹ • x)‖ < 15 * u ∧
      ‖Cᵀ.toEuclideanLin (‖x‖⁻¹ • x) - s • (‖y‖⁻¹ • y)‖ < 15 * u := by
  have ha := massMagnitude_nonneg α s
  have hb : massMagnitude α s + α ≤ 4 * u := by
    linarith only [massMagnitude_le_add hα hs, hαu, hsu]
  exact ⟨low_normalize_one C.toEuclideanLin x y xNeg
      (by rw [abs_of_nonpos (by linarith only [ha, hα])]; linarith only [hb])
      hs hsu hη hx hy hxNeg hL,
    low_normalize_one Cᵀ.toEuclideanLin y x yPos
      (by rwa [abs_of_nonneg (by linarith only [ha, hα])])
      hs hsu hη hy hx hyPos hR⟩

private theorem rounded_residual_one {n : ℕ} (C : Matrix (Fin n) (Fin n) ℝ)
    (x y xHat yHat : EuclideanSpace ℝ (Fin n)) {s μ u : ℝ}
    (hC : ‖C‖ ≤ 1 / 2) (hx : ‖x‖ = 1)
    (hμ : 0 ≤ μ) (hμ₁ : μ ≤ 1) (hs : |μ - s| ≤ u)
    (hxHat : ‖xHat - x‖ ≤ 2 * u) (hyHat : ‖yHat - y‖ ≤ 2 * u)
    (hres : ‖C.toEuclideanLin y - s • x‖ ≤ 15 * u) :
    ‖C.toEuclideanLin yHat - μ • xHat‖ ≤ 20 * u := by
  have hu : 0 ≤ u := (abs_nonneg _).trans hs
  have hCerr : ‖C.toEuclideanLin (yHat - y)‖ ≤ u := calc
    _ ≤ ‖C‖ * ‖yHat - y‖ := Matrix.l2_opNorm_mulVec _ _
    _ ≤ (1 / 2) * (2 * u) := by gcongr
    _ = _ := by ring
  have hμerr : ‖μ • (xHat - x)‖ ≤ 2 * u := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hμ]
    calc
      _ ≤ 1 * (2 * u) := by gcongr
      _ = _ := one_mul _
  have hserr : ‖(μ - s) • x‖ ≤ u := by
    simpa only [norm_smul, Real.norm_eq_abs, hx, mul_one] using hs
  have heq : C.toEuclideanLin yHat - μ • xHat =
      (C.toEuclideanLin y - s • x) + C.toEuclideanLin (yHat - y) -
        μ • (xHat - x) - (μ - s) • x := by
    simp only [map_sub, smul_sub, sub_smul]
    abel
  rw [heq]
  calc
    _ ≤ ‖(C.toEuclideanLin y - s • x) + C.toEuclideanLin (yHat - y) -
        μ • (xHat - x)‖ + ‖(μ - s) • x‖ := norm_sub_le ..
    _ ≤ (‖(C.toEuclideanLin y - s • x) + C.toEuclideanLin (yHat - y)‖ +
        ‖μ • (xHat - x)‖) + ‖(μ - s) • x‖ := by
      gcongr; exact norm_sub_le ..
    _ ≤ ((‖C.toEuclideanLin y - s • x‖ + ‖C.toEuclideanLin (yHat - y)‖) +
        ‖μ • (xHat - x)‖) + ‖(μ - s) • x‖ := by
      gcongr; exact norm_add_le ..
    _ ≤ _ := by linarith only [hres, hCerr, hμerr, hserr, hu]

/-- The same rounded pair satisfies the two coupled residual bounds at the
same stored label before rescaling. -/
theorem svd_rounded_residuals {n : ℕ} (C : Matrix (Fin n) (Fin n) ℝ)
    (x y xHat yHat : EuclideanSpace ℝ (Fin n)) {s μ u : ℝ}
    (hC : ‖C‖ ≤ 1 / 2) (hx : ‖x‖ = 1) (hy : ‖y‖ = 1)
    (hμ : 0 ≤ μ) (hμ₁ : μ ≤ 1) (hs : |μ - s| ≤ u)
    (hxHat : ‖xHat - x‖ ≤ 2 * u) (hyHat : ‖yHat - y‖ ≤ 2 * u)
    (hL : ‖C.toEuclideanLin y - s • x‖ ≤ 15 * u)
    (hR : ‖Cᵀ.toEuclideanLin x - s • y‖ ≤ 15 * u) :
    ‖C.toEuclideanLin yHat - μ • xHat‖ ≤ 20 * u ∧
      ‖Cᵀ.toEuclideanLin xHat - μ • yHat‖ ≤ 20 * u := by
  have hCt : ‖Cᵀ‖ ≤ 1 / 2 := by
    rw [← Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.l2_opNorm_conjTranspose]
    exact hC
  exact ⟨rounded_residual_one C x y xHat yHat hC hx hμ hμ₁ hs hxHat hyHat hL,
    rounded_residual_one Cᵀ y x yHat xHat hCt hy hμ hμ₁ hs hyHat hxHat hR⟩

open Matrix.Bipartite.MassParityGrams NormalizedGram

private abbrev col {m ι : Type*} (Q : Matrix m ι ℝ) (j : ι) :
    EuclideanSpace ℝ m := WithLp.toLp 2 (fun i => Q i j)

private theorem column_le_operatorNorm {m ι : Type*} [Fintype m] [Fintype ι] [DecidableEq ι]
    (Q : Matrix m ι ℝ) (j : ι) : ‖col Q j‖ ≤ ‖Q‖ := by
  let e : EuclideanSpace ℝ ι := EuclideanSpace.single j 1
  simpa [e, col, Matrix.toLpLin_apply, Matrix.mulVec_single] using
    Matrix.l2_opNorm_mulVec Q e

private theorem normalizeColumns_col {m ι : Type*} [Fintype m] [Fintype ι] [DecidableEq ι]
    (Q : Matrix m ι ℝ) (j : ι) :
    col (normalizeColumns Q) j = (‖col Q j‖)⁻¹ • col Q j := by
  ext i
  simp [Matrix.mul_diagonal, col, normalizeColumns, columnNorm, mul_comm]

private theorem massShift_col_parity {n r : ℕ} (C : Matrix (Fin n) (Fin n) ℝ)
    (W : Matrix (Fin n ⊕ Fin n) (Fin r) ℝ) (d : Fin r → ℝ) (α : ℝ) (j : Fin r) :
    let E := massShift C α * W - W * diagonal d
    let x := col (left W) j
    let y := col (right W) j
    col (left E) j = C.toEuclideanLin y - (d j - α) • x ∧
      col (right E) j = Cᵀ.toEuclideanLin x - (d j + α) • y := by
  have hblk : massShift C α = fromBlocks (α • 1) C Cᵀ (-(α • 1)) := by
    ext (i | i) (j | j) <;> simp [massShift, embedding, signature]
  have hm (i : Fin n ⊕ Fin n) :
      (massShift C α * W) i j = (massShift C α *ᵥ (fun t => W t j)) i := rfl
  dsimp only
  constructor <;> ext i
  · simp only [col, left, right, Matrix.toRows₁_apply,
      Matrix.sub_apply, Matrix.mul_diagonal, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul,
      Matrix.toLpLin_apply, Matrix.toRows₂_apply]
    rw [hm, hblk, Matrix.fromBlocks_mulVec]
    simp [Matrix.neg_mulVec, Matrix.smul_mulVec, Function.comp_def]
    ring
  · simp only [col, left, right, Matrix.toRows₂_apply,
      Matrix.sub_apply, Matrix.mul_diagonal, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul,
      Matrix.toLpLin_apply, Matrix.toRows₁_apply]
    rw [hm, hblk, Matrix.fromBlocks_mulVec]
    simp [Matrix.neg_mulVec, Matrix.smul_mulVec, Function.comp_def]
    ring

/-- The assigned-label residual of a common witness bounds both projected
equations at each actual signed column. -/
theorem svd_assigned_parity_residuals {n r : ℕ} (C : Matrix (Fin n) (Fin n) ℝ)
    (W : Matrix (Fin n ⊕ Fin n) (Fin r) ℝ) (d : Fin r → ℝ) (α η : ℝ) (j : Fin r)
    (hE : ‖massShift C α * W - W * diagonal d‖ ≤ η) :
    let x : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 (fun i => W (Sum.inl i) j)
    let y : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 (fun i => W (Sum.inr i) j)
    ‖C.toEuclideanLin y - (d j - α) • x‖ ≤ η ∧
      ‖Cᵀ.toEuclideanLin x - (d j + α) • y‖ ≤ η := by
  let E := massShift C α * W - W * diagonal d
  obtain ⟨hL, hR⟩ := massShift_col_parity C W d α j
  change ‖C.toEuclideanLin (col (right W) j) - (d j - α) • col (left W) j‖ ≤ η ∧
    ‖Cᵀ.toEuclideanLin (col (left W) j) - (d j + α) • col (right W) j‖ ≤ η
  rw [← hL, ← hR]
  exact ⟨(column_le_operatorNorm (left E) j).trans ((parity_norm_le E).1.trans hE),
    (column_le_operatorNorm (right E) j).trans ((parity_norm_le E).2.trans hE)⟩

private theorem gram_column_deviation {m ι : Type*} [Fintype m] [Fintype ι] [DecidableEq ι]
    (Q : Matrix m ι ℝ) (d : ι → ℝ) {δ : ℝ} (h : ‖Qᵀ * Q - diagonal d‖ ≤ δ)
    (j : ι) : |‖col Q j‖ ^ 2 - d j| ≤ δ := by
  have he := (abs_apply_le_norm (Qᵀ * Q - diagonal d) j j).trans h
  simpa only [Matrix.sub_apply, Matrix.diagonal_apply_eq, gram_diag] using he

/-- Exact coupled residuals of the normalized parities of one assigned-label
witness. The right columns use the same positive witness columns in the high
group and the corresponding negative columns in the low group. -/
theorem svd_normalized_residuals_of_witness {n r h l : ℕ}
    (C : Matrix (Fin n) (Fin n) ℝ) (W : Matrix (Fin n ⊕ Fin n) (Fin r) ℝ)
    (d : Fin r → ℝ) (eP : (Fin h ⊕ Fin l) ↪ Fin r) (eL : Fin l ↪ Fin r)
    (s : Fin h ⊕ Fin l → ℝ) {α u η cut : ℝ}
    (hα : 0 < α) (hαu : α ≤ u) (hu : u ≤ 1 / 256) (hη : 0 ≤ η)
    (hbudget : η / α = u / 16) (hcut : α ≤ cut) (hcutu : cut ≤ 2 * u)
    (hsH : ∀ i, cut + α ≤ s (.inl i)) (hs : ∀ j, 0 ≤ s j)
    (hsL : ∀ j, s (.inr j) ≤ cut) (hsMax : ∀ j, s j ≤ 3 / 4)
    (hW : Wᵀ * W = 1)
    (hdP : ∀ j, d (eP j) = massMagnitude α (s j))
    (hdL : ∀ j, d (eL j) = -massMagnitude α (s (.inr j)))
    (hE : ‖massShift C α * W - W * diagonal d‖ ≤ η) :
    let X := left (W.submatrix id eP)
    let Y := mixedRight (columns W (eP ∘ Sum.inl)) (columns W eL)
    let U := normalizeColumns X
    let V := normalizeColumns Y
    ∀ j, ‖C.toEuclideanLin (WithLp.toLp 2 (fun i => V i j)) -
        s j • (WithLp.toLp 2 (fun i => U i j))‖ ≤ 15 * u ∧
      ‖Cᵀ.toEuclideanLin (WithLp.toLp 2 (fun i => U i j)) -
        s j • (WithLp.toLp 2 (fun i => V i j))‖ ≤ 15 * u := by
  let eH : Fin h ↪ Fin r := ⟨eP ∘ Sum.inl, eP.injective.comp Sum.inl_injective⟩
  let e : Fin (h + l) ≃ Fin h ⊕ Fin l := finSumFinEquiv.symm
  let eP' := e.toEmbedding.trans eP
  let X := left (W.submatrix id eP)
  let Y := mixedRight (columns W eH) (columns W eL)
  let dX := fun j => (1 + α / massMagnitude α (s j)) / 2
  let dY := Sum.elim (fun i => (1 - α / massMagnitude α (s (.inl i))) / 2)
    (fun j => (1 + α / massMagnitude α (s (.inr j))) / 2)
  have hu₀ : 0 < u := hα.trans_le hαu
  have hg := parity_raw_gram_budgets C α η cut u W d eP' eH eL (s ∘ e)
    (s ∘ Sum.inl) (s ∘ Sum.inr) hα hη hcut hu₀ hbudget hsH
    (fun j => hs (.inr j)) hsL hW (fun j => hdP (e j)) (fun i => hdP (.inl i)) hdL hE
  obtain ⟨hdX', hdY, hX', hY⟩ := hg
  have hdX : ∀ j, (1 / 4 : ℝ) ≤ dX j := by
    intro j
    simpa [dX] using hdX' (e.symm j)
  have hX : ‖Xᵀ * X - diagonal dX‖ ≤ u / 32 := by
    have he := parity_gram_deviation_reindex X dX e
    exact he ▸ hX'
  have hX₈ : ‖Xᵀ * X - diagonal dX‖ ≤ u / 8 := hX.trans (by linarith)
  have hY₈ : ‖Yᵀ * Y - diagonal dY‖ ≤ u / 8 := hY.le
  have hnormX := (parity_normalized_gram_budgets X dX u hu hdX hX₈).1
  have hnormY := (parity_normalized_gram_budgets Y dY u hu hdY hY₈).1
  have hη' : η < u / 3 := by
    have he := (div_eq_iff hα.ne').1 hbudget
    nlinarith only [he, mul_le_mul_of_nonneg_left (show α ≤ 1 by linarith) hu₀.le, hu₀]
  have hmajor : ‖W‖ ≤ 1 := norm_le_one_of_orthonormal W hW
  have hparity := parity_norm_le W
  change ∀ j, ‖C.toEuclideanLin (col (normalizeColumns Y) j) -
      s j • col (normalizeColumns X) j‖ ≤ 15 * u ∧
    ‖Cᵀ.toEuclideanLin (col (normalizeColumns X) j) -
      s j • col (normalizeColumns Y) j‖ ≤ 15 * u
  intro j
  rw [normalizeColumns_col, normalizeColumns_col]
  obtain ⟨hLP, hRP⟩ := svd_assigned_parity_residuals C W d α η (eP j) hE
  dsimp only at hLP hRP
  rw [hdP] at hLP hRP
  have hx : col X j = col (left W) (eP j) := rfl
  cases j with
  | inl i =>
    have hy : col Y (.inl i) = col (right W) (eP (.inl i)) := rfl
    have hL : ‖C.toEuclideanLin (col Y (.inl i)) -
        (massMagnitude α (s (.inl i)) - α) • col X (.inl i)‖ ≤ η := by
      rwa [hx, hy]
    have hR : ‖Cᵀ.toEuclideanLin (col X (.inl i)) -
        (massMagnitude α (s (.inl i)) + α) • col Y (.inl i)‖ ≤ η := by
      rwa [hx, hy]
    have ha : massMagnitude α (s (.inl i)) + α ≤ 1 := by
      linarith only [massMagnitude_le_add hα (hs (.inl i)), hsMax (.inl i), hαu, hu]
    have hhigh := svd_high_normalized_residuals C (col X (.inl i)) (col Y (.inl i))
      hα (by linarith only [hcut, hsH i]) ha hη' (hnormX _) (hnormY _)
      (gram_column_deviation X dX hX₈ _) (gram_column_deviation Y dY hY₈ _) hL hR
    exact ⟨hhigh.1.le.trans (by linarith), hhigh.2.le.trans (by linarith)⟩
  | inr i =>
    have hy : col Y (.inr i) = col (right W) (eL i) := rfl
    obtain ⟨hLN, _⟩ := svd_assigned_parity_residuals C W d α η (eL i) hE
    dsimp only at hLN
    rw [hdL] at hLN
    have hL : ‖C.toEuclideanLin (col Y (.inr i)) -
        (-massMagnitude α (s (.inr i)) - α) • col (left W) (eL i)‖ ≤ η := by
      rwa [hy]
    have hR : ‖Cᵀ.toEuclideanLin (col X (.inr i)) -
        (massMagnitude α (s (.inr i)) + α) • col (right W) (eP (.inr i))‖ ≤ η := by
      rwa [hx]
    have hxNeg := (column_le_operatorNorm (left W) (eL i)).trans (hparity.1.trans hmajor)
    have hyPos := (column_le_operatorNorm (right W) (eP (.inr i))).trans (hparity.2.trans hmajor)
    have hlow := svd_low_normalized_residuals C (col X (.inr i)) (col Y (.inr i))
      (col (left W) (eL i)) (col (right W) (eP (.inr i))) hα hαu
      (hs (.inr i)) ((hsL i).trans hcutu) hη' (hnormX _) (hnormY _) hxNeg hyPos hL hR
    exact ⟨hlow.1.le, hlow.2.le⟩

end
end NumStability.CertifiedTridiagonalEigenpairs
