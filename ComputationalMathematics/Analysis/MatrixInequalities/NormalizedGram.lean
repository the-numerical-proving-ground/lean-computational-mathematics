import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Gram defects after column normalization

A raw Gram close to a diagonal matrix gives operator and entrywise bounds
for the defect after exact column normalization.
-/

open Matrix
open scoped Matrix.Norms.L2Operator

namespace NumStability.NormalizedGram

noncomputable section

variable {m ι : Type*} [Fintype m] [Fintype ι] [DecidableEq ι]

/-- Euclidean norm of a matrix column. -/
def columnNorm (X : Matrix m ι ℝ) (j : ι) : ℝ :=
  ‖(WithLp.toLp 2 (fun i => X i j) : EuclideanSpace ℝ m)‖

/-- Exact column normalization by the Euclidean column norms. -/
def normalizeColumns (X : Matrix m ι ℝ) : Matrix m ι ℝ :=
  X * diagonal (fun j => (columnNorm X j)⁻¹)

omit [Fintype ι] [DecidableEq ι] in
theorem gram_diag (X : Matrix m ι ℝ) (i : ι) :
    (Xᵀ * X) i i = columnNorm X i ^ 2 := by
  rw [columnNorm, EuclideanSpace.norm_sq_eq, Matrix.mul_apply]
  simp only [Matrix.transpose_apply]
  apply Finset.sum_congr rfl
  intro j _
  rw [Real.norm_eq_abs, sq_abs, pow_two]

theorem abs_apply_le_norm {n : Type*} [Fintype n] (A : Matrix n ι ℝ) (i : n) (j : ι) :
    |A i j| ≤ ‖A‖ := by
  let e : EuclideanSpace ℝ ι := EuclideanSpace.single j 1
  let y : EuclideanSpace ℝ n := (EuclideanSpace.equiv n ℝ).symm (A *ᵥ e)
  have he : ‖e‖ = 1 := by simp [e]
  have hy : y i = A i j := by simp [y, e, Matrix.mulVec_single]
  rw [← hy, ← Real.norm_eq_abs]
  exact (PiLp.norm_apply_le y i).trans (by simpa [y, he] using Matrix.l2_opNorm_mulVec A e)

theorem norm_diagonal_entries_le (F : Matrix ι ι ℝ) :
    ‖diagonal (fun i => F i i)‖ ≤ ‖F‖ := by
  rw [Matrix.l2_opNorm_diagonal]
  exact (pi_norm_le_iff_of_nonneg (norm_nonneg F)).2
    (fun i => by simpa [Real.norm_eq_abs] using abs_apply_le_norm F i i)

theorem normalize_gram_defect (X : Matrix m ι ℝ) (d : ι → ℝ)
    (hX : ∀ i, 0 < columnNorm X i) :
    let F := Xᵀ * X - diagonal d
    let D := diagonal (fun i => (columnNorm X i)⁻¹)
    (normalizeColumns X)ᵀ * normalizeColumns X - 1 =
      D * (F - diagonal (fun i => F i i)) * D := by
  dsimp only
  let D := diagonal (fun i => (columnNorm X i)⁻¹)
  have ha : (X * D)ᵀ * (X * D) = (D * (Xᵀ * X)) * D := by
    simp only [Matrix.transpose_mul, D, Matrix.diagonal_transpose, Matrix.mul_assoc]
  rw [normalizeColumns, ha]
  ext i j
  simp only [D, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.sub_apply]
  by_cases hij : i = j
  · subst j
    simp only [Matrix.one_apply_eq, Matrix.diagonal_apply_eq, sub_self, zero_mul, mul_zero]
    rw [gram_diag]
    field_simp [(hX i).ne']
    ring
  · simp [Matrix.one_apply_ne hij, Matrix.diagonal_apply_ne _ hij]

theorem normalize_gram_diag (X : Matrix m ι ℝ) {i : ι} (hi : 0 < columnNorm X i) :
    ((normalizeColumns X)ᵀ * normalizeColumns X) i i = 1 := by
  rw [normalizeColumns, gram_diag, columnNorm]
  have he : (fun j => (X * diagonal (fun j => (columnNorm X j)⁻¹)) j i) =
      (columnNorm X i)⁻¹ • (fun j => X j i) := by
    funext j
    rw [Matrix.mul_diagonal]
    simp [mul_comm]
  rw [he, WithLp.toLp_smul, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hi)]
  change ((columnNorm X i)⁻¹ * columnNorm X i) ^ 2 = _
  rw [inv_mul_cancel₀ hi.ne', one_pow]

/-- The normalized Gram defect is at most twice the raw defect divided by the
square of a common lower bound on the column norms. -/
theorem normalize_gram_norm_le (X : Matrix m ι ℝ) (d : ι → ℝ) {c τ : ℝ}
    (hc : 0 < c) (hX : ∀ i, c ≤ columnNorm X i) (hF : ‖Xᵀ * X - diagonal d‖ ≤ τ) :
    ‖(normalizeColumns X)ᵀ * normalizeColumns X - 1‖ ≤ 2 * τ / c ^ 2 := by
  let F := Xᵀ * X - diagonal d
  let D := diagonal (fun i => (columnNorm X i)⁻¹)
  have hD : ‖D‖ ≤ c⁻¹ := by
    change ‖diagonal (fun i => (columnNorm X i)⁻¹)‖ ≤ _
    rw [Matrix.l2_opNorm_diagonal]
    refine (pi_norm_le_iff_of_nonneg (inv_nonneg.mpr hc.le)).2 fun i => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (hc.le.trans (hX i)))]
    exact inv_anti₀ hc (hX i)
  have hτ : 0 ≤ τ := (norm_nonneg _).trans hF
  have herr : ‖F - diagonal (fun i => F i i)‖ ≤ 2 * τ :=
    (norm_sub_le _ _).trans (by
      have hd := norm_diagonal_entries_le F
      change ‖F‖ ≤ τ at hF
      linarith)
  rw [normalize_gram_defect X d (fun i => hc.trans_le (hX i))]
  change ‖D * (F - diagonal (fun i => F i i)) * D‖ ≤ _
  calc
    _ ≤ ‖D‖ * ‖F - diagonal (fun i => F i i)‖ * ‖D‖ := by
      grw [Matrix.l2_opNorm_mul, Matrix.l2_opNorm_mul]
    _ ≤ c⁻¹ * (2 * τ) * c⁻¹ := by gcongr
    _ = _ := by ring

/-- A raw diagonal model and operator error certify a lower bound on every
actual column norm. -/
theorem le_columnNorm_of_gram (X : Matrix m ι ℝ) (d : ι → ℝ) {c τ : ℝ}
    (hc : 0 ≤ c) (hd : ∀ i, c ^ 2 + τ ≤ d i)
    (hF : ‖Xᵀ * X - diagonal d‖ ≤ τ) (i : ι) : c ≤ columnNorm X i := by
  have h := (abs_apply_le_norm (Xᵀ * X - diagonal d) i i).trans hF
  rw [Matrix.sub_apply, Matrix.diagonal_apply_eq, gram_diag] at h
  have hcol : 0 ≤ columnNorm X i := norm_nonneg _
  exact (sq_le_sq₀ hc hcol).1 (by linarith only [(abs_le.mp h).1, hd i])

/-- An individual off-diagonal defect incurs only one factor of the raw
operator error, since removing the diagonal leaves this entry unchanged. -/
theorem abs_normalize_gram_apply_le (X : Matrix m ι ℝ) (d : ι → ℝ) {c τ : ℝ}
    (hc : 0 < c) (hX : ∀ i, c ≤ columnNorm X i) (hF : ‖Xᵀ * X - diagonal d‖ ≤ τ)
    {i j : ι} (hij : i ≠ j) :
    |((normalizeColumns X)ᵀ * normalizeColumns X) i j| ≤ τ / c ^ 2 := by
  have h := congrArg (fun A : Matrix ι ι ℝ => A i j)
    (normalize_gram_defect X d (fun i => hc.trans_le (hX i)))
  dsimp only at h
  simp only [Matrix.sub_apply, Matrix.one_apply_ne hij, sub_zero, Matrix.mul_diagonal,
    Matrix.diagonal_mul, Matrix.diagonal_apply_ne _ hij] at h
  have hi : 0 < columnNorm X i := hc.trans_le (hX i)
  have hj : 0 < columnNorm X j := hc.trans_le (hX j)
  have hentry := (abs_apply_le_norm (Xᵀ * X - diagonal d) i j).trans hF
  simp only [Matrix.sub_apply, Matrix.diagonal_apply_ne _ hij, sub_zero] at hentry
  rw [h, abs_mul, abs_mul, abs_of_pos (inv_pos.mpr hi), abs_of_pos (inv_pos.mpr hj)]
  have hτ : 0 ≤ τ := (norm_nonneg _).trans hF
  have hDi := inv_anti₀ hc (hX i)
  have hDj := inv_anti₀ hc (hX j)
  calc
    _ ≤ c⁻¹ * τ * c⁻¹ := by gcongr
    _ = _ := by ring

end
end NumStability.NormalizedGram
