import ComputationalMathematics.Analysis.Eigenvalues.DiagonalPerturbation
import ComputationalMathematics.Analysis.Eigenvalues.HermitianInterlacing
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-! The ordered eigenvalues are stable under real diagonal perturbations. -/

namespace Matrix.IsHermitian

open scoped BigOperators

private theorem diagonalPerturbation_rayleigh {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (v : Fin n → ℝ) (x : EuclideanSpace ℂ (Fin n)) :
    (inner ℂ x ((A.diagonalPerturbation v).toEuclideanLin x)).re =
      (inner ℂ x (A.toEuclideanLin x)).re + ∑ i, v i * ‖x i‖ ^ 2 := by
  have hvec : (A.diagonalPerturbation v).toEuclideanLin x =
      A.toEuclideanLin x + (Matrix.diagonal (fun i => (v i : ℂ))).toEuclideanLin x := by
    ext i
    simp [Matrix.diagonalPerturbation, Matrix.toLpLin_apply]
  rw [hvec, inner_add_right, Complex.add_re]
  congr 1
  rw [PiLp.inner_apply, Complex.re_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  change (((Matrix.diagonal (fun i => (v i : ℂ))) *ᵥ (fun j => x j)) i *
    (starRingEnd ℂ) (x i)).re = _
  rw [Matrix.mulVec_diagonal, mul_assoc, Complex.mul_conj, Complex.re_ofReal_mul, Complex.sq_norm]
  simp

private theorem orderedEigenvaluesFin_diagonalPerturbation_sub_le {n : ℕ}
    {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsHermitian) (j : Fin n)
    (v w : Fin n → ℝ) :
    (hA.diagonalPerturbation v).orderedEigenvaluesFin j -
      (hA.diagonalPerturbation w).orderedEigenvaluesFin j ≤ ‖v - w‖ := by
  apply (hA.diagonalPerturbation v).orderedEigenvaluesFin_sub_le_of_rayleigh
    (hA.diagonalPerturbation w) j
  intro x
  change (inner ℂ x ((A.diagonalPerturbation v).toEuclideanLin x)).re ≤
    (inner ℂ x ((A.diagonalPerturbation w).toEuclideanLin x)).re + ‖v - w‖ * ‖x‖ ^ 2
  rw [diagonalPerturbation_rayleigh, diagonalPerturbation_rayleigh, add_assoc]
  apply add_le_add_right
  rw [← sub_le_iff_le_add']
  rw [← Finset.sum_sub_distrib, EuclideanSpace.norm_sq_eq, Finset.mul_sum]
  refine Finset.sum_le_sum (fun i _ => ?_)
  rw [← sub_mul]
  exact mul_le_mul_of_nonneg_right
    ((le_abs_self (v i - w i)).trans (by
      simpa only [Pi.sub_apply, Real.norm_eq_abs] using norm_le_pi_norm (v - w) i))
    (sq_nonneg _)

/-- Each decreasing eigenvalue is 1-Lipschitz in the diagonal shifts, in the supremum norm. -/
theorem lipschitzWith_orderedEigenvaluesFin_diagonalPerturbation {n : ℕ}
    {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsHermitian) (j : Fin n) :
    LipschitzWith 1 (fun v => (hA.diagonalPerturbation v).orderedEigenvaluesFin j) := by
  apply LipschitzWith.of_dist_le_mul
  intro v w
  simp only [NNReal.coe_one, one_mul, dist_eq_norm, Real.norm_eq_abs, abs_sub_le_iff]
  exact ⟨orderedEigenvaluesFin_diagonalPerturbation_sub_le hA j v w,
    (orderedEigenvaluesFin_diagonalPerturbation_sub_le hA j w v).trans_eq (norm_sub_rev _ _)⟩

theorem continuous_orderedEigenvaluesFin_diagonalPerturbation {n : ℕ}
    {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsHermitian) (j : Fin n) :
    Continuous (fun v => (hA.diagonalPerturbation v).orderedEigenvaluesFin j) :=
  (hA.lipschitzWith_orderedEigenvaluesFin_diagonalPerturbation j).continuous

theorem isClosed_specifiedAdjacentGapEvent {n : ℕ}
    {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    (hA : A.IsHermitian) (j : Fin n) (g : ℝ) :
    IsClosed (hA.specifiedAdjacentGapEvent j g) :=
  isClosed_le
    ((hA.continuous_orderedEigenvaluesFin_diagonalPerturbation j.rev.castSucc).sub
      (hA.continuous_orderedEigenvaluesFin_diagonalPerturbation j.rev.succ))
    continuous_const

theorem measurableSet_specifiedAdjacentGapEvent {n : ℕ}
    {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    (hA : A.IsHermitian) (j : Fin n) (g : ℝ) :
    MeasurableSet (hA.specifiedAdjacentGapEvent j g) :=
  (hA.isClosed_specifiedAdjacentGapEvent j g).measurableSet

end Matrix.IsHermitian
