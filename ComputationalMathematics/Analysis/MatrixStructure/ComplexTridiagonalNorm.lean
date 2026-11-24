import ComputationalMathematics.Analysis.MatrixStructure.TridiagonalNorm
import Mathlib.Analysis.CStarAlgebra.Matrix

/-!
# Euclidean norm of a complex tridiagonal matrix

The Euclidean action of a complex matrix is dominated by the action of the
real matrix of its entrywise norms. The real tridiagonal bound therefore
also controls complex tridiagonal perturbations.
-/

namespace NumStability

open scoped Matrix Matrix.Norms.L2Operator

/-- A complex matrix has induced Euclidean norm at most that of the real
matrix obtained by taking the norm of each entry. -/
theorem complexMatrixOperatorNorm_le_entrywiseNorm {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℂ) :
    ‖A‖ ≤ realMatrixOperatorNorm (fun i j => ‖A i j‖) := by
  let B : Matrix (Fin m) (Fin n) ℝ := fun i j => ‖A i j‖
  let T : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin m) :=
    LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin A)
  change ‖T‖ ≤ ‖realMatrixContinuousLinearMap B‖
  apply T.opNorm_le_bound (norm_nonneg _)
  intro x
  let y : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 (fun j => ‖x j‖)
  have hy : ‖y‖ = ‖x‖ := by
    rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
    simp [y]
  have hnorm (i : Fin m) :
      ‖(T x) i‖ ≤ (realMatrixContinuousLinearMap B y) i := by
    change ‖(A *ᵥ (WithLp.ofLp x)) i‖ ≤ (B *ᵥ (WithLp.ofLp y)) i
    simp only [Matrix.mulVec, dotProduct]
    simpa only [norm_mul] using
      (norm_sum_le (Finset.univ : Finset (Fin n)) (fun j => A i j * x j))
  calc
    ‖T x‖ ≤ ‖realMatrixContinuousLinearMap B y‖ := by
      rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
      apply Real.sqrt_le_sqrt
      refine Finset.sum_le_sum fun i _ => ?_
      apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).2
      exact (hnorm i).trans (Real.le_norm_self _)
    _ ≤ ‖realMatrixContinuousLinearMap B‖ * ‖y‖ :=
      (realMatrixContinuousLinearMap B).le_opNorm y
    _ = ‖realMatrixContinuousLinearMap B‖ * ‖x‖ := by rw [hy]

/-- A complex tridiagonal matrix with diagonal bound `d` and both adjacent
bands bounded by `e` has induced Euclidean operator norm at most `d + 2 * e`. -/
theorem complexMatrixOperatorNorm_le_of_tridiagonal {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) {d e : ℝ} (hd : 0 ≤ d) (he : 0 ≤ e)
    (hband : ∀ i j, (i.val + 1 < j.val ∨ j.val + 1 < i.val) → A i j = 0)
    (hdiag : ∀ i, ‖A i i‖ ≤ d)
    (hoff : ∀ i j, (i.val + 1 = j.val ∨ j.val + 1 = i.val) → ‖A i j‖ ≤ e) :
    ‖A‖ ≤ d + 2 * e := by
  refine (complexMatrixOperatorNorm_le_entrywiseNorm A).trans
    (realMatrixOperatorNorm_le_of_tridiagonal (fun i j => ‖A i j‖) hd he ?_ ?_ ?_)
  · intro i j hij
    simp [hband i j hij]
  · intro i
    simpa only [abs_of_nonneg (norm_nonneg _)] using hdiag i
  · intro i j hij
    simpa only [abs_of_nonneg (norm_nonneg _)] using hoff i j hij

end NumStability
