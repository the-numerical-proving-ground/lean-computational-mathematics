import ComputationalMathematics.Analysis.Eigenvalues.HermitianInterlacing
import Mathlib.Analysis.CStarAlgebra.Matrix

/-! # Weyl's inequality in the Euclidean operator norm -/

namespace Matrix.IsHermitian

open scoped Matrix.Norms.L2Operator

variable {𝕜 : Type*} [RCLike 𝕜] {n : ℕ}

private theorem orderedEigenvaluesFin_sub_le_operatorNorm
    {A B : Matrix (Fin n) (Fin n) 𝕜} (hA : A.IsHermitian) (hB : B.IsHermitian) (j : Fin n) :
    hA.orderedEigenvaluesFin j - hB.orderedEigenvaluesFin j ≤ ‖A - B‖ := by
  apply hA.orderedEigenvaluesFin_sub_le_of_rayleigh hB j
  intro x
  have hsub : RCLike.re (inner 𝕜 x ((A - B).toEuclideanLin x)) =
      RCLike.re (inner 𝕜 x (A.toEuclideanLin x)) -
        RCLike.re (inner 𝕜 x (B.toEuclideanLin x)) := by
    simp only [map_sub, LinearMap.sub_apply, inner_sub_right]
  rw [← sub_le_iff_le_add', ← hsub]
  calc
    RCLike.re (inner 𝕜 x ((A - B).toEuclideanLin x)) ≤
        ‖inner 𝕜 x ((A - B).toEuclideanLin x)‖ := RCLike.re_le_norm _
    _ ≤ ‖x‖ * ‖(A - B).toEuclideanLin x‖ := norm_inner_le_norm _ _
    _ ≤ ‖x‖ * (‖A - B‖ * ‖x‖) :=
      mul_le_mul_of_nonneg_left ((A - B).l2_opNorm_mulVec x) (norm_nonneg _)
    _ = ‖A - B‖ * ‖x‖ ^ 2 := by ring

/-- The eigenvalues of two Hermitian matrices at the same rank differ by no
more than the induced Euclidean operator norm of their difference. -/
theorem abs_orderedEigenvaluesFin_sub_le_operatorNorm
    {A B : Matrix (Fin n) (Fin n) 𝕜} (hA : A.IsHermitian) (hB : B.IsHermitian) (j : Fin n) :
    |hA.orderedEigenvaluesFin j - hB.orderedEigenvaluesFin j| ≤ ‖A - B‖ := by
  rw [abs_sub_le_iff]
  exact ⟨orderedEigenvaluesFin_sub_le_operatorNorm hA hB j,
    (orderedEigenvaluesFin_sub_le_operatorNorm hB hA j).trans_eq (norm_sub_rev _ _)⟩

end Matrix.IsHermitian
