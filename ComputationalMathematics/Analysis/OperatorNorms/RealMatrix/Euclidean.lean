import ComputationalMathematics.Analysis.SingularValues.EckartYoung

namespace NumStability.RealMatrixOperator

open scoped BigOperators
noncomputable section

private theorem norm_toLp_eq_vecNorm2 {n : ℕ} (x : Fin n → ℝ) :
    ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin n))‖ = vecNorm2 x := by
  simp only [EuclideanSpace.norm_eq, vecNorm2, vecNorm2Sq,
    Real.norm_eq_abs, sq_abs]

theorem rectOpNorm2Le_realMatrixOperatorNorm {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) : rectOpNorm2Le A (realMatrixOperatorNorm A) := by
  intro x
  have h := ContinuousLinearMap.le_opNorm (realMatrixContinuousLinearMap A)
    (WithLp.toLp 2 x)
  change ‖(WithLp.toLp 2 (rectMatMulVec A x) : EuclideanSpace ℝ (Fin m))‖ ≤
    realMatrixOperatorNorm A * ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin n))‖ at h
  simpa only [norm_toLp_eq_vecNorm2] using h

end
end NumStability.RealMatrixOperator

namespace NumStability.RealMatrixOperator
open scoped BigOperators
noncomputable section
private theorem vecNorm2_sign_mul {n : ℕ} (s x : Fin n → ℝ)
    (hs : ∀ i, |s i| = 1) : vecNorm2 (fun i => s i * x i) = vecNorm2 x := by
  unfold vecNorm2 vecNorm2Sq
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [mul_pow, ← sq_abs (s i), hs i]
  simp

theorem rectOpNorm2Le_signed {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (r : Fin m → ℝ) (s : Fin n → ℝ)
    (hr : ∀ i, |r i| = 1) (hs : ∀ j, |s j| = 1)
    (c : ℝ) (hA : rectOpNorm2Le A c) :
    rectOpNorm2Le (fun i j => r i * A i j * s j) c := by
  intro x
  have haction : rectMatMulVec (fun i j => r i * A i j * s j) x =
      fun i => r i * rectMatMulVec A (fun j => s j * x j) i := by
    funext i
    unfold rectMatMulVec
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [haction, vecNorm2_sign_mul r _ hr]
  simpa only [vecNorm2_sign_mul s x hs] using hA (fun j => s j * x j)


end
end NumStability.RealMatrixOperator
