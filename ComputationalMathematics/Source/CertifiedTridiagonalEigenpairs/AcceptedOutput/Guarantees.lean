import ComputationalMathematics.Source.CertifiedTridiagonalEigenpairs.ReturnedErrors
import ComputationalMathematics.Source.CertifiedTridiagonalEigenpairs.CommonWitness.Proof
import ComputationalMathematics.Source.CertifiedTridiagonalEigenpairs.Parameters

/-! Deterministic guarantees for an assembled array of returned eigenpairs. -/

namespace NumStability.CertifiedTridiagonalEigenpairs

open Matrix WithLp NoisyRankCertificate FloatingPointFormat.UnboundedBinary
open scoped Matrix.Norms.L2Operator RealInnerProductSpace

/-- The accuracy of a returned array, including one common indexed witness
for all of its reported eigenpairs. -/
def ReturnedAccuracy {n k : ℕ} (I : Fin k → Fin n)
    (T : Matrix (Fin n) (Fin n) ℝ) (hT : T.IsHermitian)
    (Q : Matrix (Fin n) (Fin k) ℝ) (labels : Fin k → ℝ) (u : ℝ) : Prop :=
  (∀ j, |labels j - ascendingEigenvalue hT (I j)| ≤ 16 * u * ‖T‖) ∧
  ‖T * Q - Q * diagonal labels‖ ≤ 128 * Real.sqrt k * u * ‖T‖ ∧
  ‖Qᵀ * Q - 1‖ ≤ 9 * Real.sqrt k * u ∧
  (∀ i j : Fin k, i ≠ j → |(Qᵀ * Q) i j| ≤ 9 * u) ∧
  (∀ j, ‖toLp 2 (T *ᵥ Q.col j) - labels j • toLp 2 (Q.col j)‖ ≤ 128 * u * ‖T‖) ∧
  ∃ (W : Matrix (Fin n) (Fin n) ℝ) (hW : W.IsHermitian)
    (V : Fin k → EuclideanSpace ℝ (Fin n)),
    ‖W - T‖ ≤ 24 * u * ‖T‖ ∧ Orthonormal ℝ V ∧
    frobNormRect (Q - (Matrix.of fun i j => V j i)) ≤ 4 * Real.sqrt k * u ∧
    ∀ j, W.toEuclideanLin (V j) = labels j • V j ∧
      ascendingEigenvalue hW (I j) = labels j ∧ ‖toLp 2 (Q.col j) - V j‖ ≤ 4 * u

set_option maxHeartbeats 1200000 in
/-- Combine the source's returned-error and indexed-witness lemmas for the
same signed unit eigenvectors of the accepted matrix. -/
theorem returnedAccuracy_of_signed_eigenvectors
    {n k p : ℕ} (hp : 2 ≤ p) (hn : 2 ≤ n) (hk : 0 < k) (hkn : k ≤ n)
    (I : Fin k ↪o Fin n) (T S M : Matrix (Fin n) (Fin n) ℝ)
    (hT : T.IsHermitian) (hS : S.IsHermitian) (hM : M.IsHermitian)
    {R Δ : ℝ} (hR : 0 < R) (hscale : T = R • S) (hRbound : R < 8 * ‖T‖)
    (Q : Matrix (Fin n) (Fin k) ℝ) (theta labels : Fin k → ℝ)
    (U : Fin k → EuclideanSpace ℝ (Fin n))
    (hguard : precisionGuard n p) (hclose : ‖M - S‖ ≤ unitRoundoff p / 128) (hMnorm : ‖M‖ < 1)
    (hseparated : 2 * finalLabelTolerance n k p < Δ)
    (hgap : ∀ j i, i ≠ I j → Δ < |ascendingEigenvalue hM i - ascendingEigenvalue hM (I j)|)
    (htheta : ∀ j, |theta j - ascendingEigenvalue hM (I j)| ≤ finalLabelTolerance n k p)
    (hmu : ∀ j, |roundToEven p hp (theta j) - ascendingEigenvalue hM (I j)| < 2 * unitRoundoff p)
    (hlabels : ∀ j, labels j = R * roundToEven p hp (theta j))
    (hU : ∀ j, ‖U j‖ = 1 ∧ M.toEuclideanLin (U j) = ascendingEigenvalue hM (I j) • U j)
    (hcolumn : ∀ j, ‖toLp 2 (Q.col j) - U j‖ ≤ 4 * unitRoundoff p) :
    ReturnedAccuracy I T hT Q labels (unitRoundoff p) := by
  let B : Matrix (Fin n) (Fin k) ℝ := fun i j => U j i
  let Qhat : Fin k → EuclideanSpace ℝ (Fin n) := fun j => toLp 2 (Q.col j)
  have h := tridiagonalCommonWitness_proof n k p hp I T S M hM R Δ (finalLabelTolerance n k p)
    theta U Qhat hn hk I.strictMono hR hRbound hscale hclose hseparated hgap htheta hmu hU hcolumn
  obtain ⟨_, _, _, _, _, _, W, hW, _, _, _, _, _, hback, horth, _, hindexed⟩ := h
  have hUGram : Bᵀ * B = 1 := by
    ext i j
    calc
      _ = (U j).ofLp ⬝ᵥ star (U i).ofLp := by
        rw [star_trivial, dotProduct_comm]
        rfl
      _ = inner ℝ (U i) (U j) := (EuclideanSpace.inner_eq_star_dotProduct (U i) (U j)).symm
      _ = if i = j then 1 else 0 := (orthonormal_iff_ite.mp horth) i j
      _ = _ := Matrix.one_apply.symm
  have hUEig :
      M * B = B * diagonal (fun j => hermitianOrderedEigenvalue hM (I j).rev) := by
    ext i j
    have he := congrArg (fun v : EuclideanSpace ℝ (Fin n) => v i) (hU j).2
    rw [Matrix.mul_diagonal]
    simpa [B, Matrix.mul_apply, Matrix.toLpLin_apply, Matrix.mulVec, dotProduct,
      ascendingEigenvalue, PiLp.smul_apply, smul_eq_mul, mul_comm] using he
  have hdiff (j : Fin k) : toLp 2 (B.col j) = U j := rfl
  have hcols (j : Fin k) : ‖toLp 2 (Q.col j) - toLp 2 (B.col j)‖ ≤ 4 * unitRoundoff p := by
    rw [hdiff]
    exact hcolumn j
  obtain ⟨⟨_, hfrob⟩, hGram, hPairs, _, _, _, hResidual, hColResidual, hValues⟩ :=
    returnedEigenpairErrors hp hn hk hkn I T S M hT hS hM R hR hscale hRbound B Q theta
      hguard hclose hMnorm hUGram hUEig htheta hcols
  have hD : R • diagonal (fun j => roundToEven p hp (theta j)) = diagonal labels := by
    rw [← diagonal_smul]
    congr 1
    funext j
    exact (hlabels j).symm
  refine ⟨?_, hD ▸ hResidual, hGram, hPairs, ?_, W, hW, U, hback, horth, hfrob, ?_⟩
  · intro j
    rw [hlabels]
    exact (hValues j).2.2
  · intro j
    rw [hlabels]
    exact hColResidual j
  · intro j
    rw [hlabels]
    exact hindexed j

end NumStability.CertifiedTridiagonalEigenpairs
