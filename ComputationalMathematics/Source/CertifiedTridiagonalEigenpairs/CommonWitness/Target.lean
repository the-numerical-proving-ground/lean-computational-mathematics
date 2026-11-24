import ComputationalMathematics.Analysis.Eigenvalues.StrictSpectralCount
import ComputationalMathematics.Analysis.FloatingPointArithmetic.UnboundedBinary.Basic
import ComputationalMathematics.Analysis.OperatorNorms.RealMatrix
import ComputationalMathematics.Analysis.SingularValues.InverseSVD
import ComputationalMathematics.Order.Finset.OrderedCompletion.Signed

/-!
# The common symmetric indexed witness

The nontrivial branch of the tridiagonal guarantee, from the stored matrix
and selected signed eigenvectors of an accepted trial to the one shared
symmetric witness. The full eigenbasis and the witness are proof objects.
-/

namespace NumStability.CertifiedTridiagonalEigenpairs.SourceTargets

open NoisyRankCertificate OrderStatistics FloatingPointFormat.UnboundedBinary
open scoped Matrix.Norms.Frobenius

/-- The witness has all reported labels at their requested positions, even
when distinct internal labels round to the same value. Its selected columns
are the exact signed eigenvectors chosen before the spectrum is clipped. -/
def tridiagonalCommonWitness : Prop :=
  ∀ (n k p : ℕ) (hp : 2 ≤ p) (I : Fin k → Fin n)
    (T S M : Matrix (Fin n) (Fin n) ℝ) (hM : M.IsHermitian)
    (R Δ η : ℝ) (θ : Fin k → ℝ)
    (U Qhat : Fin k → EuclideanSpace ℝ (Fin n)),
    let u := unitRoundoff p
    let ℓ := ascendingEigenvalue hM
    let μ := fun j => roundToEven p hp (θ j)
    let ζ := clipSelectedValues I ℓ μ
    2 ≤ n →
    1 ≤ k →
    StrictMono I →
    0 < R →
    R < 8 * realMatrixOperatorNorm T →
    T = R • S →
    realMatrixOperatorNorm (M - S) ≤ u / 128 →
    2 * η < Δ →
    (∀ j i, i ≠ I j → Δ < |ℓ i - ℓ (I j)|) →
    (∀ j, |θ j - ℓ (I j)| ≤ η) →
    (∀ j, |μ j - ℓ (I j)| < 2 * u) →
    (∀ j, ‖U j‖ = 1 ∧ M.toEuclideanLin (U j) = ℓ (I j) • U j) →
    (∀ j, ‖Qhat j - U j‖ ≤ 4 * u) →
    StrictMono θ ∧ Monotone μ ∧ Monotone ζ ∧
    (∀ j, ζ (I j) = μ j) ∧ (∀ i, |ζ i - ℓ i| ≤ 2 * u) ∧
    ∃ (b : OrthonormalBasis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)))
      (W : Matrix (Fin n) (Fin n) ℝ) (hW : W.IsHermitian),
      let V := orthonormalBasisMatrix b
      let E : Matrix (Fin n) (Fin k) ℝ := fun i j => (Qhat j - U j) i
      (∀ i, M.toEuclideanLin (b i) = ℓ i • b i) ∧
      (∀ j, b (I j) = U j) ∧
      W = R • (V * Matrix.diagonal ζ * V.transpose) ∧
      realMatrixOperatorNorm (W - T) ≤ R * (2 * u + u / 128) ∧
      R * (2 * u + u / 128) < 24 * u * realMatrixOperatorNorm T ∧
      realMatrixOperatorNorm (W - T) ≤ 24 * u * realMatrixOperatorNorm T ∧
      Orthonormal ℝ U ∧ ‖E‖ ≤ 4 * Real.sqrt k * u ∧
      ∀ j, W.toEuclideanLin (U j) = (R * μ j) • U j ∧
        ascendingEigenvalue hW (I j) = R * μ j ∧ ‖Qhat j - U j‖ ≤ 4 * u

end NumStability.CertifiedTridiagonalEigenpairs.SourceTargets
