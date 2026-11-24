import ComputationalMathematics.Source.CertifiedTridiagonalEigenpairs.TridiagonalEigenpairStorage
import ComputationalMathematics.Source.CertifiedTridiagonalEigenpairs.TridiagonalGuarantee.Precision

/-! The selected tridiagonal eigenpair guarantee for the native execution. -/

open MeasureTheory
open scoped ENNReal

namespace NumStability.CertifiedTridiagonalEigenpairs.SourceTargets

open FloatingPointFormat.UnboundedBinary NoisyRankCertificate

/-- Theorem `main:theorem`: every native return satisfies the indexed
stability guarantee, and the work, trial count, and workspace describe the
same exact-dispatch and normalized-retry execution. -/
def selectedTridiagonalEigenpairs : Prop :=
  ∃ C_W C_S C_hp : ℕ, 0 < C_W ∧ 0 < C_S ∧ 0 < C_hp ∧
    ∀ (n p : ℕ) (hp : 2 ≤ p) (J : Finset ℕ)
      (a : Fin (n + 1) → Word p hp) (b : Fin n → Word p hp)
      (hguard : precisionGuard (n + 1) p) (hJ : J.Nonempty)
      (hJvalid : J ⊆ Finset.Icc 1 (n + 1)),
      let d := n + 1
      let k := J.card
      let μ := retryBitMeasure n J
      let run := fun bits => runTridiagonalEigenpairs a b bits hguard hJ hJvalid
      let W := tridiagonalEigenpairWork a b hJvalid
      let τ := tridiagonalEigenpairAttemptCount a b hJvalid
      let β := 3 / (2048 * (nextPowerOfTwo d : ℝ) ^ 2)
      workingPrecision d k p = 2 * p + 3 * Nat.clog 2 d + Nat.clog 2 k + 32 ∧
      tridiagonalEigenpairRespectsPrecision a b hguard hJ hJvalid ∧
      (∀ᵐ bits ∂μ, ∃ out, run bits = some out) ∧
      (∀ bits out, run bits = some out →
        ReturnedAccuracy (requestedRankOrder hJvalid) (storedTridiagonal a b)
          (sturmTridiagonal_isHermitian _ _) out.columns out.labels (unitRoundoff p)) ∧
      (∫⁻ bits, W bits ∂μ) ≤ ((C_W * d * k * p : ℕ) : ℝ≥0∞) ∧
      (∀ bits, tridiagonalEigenpairWorkspace a b bits hguard hJ hJvalid ≤ C_S * (d + d * k)) ∧
      (∀ m : ℕ, μ {bits | (m : ℝ≥0∞) < τ bits} ≤ ENNReal.ofReal β ^ m) ∧
      (∫⁻ bits, τ bits ∂μ) ≤ ENNReal.ofReal ((1 - β)⁻¹) ∧
      ENNReal.ofReal ((1 - β)⁻¹) < 2 ∧
      (∀ m : ℕ, 1 ≤ m →
        μ {bits | ((C_hp * (m + 1) * d * k * p : ℕ) : ℝ≥0∞) < W bits} ≤
          ENNReal.ofReal β ^ m)

end NumStability.CertifiedTridiagonalEigenpairs.SourceTargets
