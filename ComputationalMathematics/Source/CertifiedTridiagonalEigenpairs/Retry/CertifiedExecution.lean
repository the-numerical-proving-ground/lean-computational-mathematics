import ComputationalMathematics.Source.CertifiedTridiagonalEigenpairs.FiniteTrial.CostReliability
import ComputationalMathematics.Source.CertifiedTridiagonalEigenpairs.Retry.Execution

/-! Almost-sure return and the trial count of the actual rounded acceptance loop. -/

namespace NumStability.CertifiedTridiagonalEigenpairs

open MeasureTheory IndependentRetry
open scoped ENNReal

/-- Fresh fair bit blocks drive the same gate whose success returns the stored matrix.
The one-trial rejection certificate supplies the geometric tail and expected cost
of the number of invocations. The precision guard and entry bounds are the
nontrivial branch's preconditions after exact scaling. -/
theorem certifiedRetryRun {n p : ℕ} {J : Finset ℕ}
    (a : Fin (n + 1) → TrialWord n J p) (b : Fin n → TrialWord n J p)
    (hn : 2 ≤ n + 1) (hguard : precisionGuard (n + 1) p)
    (hJ : J.Nonempty) (hJbounds : J ⊆ Finset.Icc 1 (n + 1))
    (ha : ∀ i, |(a i).value| ≤ 1 / 4) (hb : ∀ i, |(b i).value| ≤ 1 / 4) :
    (∀ᵐ bits ∂retryBitMeasure n J, ∃ result, retryRun a b bits = some result) ∧
    (∀ m : ℕ, retryBitMeasure n J
      {bits | (m : ℝ≥0∞) < retryCount (trialRejected n p J a b) bits} ≤
        ENNReal.ofReal (rejectionBound (n + 1)) ^ m) ∧
    (∫⁻ bits, retryCount (trialRejected n p J a b) bits ∂retryBitMeasure n J) ≤
      ENNReal.ofReal ((1 - rejectionBound (n + 1))⁻¹) ∧
    ENNReal.ofReal ((1 - rejectionBound (n + 1))⁻¹) < 2 := by
  have hβ := finiteTrialUniformRejection n p J a b hn hguard hJ hJbounds ha hb
  exact ⟨ae_retryRun_returns hβ, fun m => retryRun_attemptTail_le hβ m,
    retryRun_attemptExpectation_le hβ⟩

end NumStability.CertifiedTridiagonalEigenpairs
