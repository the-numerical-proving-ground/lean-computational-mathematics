import ComputationalMathematics.Source.CertifiedTridiagonalEigenpairs.TridiagonalGuarantee.Target

/-! Proof of the selected tridiagonal eigenpair source theorem. -/

namespace NumStability.CertifiedTridiagonalEigenpairs

open scoped ENNReal

theorem selectedTridiagonalEigenpairs : SourceTargets.selectedTridiagonalEigenpairs := by
  refine ⟨12000, 64, 4000, by decide, by decide, by decide, ?_⟩
  intro n p hp J a b hguard hJ hJvalid
  have hwork := tridiagonalEigenpairWork_expectation_tail a b hguard hJ hJvalid
  have hcount := tridiagonalEigenpairAttemptCount_expectation_tail a b hguard hJ hJvalid
  refine ⟨rfl, tridiagonalEigenpair_respectsPrecision a b hguard hJ hJvalid,
    runTridiagonalEigenpairs_returns a b hguard hJ hJvalid,
    fun bits => runTridiagonalEigenpairs_accuracy a b bits hguard hJ hJvalid, ?_,
    fun bits => tridiagonalEigenpairWorkspace_le a b bits hguard hJ hJvalid,
    hcount.1, hcount.2.1, hcount.2.2, ?_⟩
  · convert hwork.1 using 1
    unfold retryTrialWorkScale
    push_cast
    ring
  · intro m _
    have hcut :
        ((4000 * (m + 1) * (n + 1) * J.card * p : ℕ) : ℝ≥0∞) =
          (retryTrialWorkScale n J p : ℝ≥0∞) * ((m : ℝ≥0∞) + 1) := by
      unfold retryTrialWorkScale
      push_cast
      ring
    simpa only [hcut] using hwork.2 m

end NumStability.CertifiedTridiagonalEigenpairs
