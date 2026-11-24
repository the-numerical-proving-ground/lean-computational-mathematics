import ComputationalMathematics.Algorithms.RandomizedLinearAlgebra.Retry.Independent
import ComputationalMathematics.Source.CertifiedTridiagonalEigenpairs.Retry.ConfidenceTarget
import ComputationalMathematics.Source.CertifiedTridiagonalEigenpairs.Parameters
import Mathlib.Probability.Distributions.Uniform

/-!
# Fresh finite trials for the tridiagonal eigensolver

For fixed input data, each trial uses `n` independent uniform `bits`-bit
integers; the same deterministic rejection predicate is applied at every
coordinate of the trial stream.
-/

open MeasureTheory
open scoped ENNReal

namespace NumStability.CertifiedTridiagonalEigenpairs

open IndependentRetry

/-- One integer from each of the `n` blocks of `bits` fair bits. -/
abbrev TrialDraws (n bits : ℕ) := Fin n → Fin (2 ^ bits)

/-- Uniform law of the integer tuple in one trial. -/
noncomputable def trialDrawMeasure (n bits : ℕ) : Measure (TrialDraws n bits) :=
  (PMF.uniformOfFintype (TrialDraws n bits)).toMeasure

instance (n bits : ℕ) : IsProbabilityMeasure (trialDrawMeasure n bits) := by
  unfold trialDrawMeasure
  infer_instance

namespace SourceTargets

/-- The almost-sure termination, attempt tail and mean for the perturbation loop,
conditional on the one-trial rejection theorem for its fixed input. -/
def tridiagonalRetryTransfer : Prop :=
  ∀ (n k : ℕ), 2 ≤ n → 0 < k → k ≤ n →
    let bits := rngBits n k
    ∀ (reject : Set (TrialDraws n bits)),
      trialDrawMeasure n bits reject ≤ ENNReal.ofReal (rejectionBound n) →
      let μ := streamMeasure (trialDrawMeasure n bits)
      (∀ᵐ x ∂μ, ∃ j : ℕ, x j ∉ reject) ∧
      (∀ m : ℕ, μ {x | (m : ℝ≥0∞) < retryCount reject x} ≤
        ENNReal.ofReal (rejectionBound n) ^ m) ∧
      ((∫⁻ x, retryCount reject x ∂μ) ≤ ENNReal.ofReal ((1 - rejectionBound n)⁻¹)) ∧
      ENNReal.ofReal ((1 - rejectionBound n)⁻¹) < 2

/-- Expected work and the work tail follow from the one-trial rejection
bound and the affine pathwise work estimate. -/
def tridiagonalRetryWorkTransfer : Prop :=
  ∀ (n k p : ℕ), 2 ≤ n → 0 < k → k ≤ n →
    let bits := rngBits n k
    ∀ (reject : Set (TrialDraws n bits)) (work : (ℕ → TrialDraws n bits) → ℝ≥0∞)
      (C : ℝ≥0∞),
      trialDrawMeasure n bits reject ≤ ENNReal.ofReal (rejectionBound n) →
      let scale := C * (n : ℝ≥0∞) * k * p
      (∀ x, work x ≤ scale * (retryCount reject x + 1)) →
      let μ := streamMeasure (trialDrawMeasure n bits)
      ((∫⁻ x, work x ∂μ) ≤ 3 * scale) ∧
      (∀ m : ℕ, 0 < m → μ {x | scale * ((m : ℝ≥0∞) + 1) < work x} ≤
        ENNReal.ofReal (rejectionBound n) ^ m)

end SourceTargets

end NumStability.CertifiedTridiagonalEigenpairs
