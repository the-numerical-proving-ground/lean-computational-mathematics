import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

/-!
# Retry thresholds for the tridiagonal eigensolver

The two thresholds in the work-confidence corollary use the same algorithm and
one-trial rejection bound. A tail estimate for runtime therefore suffices for
both confidence statements.
-/

open MeasureTheory
open scoped ENNReal

namespace NumStability.CertifiedTridiagonalEigenpairs

/-- The paper's uniform bound on the probability of rejecting one trial. -/
noncomputable def trialRejectionBound (N : ℕ) : ℝ := 3 / (2048 * (N : ℝ) ^ 2)

/-- Number of trials used in the polynomial confidence bound. -/
noncomputable def polynomialConfidenceTrials (c : ℝ) : ℕ := ⌈c / 2⌉₊

/-- Number of trials used for confidence `1 - ε`. -/
noncomputable def arbitraryConfidenceTrials (N : ℕ) (ε : ℝ) : ℕ :=
  ⌈Real.log (1 / ε) / Real.log (2048 * (N : ℝ) ^ 2 / 3)⌉₊

namespace SourceTargets

/-- The probability conversion in the tridiagonal work-confidence corollary.
The hypothesis is the full execution's work-tail inequality at one common scale. -/
def tridiagonalWorkConfidenceTransfer : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (work : Ω → ℝ≥0∞), Measurable work →
    ∀ (n k p N : ℕ) (C : ℝ≥0∞), 0 < n → n ≤ N →
      let scale := C * (n : ℝ≥0∞) * k * p
      (∀ m : ℕ, 0 < m → μ {x | scale * ((m : ℝ≥0∞) + 1) < work x} ≤
        ENNReal.ofReal (trialRejectionBound N) ^ m) →
      (∀ c : ℝ, 0 < c → 1 - ENNReal.ofReal ((n : ℝ) ^ (-c)) ≤
        μ {x | work x ≤ scale * ((polynomialConfidenceTrials c : ℝ≥0∞) + 1)}) ∧
      (∀ ε : ℝ, 0 < ε → ε < 1 → 1 - ENNReal.ofReal ε ≤
        μ {x | work x ≤ scale * ((arbitraryConfidenceTrials N ε : ℝ≥0∞) + 1)})

end SourceTargets

end NumStability.CertifiedTridiagonalEigenpairs
