import ComputationalMathematics.Analysis.FloatingPointArithmetic.UnboundedBinary.NativeEmptyBinComparison
import ComputationalMathematics.Source.CertifiedTridiagonalEigenpairs.BidiagonalSVDRunResourceModel

/-! Precision and complete work of the selected bidiagonal SVD. -/

open MeasureTheory
open scoped ENNReal

namespace NumStability.CertifiedTridiagonalEigenpairs.SourceTargets

open FloatingPointFormat.UnboundedBinary BidiagonalSVDRequest

/-- The complete work and workspace on the branch and bit law actually
selected by the stored input. The work includes the exact dispatch, native
preparation, the full auxiliary retry execution, and both output arrays. -/
def svdCompleteResources : Prop :=
  ∀ (n k p : ℕ) (hp : 2 ≤ p) (upper : Bool)
    (a : Fin (n + 1) → Word p hp) (b : Fin n → Word p hp) (I : Fin k ↪o Fin (n + 1))
    (hk : 1 ≤ k) (hguard : precisionGuard (n + 1) p),
    let cmp := EmptyBinScan.defaultComparison (svdLabelPrecision k p) (svdLabelPrecision_ge_two k p)
    let plan := prepareRun upper a b I cmp hk hguard
    (∫⁻ bits, plan.work bits ∂plan.bitMeasure) ≤ (200000 * ((n + 1) * k * p) : ℕ) ∧
    (∀ bits, plan.workspaceBound bits ≤ 500 * ((n + 1) + (n + 1) * k)) ∧
    (∀ c : ℝ, 0 < c → 1 - ENNReal.ofReal ((n + 1 : ℝ) ^ (-c)) ≤
      plan.bitMeasure {bits | plan.work bits ≤
        ((66000 * ((n + 1) * k * p) : ℕ) : ℝ≥0∞) *
          ((polynomialConfidenceTrials c : ℝ≥0∞) + 1)}) ∧
    (∀ bits, plan.work bits ≤ ((66000 * ((n + 1) * k * p) : ℕ) : ℝ≥0∞) *
      (plan.attemptCount bits + 1)) ∧
    plan.RespectsPrecision ∧
    (p ≤ plan.precision ∧ plan.precision ≤ svdWorkingPrecision (n + 1) k p ∧
      plan.precision ≤ 10 * p + 14) ∧
    (storedBidiagonal upper a b = 0 ∨ n = 0 → plan.precision = p)

end NumStability.CertifiedTridiagonalEigenpairs.SourceTargets
