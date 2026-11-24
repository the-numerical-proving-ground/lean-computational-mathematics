import ComputationalMathematics.Analysis.FloatingPointArithmetic.UnboundedBinary.NativeEmptyBinComparison
import ComputationalMathematics.Source.CertifiedTridiagonalEigenpairs.BidiagonalSVDRunAccuracy
import ComputationalMathematics.Source.CertifiedTridiagonalEigenpairs.BidiagonalSVDRunResourceModel
import ComputationalMathematics.Source.CertifiedTridiagonalEigenpairs.TridiagonalConfidence.Target

/-! The selected bidiagonal singular triplet guarantee for the native execution. -/

open MeasureTheory
open scoped ENNReal

namespace NumStability.CertifiedTridiagonalEigenpairs.SourceTargets

open FloatingPointFormat.UnboundedBinary BidiagonalSVDRequest

/-- Theorem `svd:theorem` for upper and lower bidiagonal bands and ordered
requested ranks. The output, probability, and costs use one prepared solver. -/
def selectedBidiagonalSingularTriplets : Prop :=
  ∃ C_W C_S C_hp : ℕ, 0 < C_W ∧ 0 < C_S ∧ 0 < C_hp ∧
    ∀ (n k p : ℕ) (hp : 2 ≤ p) (upper : Bool)
      (a : Fin (n + 1) → Word p hp) (b : Fin n → Word p hp)
      (I : Fin k ↪o Fin (n + 1)) (hk : 1 ≤ k) (hguard : precisionGuard (n + 1) p),
      let d := n + 1
      let B := storedBidiagonal upper a b
      let q := svdWorkingPrecision d k p
      let plan := prepareRun upper a b I (EmptyBinScan.defaultComparison _ _) hk hguard
      let μ := plan.bitMeasure
      let W := plan.work
      (∀ᵐ bits ∂μ, ∃ out, plan.run bits = some out) ∧
      (∀ bits out, plan.run bits = some out → RunAccuracy B I out.triplets) ∧
      (∫⁻ bits, W bits ∂μ) ≤ ((C_W * d * k * p : ℕ) : ℝ≥0∞) ∧
      (∀ bits, plan.workspaceBound bits ≤ C_S * (d + d * k)) ∧
      (∀ c : ℝ, 0 < c → 1 - ENNReal.ofReal ((d : ℝ) ^ (-c)) ≤
        μ {bits | W bits ≤ manuscriptWorkCutoff C_hp d k p ⌈c / 2⌉}) ∧
      q = 4 * p + 3 * Nat.clog 2 d + 3 * Nat.clog 2 k + 56 ∧
      plan.RespectsPrecision ∧ plan.precision ≤ q ∧ (2 ≤ d → q ≤ 10 * p + 14) ∧
      (B = 0 ∨ n = 0 → plan.precision = p ∧
        ∃ exactOut, bidiagonalExactBranch a b I = some exactOut ∧
          ∀ bits, plan.run bits = some (exactPackedOutput exactOut))

end NumStability.CertifiedTridiagonalEigenpairs.SourceTargets
