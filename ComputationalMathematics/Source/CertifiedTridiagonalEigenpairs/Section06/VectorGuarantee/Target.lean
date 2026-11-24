import ComputationalMathematics.Analysis.FloatingPointArithmetic.UnboundedBinary.PositivePrecision
import ComputationalMathematics.Source.CertifiedTridiagonalEigenpairs.Section06.VectorExecutionWork

/-! # Accuracy and work of the Section 6 vector computation -/

open Matrix
open scoped Matrix.Norms.L2Operator

namespace NumStability.CertifiedTridiagonalEigenpairs.SourceTargets

open FloatingPointFormat.UnboundedBinary ScalarWork

/-- Theorem 6.1 (vec:accuracy). Reverse the descending Hermitian spectrum to
use increasing indices. The gap inequality over all other spectral indices
includes simplicity of the selected eigenvalue. The positive precision inputs
are retained, and the numerical guards imply the floors needed by the word
implementation.

Work and storage use the scalar charges for the cached passes at the selected
row, including the normalization and conversion. The charge lists are used
only for the mathematical bounds. The stored output is the actual computed
vector of precision-p words. -/
def vectorGuarantee : Prop :=
  ∀ (n p q : ℕ) (hn : 2 ≤ n) (hp : 0 < p) (hq : 0 < q)
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsSymm)
    (j : Fin n) (v : EuclideanSpace ℝ (Fin n)) (shift η Δ : ℝ),
    let eigenvalue (i : Fin n) :=
      (MatrixResolvent.isHermitian_map_ofReal hA).eigenvalues i.rev
    let u := unitRoundoff p
    let ω := unitRoundoff q
    ‖A‖ ≤ 2 →
    (∀ i k : Fin n, i.val + 1 < k.val ∨ k.val + 1 < i.val → A i k = 0) →
    (∀ i k : Fin n, i.val + 1 = k.val → |A i k| ≤ 1) →
    (∀ i k : Fin n, NativeAt q hq (A i k)) →
    NativeAt q hq shift →
    ‖v‖ = 1 →
    A *ᵥ v.ofLp = eigenvalue j • v.ofLp →
    0 < Δ →
    (∀ i ≠ j, Δ ≤ |eigenvalue i - eigenvalue j|) →
    (n : ℝ) * u ≤ 1 / 128 →
    (∃ m : ℤ, η = (2 : ℝ) ^ m) →
    |shift - eigenvalue j| ≤ η →
    η ≤ min (1 / 2) (Δ * Real.sqrt u / (16 * (n : ℝ) ^ (1 / 4 : ℝ))) →
    ω ≤ min (η / 4096) (min (u * Δ / 8192) (u / (65536 * (n : ℝ)))) →
    ∃ (hp₂ : 2 ≤ p) (hq₂ : 2 ≤ q),
      let hn₀ : 0 < n := by omega
      let a := vectorInputDiagonal A shift
      let b := vectorInputEdge A
      let run := vectorCachedExecution q hq₂ n hn₀ a b η
      let r := run.root
      let yHat := vectorComputedImaginaryArray hq₂ hn₀ A shift η
      let trace := vectorExecutionTrace q p r
      let liveWords := vectorExecutionLiveWords r
      r = vectorSelectedIndex q hq₂ n hn₀ a b η ∧
      (∀ i : Fin n, (yHat.get i).value = (run.column.get i).im) ∧
      vectorPivotDivisorsPositive n q hq₂ a b η ∧
      (∀ i : Fin n, i ≠ r →
        let edge := vectorOutwardEdge q hq₂ n a b η r i 0
        0 < vectorSquaredModulus q hq₂ edge.pivotRe edge.pivotNegIm) ∧
      work trace ≤ 166 * n ∧ TraceAllowed q trace ∧ storage liveWords ≤ 31 * n ∧
      ∃ hx : Word.euclidean yHat.get ≠ 0,
        0 < (Word.roundedNormScan yHat).value ∧
        let vHat := Word.euclidean (vectorComputedOutput hp₂ hq₂ hn₀ A shift η hx)
        min ‖vHat + v‖ ‖vHat - v‖ ≤ 4 * u

end NumStability.CertifiedTridiagonalEigenpairs.SourceTargets
