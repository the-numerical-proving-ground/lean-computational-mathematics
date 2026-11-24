import ComputationalMathematics.Source.CertifiedTridiagonalEigenpairs.RoundedVectorLocal.Path
import Mathlib.Analysis.CStarAlgebra.Matrix

namespace NumStability.CertifiedTridiagonalEigenpairs

open scoped Matrix Matrix.Norms.L2Operator
open FloatingPointFormat.UnboundedBinary

namespace SourceTargets

/-- Positive pivots and structured backward error for the actual sweeps and
twist (vec:local). The input a is the diagonal after exact subtraction of the
label and before rounding. The direct bounds on a, b, η and the working
roundoff are the local bounds used in the paper's proof. -/
def roundedVectorStructuredBackward : Prop :=
  ∀ (n q : ℕ) (_hn : 2 ≤ n) (hq : 2 ≤ q) (a b : ℕ → ℝ) (η : ℝ),
    unitRoundoff q ≤ 1 / 128 → 0 < η → η ≤ 1 / 2 → Native q hq η →
    (∀ i < n, |a i| ≤ 5) → (∀ i, i + 1 < n → |b i| ≤ 1) →
    (∀ i : Fin n,
      let left := vectorLeftSweep q hq a b η i.val
      let right := vectorRightSweep q hq n a b η i.val
      VectorPivotBounds η left ∧ VectorPivotBounds η right ∧
        0 < vectorSquaredModulus q hq left.1 left.2 ∧
        0 < vectorSquaredModulus q hq right.1 right.2) ∧
    ∀ r : Fin n,
      let twist := vectorSweepTwist q hq n a b η r
      let d := vectorAssemblyPivot q hq n a b η r
      let K := vectorShiftedMatrix n a b η
      η ≤ twist.2 ∧ 0 < vectorSquaredModulus q hq twist.1 twist.2 ∧
      ∃ (E : Matrix (Fin n) (Fin n) ℂ) (β : Fin n → ℂ),
        let L := 1 + rootedEliminationPart r (vectorParent r) β d
        Eᵀ = E ∧
        (∀ i j : Fin n, i.val + 1 < j.val ∨ j.val + 1 < i.val → E i j = 0) ∧
        K + E = L * Matrix.diagonal d * Lᵀ ∧
        IsUnit (K + E) ∧ ((K + E)⁻¹) r r = (vectorComplexPivot twist)⁻¹ ∧
        ‖E‖ ≤ 40 * unitRoundoff q ∧
        (∀ j : Fin n, j ≠ r → (K + E) (vectorParent r j) j = β j) ∧
        ∀ i j : Fin n, i.val + 1 = j.val →
          let edge := (K + E) i j
          (b i.val = 0 → edge = 0) ∧
          (b i.val ≠ 0 → ‖edge / (b i.val : ℂ) - 1‖ ≤ 11 * unitRoundoff q)

end SourceTargets

end NumStability.CertifiedTridiagonalEigenpairs
