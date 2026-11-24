import ComputationalMathematics.Analysis.Eigenvalues.DiagonalPerturbation
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.WithDensity

/-! Statement of the fixed adjacent-rank gap estimate. -/

open MeasureTheory
open scoped ENNReal

namespace NumStability.CertifiedTridiagonalEigenpairs.SourceTargets

/-- Under independent real diagonal perturbations with densities bounded by
`ρ`, a specified increasing adjacent gap is at most `g` with probability at
most the matrix order times `ρ * g`. The product measure is the joint law. -/
def specifiedAdjacentGapProbability : Prop :=
  ∀ (n : ℕ) (_ : 2 ≤ n + 1)
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (hA : A.IsHermitian)
    (f : Fin (n + 1) → ℝ → ℝ≥0∞) (_ : ∀ i, Measurable (f i))
    (_ : ∀ i, IsProbabilityMeasure ((volume : Measure ℝ).withDensity (f i)))
    (ρ : ℝ) (_ : ∀ i, ∀ᵐ x ∂(volume : Measure ℝ), f i x ≤ ENNReal.ofReal ρ)
    (j : Fin n) (g : ℝ) (_ : 0 < g),
      (Measure.pi fun i => (volume : Measure ℝ).withDensity (f i))
        (hA.specifiedAdjacentGapEvent j g) ≤ ENNReal.ofReal ((n + 1) * ρ * g)

end NumStability.CertifiedTridiagonalEigenpairs.SourceTargets
