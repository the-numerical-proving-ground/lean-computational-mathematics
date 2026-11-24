import ComputationalMathematics.Analysis.FunctionalCalculus.Resolvent.SpectralAveraging
import Mathlib.Probability.Kernel.Basic

/-! The rank-one spectral averaging statement and its density consequences. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace NumStability.CertifiedTridiagonalEigenpairs

/-- A bounded real interval with either choice of membership at each endpoint. -/
def IsBoundedRealInterval (I : Set ℝ) : Prop :=
  ∃ a b : ℝ, a ≤ b ∧ Set.Ioo a b ⊆ I ∧ I ⊆ Set.Icc a b

/-- The coordinate diagonal of the interval spectral projection after a real
shift in coordinate `i`. This diagonal is real. -/
noncomputable def rankOneCoordinateProjectionWeight {n : ℕ} {C : Matrix (Fin n) (Fin n) ℂ}
    (hC : C.IsHermitian) (i : Fin n) (I : Set ℝ) (t : ℝ) : ℝ :=
  (matrixSpectralProjection (isHermitian_add_diagonal_single hC i t) I i i).re

namespace SourceTargets

/-- The Lebesgue integral is bounded by the interval length. A bounded
perturbation density gives the corresponding expectation bound, also almost
surely under a supplied conditional law when the conditioning fixes the matrix
and interval. -/
def rankOneSpectralAveraging.{u} : Prop :=
  ∀ (n : ℕ) (i : Fin n),
    (∀ (C : Matrix (Fin n) (Fin n) ℂ) (hC : C.IsHermitian)
      (I : Set ℝ) (_ : IsBoundedRealInterval I),
      (∫ t : ℝ, rankOneCoordinateProjectionWeight hC i I t) ≤ (volume I).toReal ∧
      ∀ (ρ : ℝ≥0) (d : ℝ → ℝ≥0∞) (_ : Measurable d)
        (_ : IsProbabilityMeasure ((volume : Measure ℝ).withDensity d))
        (_ : ∀ᵐ t ∂(volume : Measure ℝ), d t ≤ (ρ : ℝ≥0∞)),
        (∫ t : ℝ, rankOneCoordinateProjectionWeight hC i I t
          ∂(volume : Measure ℝ).withDensity d) ≤ (ρ : ℝ) * (volume I).toReal) ∧
    ∀ (Ω : Type u) [MeasurableSpace Ω] (ν : Measure Ω) (_ : IsProbabilityMeasure ν)
      (κ : Kernel Ω ℝ) (_ : IsMarkovKernel κ)
      (C : Ω → Matrix (Fin n) (Fin n) ℂ) (hC : ∀ ω, (C ω).IsHermitian)
      (I : Ω → Set ℝ) (_ : ∀ ω, IsBoundedRealInterval (I ω)) (ρ : ℝ≥0)
      (_ : ∀ᵐ ω ∂ν, ∃ d : ℝ → ℝ≥0∞, Measurable d ∧
        (∀ᵐ t ∂(volume : Measure ℝ), d t ≤ (ρ : ℝ≥0∞)) ∧
        κ ω = (volume : Measure ℝ).withDensity d),
      ∀ᵐ ω ∂ν, (∫ t : ℝ, rankOneCoordinateProjectionWeight (hC ω) i (I ω) t ∂κ ω) ≤
        (ρ : ℝ) * (volume (I ω)).toReal

end SourceTargets

end NumStability.CertifiedTridiagonalEigenpairs
