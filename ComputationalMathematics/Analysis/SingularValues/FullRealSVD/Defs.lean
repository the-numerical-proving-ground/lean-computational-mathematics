import ComputationalMathematics.Algorithms.RandomizedLinearAlgebra.LowRankApproximation.ColumnSketches.Core
import Mathlib.Data.Fin.Rev

/-!
# Ascending complete real singular spectra

Reverse the entire canonical right-Gram singular list, retaining all zero
entries and multiplicities. This is an exact mathematical spectrum.
-/

namespace NumStability

/-- The canonical ascending singular spectrum of a real square matrix. -/
noncomputable def ascendingRealSpectrum {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) : ℝ :=
  rectSingularValue A i.rev

end NumStability
