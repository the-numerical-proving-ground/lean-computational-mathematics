import ComputationalMathematics.Analysis.Eigenvalues.DiagonalPerturbation
import ComputationalMathematics.Analysis.Probability.SymmetricUniform
import ComputationalMathematics.Source.CertifiedTridiagonalEigenpairs.RequestedAdjacentGaps.Target

/-! The probability of a small gap adjacent to any of the fixed requested ranks. -/

namespace NumStability.CertifiedTridiagonalEigenpairs

open scoped ENNReal

/-- The event that at least one adjacent gap touching a requested rank is at most `g`.
The one-based index of the gap starting at zero-based rank `j` is `j + 1`. -/
def requestedSmallGapEvent {n : ℕ} {S : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    (hS : S.IsHermitian) (J : Finset ℕ) (g : ℝ) : Set (Fin (n + 1) → ℝ) :=
  {v | ∃ j : Fin n, j.val + 1 ∈ requestedAdjacentGapIndices (n + 1) J ∧
    v ∈ hS.specifiedAdjacentGapEvent j g}

namespace SourceTargets

/-- The probability bound in Lemma `rand:gap`. The matrix has order `n + 1`,
and the probability measure is the product of the uniform laws on `[-δ, δ]`. -/
def requestedGapProbability : Prop :=
  ∀ (n : ℕ) (_ : 2 ≤ n + 1) (S : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (hS : S.IsHermitian) (J : Finset ℕ) (_ : J.Nonempty) (_ : J ⊆ Finset.Icc 1 (n + 1))
    (δ g : ℝ) (_ : 0 < δ) (_ : 0 < g),
    symmetricUniformProduct (n + 1) δ (requestedSmallGapEvent hS J g) ≤
      ENNReal.ofReal ((n + 1 : ℝ) * (requestedAdjacentGapIndices (n + 1) J).card * g / (2 * δ)) ∧
    ENNReal.ofReal ((n + 1 : ℝ) * (requestedAdjacentGapIndices (n + 1) J).card * g / (2 * δ)) ≤
      ENNReal.ofReal ((n + 1 : ℝ) * J.card * g / δ)

end SourceTargets

end NumStability.CertifiedTridiagonalEigenpairs
