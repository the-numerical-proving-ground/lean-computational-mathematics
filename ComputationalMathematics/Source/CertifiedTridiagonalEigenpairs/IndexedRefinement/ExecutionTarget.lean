import ComputationalMathematics.Analysis.Eigenvalues.AscendingEigenvalueRoots
import ComputationalMathematics.Analysis.Eigenvalues.TridiagonalRefinementExecution

/-!
# Indexed refinement with a trace-free arithmetic loop

Lemma `scalar:refinement` concerns the stored midpoint returned after
`r + 4` updates. Rank `j : Fin (n + 1)` denotes the one-based rank
`j.val + 1`. The numerical loop carries its current endpoints, and a
separate interpretation of the same instructions measures its resource use.
-/

namespace NumStability.CertifiedTridiagonalEigenpairs.SourceTargets

open FloatingPointFormat.UnboundedBinary
open FloatingPointFormat.UnboundedBinary.PaddedRefinement (midpoint)

/-- Enclosure at every prefix, final accuracy, work, and peak workspace for
the trace-free rounded refinement. -/
def indexedRefinementExecution : Prop :=
  ∀ (n r q : ℕ) (hq : 2 ≤ q) (j : Fin (n + 1))
    (a : Fin (n + 1) → Word q hq) (b : Fin n → Word q hq),
    let av : Fin (n + 1) → ℝ := fun i => (a i).value
    let bv : Fin n → ℝ := fun i => (b i).value
    let H := sturmTridiagonal av bv
    let spectrum := NoisyRankCertificate.ascendingEigenvalue (sturmTridiagonal_isHermitian av bv)
    let ε := unitRoundoff r
    let measured := measuredTridiagonalRefinement r j a b
    2 ≤ r →
    r + 8 ≤ q →
    realMatrixOperatorNorm H ≤ 3 / 2 →
    (∀ i, |bv i| ≤ 1) →
    measured.1 = runTridiagonalRefinement r j a b ∧
    (∀ m ≤ r + 4,
      let interval := runTridiagonalRefinementInterval r j a b m
      let x := midpoint interval
      interval.Contains (spectrum j) ∧
        interval.lower.value ≤ x.value ∧ x.value ≤ interval.upper.value) ∧
    |(runTridiagonalRefinement r j a b).value - spectrum j| ≤ (423 / 256) * ε ∧
    (423 / 256) * ε < 2 * ε ∧
    measured.2.work ≤ 68 * (n + 1) * r ∧
    measured.2.peakWords ≤ 26 * (n + 1)

end NumStability.CertifiedTridiagonalEigenpairs.SourceTargets
