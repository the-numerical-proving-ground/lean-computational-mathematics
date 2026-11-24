import ComputationalMathematics.Analysis.Eigenvalues.TridiagonalRefinement

/-!
# Rounded refinement of an indexed eigenvalue

Lemma `scalar:refinement` of the certified tridiagonal eigenpairs paper.
A rank `j : Fin (n + 1)` denotes the paper's one-based rank `j.val + 1`
in dimension `n + 1`. All matrix entries and the returned label are
stored at precision `q`.
-/

namespace NumStability.CertifiedTridiagonalEigenpairs.SourceTargets

open FloatingPointFormat.UnboundedBinary ScalarWork
open FloatingPointFormat.UnboundedBinary.PaddedRefinement (midpoint)

/-- The fixed `r + 4` clipped-count updates and final rounded midpoint
preserve the enclosure and deliver the stated accuracy and resource bounds. -/
def indexedRefinement : Prop :=
  ∀ (n r q : ℕ) (hq : 2 ≤ q) (j : Fin (n + 1))
    (a : Fin (n + 1) → Word q hq) (b : Fin n → Word q hq),
    let av : Fin (n + 1) → ℝ := fun i => (a i).value
    let bv : Fin n → ℝ := fun i => (b i).value
    let H := sturmTridiagonal av bv
    let spectrum := NoisyRankCertificate.ascendingEigenvalue (sturmTridiagonal_isHermitian av bv)
    let ε := unitRoundoff r
    let result := tridiagonalRefinement r j a b
    2 ≤ r →
    r + 8 ≤ q →
    realMatrixOperatorNorm H ≤ 3 / 2 →
    (∀ i, |bv i| ≤ 1) →
    (∀ m ≤ r + 4,
      let interval := tridiagonalRefinement_intervalAt r j a b m
      let x := midpoint interval
      interval.Contains (spectrum j) ∧
        interval.lower.value ≤ x.value ∧ x.value ≤ interval.upper.value) ∧
    |result.label.value - spectrum j| ≤ (423 / 256) * ε ∧
    (423 / 256) * ε < 2 * ε ∧
    work result.trace ≤ 68 * (n + 1) * r ∧
    TraceAllowed q result.trace ∧
    storage result.liveWords ≤ 26 * (n + 1)

end NumStability.CertifiedTridiagonalEigenpairs.SourceTargets
