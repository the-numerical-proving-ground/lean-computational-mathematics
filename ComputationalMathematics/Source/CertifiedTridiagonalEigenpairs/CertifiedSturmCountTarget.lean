import ComputationalMathematics.Analysis.Eigenvalues.TridiagonalSturmCount
import ComputationalMathematics.Analysis.FloatingPointArithmetic.UnboundedBinary.ClippedSturmSweep

/-!
# A certified Sturm count at linear precision

Lemma `scalar:count` of the selected tridiagonal eigenpairs paper. The
dimension is written `n + 1` so that the first row exists. The data and
shift are exactly represented at precision `q`. The count uses clipping at
`2⁻ʳ / 16`, and both enclosure endpoints use strict spectral counts.
-/

namespace NumStability.CertifiedTridiagonalEigenpairs

open FloatingPointFormat.UnboundedBinary
open ScalarWork

namespace SourceTargets

/-- Successful completion, the strict spectral bracket, and the work bound
for the rounded and clipped Sturm recurrence. -/
def certifiedSturmCount : Prop :=
  ∀ (n r q : ℕ) (hq : 2 ≤ q)
    (a : Fin (n + 1) → Word q hq) (b : Fin n → Word q hq) (x : Word q hq),
    let av : Fin (n + 1) → ℝ := fun i => (a i).value
    let bv : Fin n → ℝ := fun i => (b i).value
    let H := sturmTridiagonal av bv
    let spectrum := NoisyRankCertificate.ascendingEigenvalue (sturmTridiagonal_isHermitian av bv)
    let ε := unitRoundoff r
    let s := sturmClipThreshold r
    let d := clippedSturmPivots q hq r av bv x.value
    let result := clippedSturmSweep q hq r a b x
    let c := result.count
    2 ≤ r →
    r + 8 ≤ q →
    realMatrixOperatorNorm H ≤ 3 / 2 →
    (∀ i, |bv i| ≤ 1) →
    x.value ∈ Set.Icc (-2 : ℝ) 2 →
    (∀ i, Native q hq (d i) ∧ s ≤ |d i| ∧ d i ≠ 0) ∧
    c = (Finset.univ.filter (fun i => d i < 0)).card ∧
    NoisyRankCertificate.strictBelowCount spectrum (x.value - ε) ≤ c ∧
    c ≤ NoisyRankCertificate.strictBelowCount spectrum (x.value + ε) ∧
    work result.trace ≤ 13 * (n + 1) ∧
    TraceAllowed q result.trace ∧
    storage result.liveWords ≤ 14

end SourceTargets
end NumStability.CertifiedTridiagonalEigenpairs
