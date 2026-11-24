import ComputationalMathematics.Analysis.Eigenvalues.AscendingEigenvalueRoots
import ComputationalMathematics.Analysis.Eigenvalues.TridiagonalSturmCount
import ComputationalMathematics.Analysis.FloatingPointArithmetic.UnboundedBinary.ClippedSturmExecution

/-!
# Certified Sturm count with a trace-free loop

The count in Lemma `scalar:count` is obtained from a loop whose mutable row
state consists of a stored pivot and a counter. A separate recording
interpretation of its row instructions supplies the work and simultaneous
live-word charges.
-/

namespace NumStability.CertifiedTridiagonalEigenpairs

open FloatingPointFormat.UnboundedBinary
open ScalarWork

namespace SourceTargets

/-- Successful completion, the strict spectral bracket, and resource bounds
for the rounded and clipped Sturm recurrence as executed by the trace-free loop. -/
def certifiedSturmCountExecution : Prop :=
  ∀ (n r q : ℕ) (hq : 2 ≤ q)
    (a : Fin (n + 1) → Word q hq) (b : Fin n → Word q hq) (x : Word q hq),
    let av : Fin (n + 1) → ℝ := fun i => (a i).value
    let bv : Fin n → ℝ := fun i => (b i).value
    let H := sturmTridiagonal av bv
    let spectrum := NoisyRankCertificate.ascendingEigenvalue (sturmTridiagonal_isHermitian av bv)
    let ε := unitRoundoff r
    let s := sturmClipThreshold r
    let d := clippedSturmPivots q hq r av bv x.value
    let result := runClippedSturmSweep q hq r a b x
    let recording := recordedClippedSturmExecution q hq r a b x
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
    work recording.2.trace ≤ 13 * (n + 1) ∧
    TraceAllowed q recording.2.trace ∧
    storage recording.2.liveWords ≤ 14 ∧
    recording.1 = result

end SourceTargets
end NumStability.CertifiedTridiagonalEigenpairs
