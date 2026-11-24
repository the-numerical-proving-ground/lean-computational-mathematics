import ComputationalMathematics.Source.CertifiedTridiagonalEigenpairs.FiniteTrial.Target
import ComputationalMathematics.Source.CertifiedTridiagonalEigenpairs.ScalingTransfer

/-!
# Requested label refinement on the accepted trial

The tighter indexed refinement reads the stored diagonal from the accepted result
and the same subdiagonal used in the trial. An output label rounds the refined
word to precision `p` and shifts its exponent by the normalization exponent.
-/

namespace NumStability.CertifiedTridiagonalEigenpairs

open FloatingPointFormat.UnboundedBinary NoisyRankCertificate ScalarWork

/-- A trial result that passed its rounded gate. -/
abbrev AcceptedTrial (n : ℕ) (J : Finset ℕ) (p : ℕ) :=
  {trial : FiniteTrialResult n J p // trial.accepted = true}

/-- A rank requested for refinement after acceptance. -/
abbrev RequestedTrialRank (n : ℕ) (J : Finset ℕ) :=
  {j : Fin (n + 1) // j.val + 1 ∈ J}

/-- Execute the fixed-length native refinement at tolerance `η/2`, on the
accepted diagonal and the original stored subdiagonal. -/
noncomputable def acceptedRefinement {n p : ℕ} {J : Finset ℕ}
    (trial : AcceptedTrial n J p) (b : Fin n → TrialWord n J p)
    (j : RequestedTrialRank n J) :=
  tridiagonalRefinement (vectorToleranceExponent (n + 1) J.card p + 1) j.val
    (fun i => trial.val.diagonal[i.val]) b

/-- The working-precision label used by the vector stage. -/
noncomputable def acceptedRefinedLabel {n p : ℕ} {J : Finset ℕ}
    (trial : AcceptedTrial n J p) (b : Fin n → TrialWord n J p)
    (j : RequestedTrialRank n J) : TrialWord n J p :=
  (acceptedRefinement trial b j).label

/-- Round the refined label to a native output word, then scale it exactly. -/
noncomputable def acceptedOutputLabel {n p : ℕ} {J : Finset ℕ}
    (hp : 2 ≤ p) (trial : AcceptedTrial n J p) (b : Fin n → TrialWord n J p)
    (j : RequestedTrialRank n J) (r : ℤ) : Word p hp :=
  rescaledLabel p hp r (acceptedRefinedLabel trial b j).value

namespace SourceTargets

/-- The numerical premises available after the actual finite gate and tighter
label refinement, together with the error and exact scaling of the native label.
The vector routine receives the refined label at working precision. -/
def acceptedIndexedLabels : Prop :=
  ∀ (n p : ℕ) (J : Finset ℕ) (hp : 2 ≤ p)
    (a : Fin (n + 1) → TrialWord n J p) (b : Fin n → TrialWord n J p),
    2 ≤ n + 1 → precisionGuard (n + 1) p → J.Nonempty → J ⊆ Finset.Icc 1 (n + 1) →
    (∀ i, |(a i).value| ≤ 1 / 4) → (∀ i, |(b i).value| ≤ 1 / 4) →
    ∀ (words : Fin (n + 1) → FairBitWord (rngBits (n + 1) J.card))
      (haccepted : (trialRun n p J a b words).accepted = true)
      (j : RequestedTrialRank n J) (r : ℤ),
    let trial : AcceptedTrial n J p := ⟨trialRun n p J a b words, haccepted⟩
    let av : Fin (n + 1) → ℝ := fun i => (a i).value
    let dv : Fin (n + 1) → ℝ := fun i => (trial.val.diagonal[i.val]).value
    let bv : Fin n → ℝ := fun i => (b i).value
    let S := sturmTridiagonal av bv
    let M := sturmTridiagonal dv bv
    let spectrumS := ascendingEigenvalue (sturmTridiagonal_isHermitian av bv)
    let spectrumM := ascendingEigenvalue (sturmTridiagonal_isHermitian dv bv)
    let q := workingPrecision (n + 1) J.card p
    let h := vectorToleranceExponent (n + 1) J.card p
    let eta := vectorTolerance (n + 1) J.card p
    let Δ := certifiedGap (n + 1) J.card p
    let omega := workingRoundoff (n + 1) J.card p
    let u := unitRoundoff p
    let theta := (acceptedRefinedLabel trial b j).value
    let mu := roundToEven p hp theta
    let R := (2 : ℝ) ^ r
    let result := acceptedRefinement trial b j
    let output := acceptedOutputLabel hp trial b j r
    M = trialMatrix a b words ∧
    realMatrixOperatorNorm (M - S) ≤ u / 128 ∧ realMatrixOperatorNorm M < 1 ∧
    (∀ i l, i ≠ l → M i l = S i l) ∧
    (∀ i : Fin (n + 1), i ≠ j.val → Δ < |spectrumM i - spectrumM j.val|) ∧
    gapToleranceExponent (n + 1) J.card p + 8 ≤ q ∧
    q - h = p / 2 - (Nat.clog 2 (n + 1) + 3) / 4 + 9 ∧ 12 ≤ q - h ∧
    h + 9 ≤ q ∧ eta / 2 = unitRoundoff (h + 1) ∧
    0 < eta ∧ eta < 1 / 2 ∧
    eta ≤ Δ * Real.sqrt u / (16 * ((n + 1 : ℕ) : ℝ) ^ (1 / 4 : ℝ)) ∧
    ((n + 1 : ℕ) : ℝ) * Δ < 1 / 8 ∧
    omega ≤ eta / 4096 ∧ omega = u * Δ / 8192 ∧
    ((n + 1 : ℕ) : ℝ) * omega ≤ u / 65536 ∧
    |theta - spectrumM j.val| ≤ (423 / 256) * (eta / 2) ∧
    |theta - spectrumM j.val| < eta ∧
    work result.trace ≤ 68 * (n + 1) * (h + 1) ∧ TraceAllowed q result.trace ∧
    storage result.liveWords ≤ 26 * (n + 1) ∧
    |mu - spectrumM j.val| ≤ eta + u * (1 + eta) ∧
    |mu - spectrumM j.val| < 2 * u ∧ |mu| < 2 ∧
    |mu - spectrumS j.val| ≤ eta + u * (1 + eta) + u / 128 ∧
    |mu - spectrumS j.val| < 2 * u ∧
    output.value = R * mu ∧ |output.value - R * spectrumS j.val| < R * (2 * u)

end SourceTargets
end NumStability.CertifiedTridiagonalEigenpairs
