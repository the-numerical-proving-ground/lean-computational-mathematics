import ComputationalMathematics.Source.CertifiedTridiagonalEigenpairs.TridiagonalEigenpairRun

/-! Source contract for the post-acceptance numerical execution of §3. -/

namespace NumStability.CertifiedTridiagonalEigenpairs.SourceTargets

open FloatingPointFormat.UnboundedBinary NoisyRankCertificate

/-- On the nontrivial branch, each returned pair uses the result of the tighter
refinement at its requested rank and the vector computed from that same label
and stored matrix. The gap certification is an input to the vector theorem.
The numerical vector computation reads the label, the shift, and the bands. -/
def tridiagonalPostacceptExecution : Prop :=
  ∀ (n p : ℕ) (J : Finset ℕ) (hp : 2 ≤ p)
    (a : Fin (n + 1) → Word p hp) (b : Fin n → Word p hp)
    (bits : ℕ → GateBits n J) (guard : precisionGuard (n + 1) p)
    (hJ : J.Nonempty) (valid : J ⊆ Finset.Icc 1 (n + 1))
    (out : NativeAcceptedEigenpairs n p J hp),
    runTridiagonalEigenpairs a b bits guard hJ valid = some (.refined out) →
    let r := out.scaleExponent
    let accepted := out.accepted
    let aW := fun i => normalizeTrialWord (J := J) r (a i)
    let bW := fun i => normalizeTrialWord (J := J) r (b i)
    let M := accepted.readMatrix bW
    let I := requestedRankOrder valid
    let N := n + 1
    let q := workingPrecision N J.card p
    let h := vectorToleranceExponent N J.card p
    let η := vectorTolerance N J.card p
    let Δ := certifiedGap N J.card p
    let hq := workingPrecision_ge_two N J.card p
    let shift := (acceptedShiftWord n p J).value
    2 ≤ N ∧ storedTridiagonal a b ≠ 0 ∧ normalizationExponent a b = some r ∧
    accepted.trial.val = trialRun n p J aW bW (bits accepted.index) ∧
    M = trialMatrix aW bW (bits accepted.index) ∧
    (∀ i : Fin N, (∃ j : Fin J.card, I j = i) ↔ i.val + 1 ∈ J) ∧
    h + 9 ≤ q ∧ η / 2 = unitRoundoff (h + 1) ∧ shift = η ∧
    ∀ j : Fin J.card,
      let θ := runTridiagonalRefinement (h + 1) (I j)
        (fun i => accepted.trial.val.diagonal[i.val]) bW
      let spectrum := ascendingEigenvalue (accepted.matrix_isHermitian bW)
      let imag := vectorComputedImaginaryArray hq (Nat.succ_pos n) M θ.value shift
      |θ.value - spectrum (I j)| ≤ η ∧
      (∀ i ≠ I j, Δ < |spectrum i - spectrum (I j)|) ∧
      ∃ hx : Word.euclidean imag.get ≠ 0,
        0 < (Word.roundedNormScan imag).value ∧
        out.pairs[j.val].column = Word.normalizeToScan p hp imag hx ∧
        out.pairs[j.val].label.value = (2 : ℝ) ^ r * roundToEven p hp θ.value

end NumStability.CertifiedTridiagonalEigenpairs.SourceTargets
