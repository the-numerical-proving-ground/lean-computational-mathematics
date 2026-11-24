import ComputationalMathematics.Source.CertifiedTridiagonalEigenpairs.AcceptedOutput.Guarantees
import ComputationalMathematics.Source.CertifiedTridiagonalEigenpairs.AcceptedOutput.PerRank
import ComputationalMathematics.Source.CertifiedTridiagonalEigenpairs.AcceptedOutput.RequestedRanks
import ComputationalMathematics.Source.CertifiedTridiagonalEigenpairs.AcceptedOutput.StoredBands
import ComputationalMathematics.Source.CertifiedTridiagonalEigenpairs.Retry.NormalizedInput

/-! The native return loop and its deterministic guarantees for the nontrivial branch. -/

namespace NumStability.CertifiedTridiagonalEigenpairs

open Matrix WithLp NoisyRankCertificate FloatingPointFormat.UnboundedBinary
open scoped Matrix.Norms.L2Operator

noncomputable section

variable {n p : ℕ} {J : Finset ℕ} {hp : 2 ≤ p}

/-- One label and its corresponding column, both stored at output precision. -/
structure NativeReturnedEigenpair (N p : ℕ) (hp : 2 ≤ p) where
  label : Word p hp
  column : Vector (Word p hp) N

/-- The first accepted trial and the native outputs in increasing requested rank order. -/
structure NativeAcceptedEigenpairs (n p : ℕ) (J : Finset ℕ) (hp : 2 ≤ p) where
  scaleExponent : ℤ
  accepted : RetryResult n J p
  pairs : Vector (NativeReturnedEigenpair (n + 1) p hp) J.card

/-- Read the native labels in array order. -/
def NativeAcceptedEigenpairs.labels (out : NativeAcceptedEigenpairs n p J hp) : Fin J.card → ℝ :=
  fun j => out.pairs[j.val].label.value

/-- Read the native eigenvector array as a real matrix. -/
def NativeAcceptedEigenpairs.columns (out : NativeAcceptedEigenpairs n p J hp) :
    Matrix (Fin (n + 1)) (Fin J.card) ℝ :=
  .of fun i j => (out.pairs[j.val].column.get i).value

variable (aW : Fin (n + 1) → TrialWord n J p) (bW : Fin n → TrialWord n J p)
  (bits : ℕ → GateBits n J) (trial : RetryResult n J p)
  (hn : 2 ≤ n + 1) (hguard : precisionGuard (n + 1) p)
  (hJ : J.Nonempty) (hJvalid : J ⊆ Finset.Icc 1 (n + 1))
  (ha : ∀ i, |(aW i).value| ≤ 1 / 4) (hb : ∀ i, |(bW i).value| ≤ 1 / 4)
  (htrial : retryRun aW bW bits = some trial)

include hp hn hguard hJ hJvalid ha hb htrial in
private theorem acceptedImaginary_ne_zero (j : RequestedTrialRank n J) :
    Word.euclidean (vectorComputedImaginary (workingPrecision_ge_two (n + 1) J.card p)
      (Nat.succ_pos n) (trial.readMatrix bW) (runAcceptedRefinement trial.trial bW j).value
      (acceptedShiftWord n p J).value) ≠ 0 := by
  rw [trial.readMatrix_eq]
  exact Classical.choose
    (runAcceptedVector_accuracy aW bW bits trial hp hn hguard hJ hJvalid ha hb htrial j)

include hp hn hguard hJ hJvalid ha hb htrial in
/-- Refine once and run one vector solve for each marked rank. The working label is
used by the vector solve and by the single output rounding. The temporary imaginary
vector is normalized in one native pass before the next rank is processed. -/
def acceptedOutputLoop (r : ℤ) : NativeAcceptedEigenpairs n p J hp :=
  let ranks := requestedRankArray J hJvalid
  let M := trial.readMatrix bW
  let η := acceptedShiftWord n p J
  let pairs := Vector.ofFn fun i =>
    let j := ranks.get i
    let θ := runAcceptedRefinement trial.trial bW j
    let imag := vectorComputedImaginaryArray (workingPrecision_ge_two (n + 1) J.card p)
      (Nat.succ_pos n) M θ.value η.value
    let column := Word.normalizeToScan p hp imag
      (acceptedImaginary_ne_zero (hp := hp) aW bW bits trial hn hguard hJ hJvalid ha hb htrial j)
    ⟨rescaledLabel p hp r θ.value, column⟩
  ⟨r, trial, pairs⟩

private theorem vectorTolerance_doubled_lt_gap (N k p : ℕ) :
    2 * vectorTolerance N k p < certifiedGap N k p := by
  have hΔ : 0 < certifiedGap N k p := by
    rw [certifiedGap_eq_roundoff]
    exact unitRoundoff_pos _
  have hr : unitRoundoff ((p + 1) / 2) ≤ 1 := by
    unfold unitRoundoff
    simpa only [zpow_zero] using
      (zpow_le_zpow_right₀ (a := (2 : ℝ)) (by norm_num)
        (neg_nonpos.mpr (by positivity : (0 : ℤ) ≤ (((p + 1) / 2 : ℕ) : ℤ))))
  have hN : (1 : ℝ) ≤ (quarterPowerOfTwo N : ℝ) := by
    exact_mod_cast (show 1 ≤ quarterPowerOfTwo N from Nat.succ_le_of_lt (by unfold quarterPowerOfTwo; positivity))
  have h := mul_le_mul_of_nonneg_left hr hΔ.le
  have ht : vectorTolerance N k p ≤ certifiedGap N k p / 16 := by
    unfold vectorTolerance
    apply div_le_div₀ (by positivity : 0 ≤ certifiedGap N k p)
      (by simpa only [mul_one] using h) (by norm_num)
    linarith
  linarith

/-- The numerical loop has its source accuracy on every successful run with
the supported nonzero input and selected normalization exponent. -/
theorem acceptedOutputLoop_accuracy (a : Fin (n + 1) → Word p hp) (b : Fin n → Word p hp)
    (r : ℤ) (hr : normalizationExponent a b = some r)
    (haW : ∀ i, aW i = normalizeTrialWord r (a i))
    (hbW : ∀ i, bW i = normalizeTrialWord r (b i)) :
    let out := acceptedOutputLoop (hp := hp) aW bW bits trial hn hguard hJ hJvalid ha hb htrial r
    let T := storedTridiagonal a b
    ReturnedAccuracy (requestedRankOrder hJvalid) T (sturmTridiagonal_isHermitian _ _)
      out.columns out.labels (unitRoundoff p) := by
  let out := acceptedOutputLoop (hp := hp) aW bW bits trial hn hguard hJ hJvalid ha hb htrial r
  let T := storedTridiagonal a b
  let S := normalizedTridiagonal a b r
  let M := trial.matrix bW
  let I := requestedRankOrder hJvalid
  let rank (j : Fin J.card) := (requestedRankArray J hJvalid).get j
  let θ (j : Fin J.card) := (runAcceptedRefinement trial.trial bW (rank j)).value
  let Δ := certifiedGap (n + 1) J.card p
  have hη : finalLabelTolerance (n + 1) J.card p = vectorTolerance (n + 1) J.card p := by
    rw [vectorTolerance_eq_roundoff]
    rfl
  have hS : S = sturmTridiagonal (fun i => (aW i).value) (fun i => (bW i).value) := by
    simpa only [haW, hbW] using (normalizedTrialMatrix_eq (J := J) a b r).symm
  have hSHerm : S.IsHermitian := hS.symm ▸ sturmTridiagonal_isHermitian _ _
  have hFacts (j : Fin J.card) :=
    runAcceptedRefinement_facts aW bW bits trial hp hn hguard hJ hJvalid ha hb htrial (rank j)
  have hk : 0 < J.card := Finset.card_pos.mpr hJ
  let i₀ : Fin J.card := ⟨0, hk⟩
  have hClose : ‖M - S‖ ≤ unitRoundoff p / 128 := by
    rw [hS]
    exact (hFacts i₀).1
  obtain ⟨hR, hScale, hScaleBound, _⟩ := normalization_for_returned_errors a b hr
  have hVectors (j : Fin J.card) :
      ∃ v : EuclideanSpace ℝ (Fin (n + 1)),
        (‖v‖ = 1 ∧ M.toEuclideanLin v = ascendingEigenvalue (trial.matrix_isHermitian bW) (I j) • v) ∧
        ‖toLp 2 (out.columns.col j) - v‖ ≤ 4 * unitRoundoff p := by
    obtain ⟨hx, _, v, hv, hEig, hError⟩ :=
      runAcceptedVector_accuracy aW bW bits trial hp hn hguard hJ hJvalid ha hb htrial (rank j)
    refine ⟨v, ⟨hv, hEig⟩, ?_⟩
    simpa only [out, NativeAcceptedEigenpairs.columns, acceptedOutputLoop, Vector.getElem_ofFn,
      Matrix.col, Matrix.of_apply, trial.readMatrix_eq, vectorComputedOutput, Word.euclidean] using hError
  choose U hU hError using hVectors
  exact returnedAccuracy_of_signed_eigenvectors hp hn hk
    (by simpa only [Fintype.card_fin] using Fintype.card_le_of_injective I I.injective)
    I T S M (sturmTridiagonal_isHermitian _ _) hSHerm (trial.matrix_isHermitian bW)
    hR hScale hScaleBound out.columns θ out.labels U hguard hClose (hFacts i₀).2.1
    (hη.symm ▸ vectorTolerance_doubled_lt_gap _ _ _)
    (fun j => (hFacts j).2.2.1) (fun j => hη.symm ▸ (hFacts j).2.2.2.1)
    (fun j => (hFacts j).2.2.2.2)
    (fun j => by
      simp only [out, NativeAcceptedEigenpairs.labels, acceptedOutputLoop, Vector.getElem_ofFn]
      exact rescaledLabel_value p hp r (θ j)) hU hError

end

end NumStability.CertifiedTridiagonalEigenpairs
