import ComputationalMathematics.Source.CertifiedTridiagonalEigenpairs.AcceptedOutput.ExecutionTarget

/-! Exact output projections from the unified solver to the accepted kernels. -/

namespace NumStability.CertifiedTridiagonalEigenpairs

open Matrix WithLp NoisyRankCertificate FloatingPointFormat.UnboundedBinary

variable {n p : ℕ} {J : Finset ℕ} {hp : 2 ≤ p}

/-- The refined constructor is returned by the nontrivial dispatch branch. -/
theorem runTridiagonalEigenpairs_refined_some
    {a : Fin (n + 1) → Word p hp} {b : Fin n → Word p hp}
    {bits : ℕ → GateBits n J} {guard : precisionGuard (n + 1) p}
    {hJ : J.Nonempty} {valid : J ⊆ Finset.Icc 1 (n + 1)}
    {out : NativeAcceptedEigenpairs n p J hp}
    (h : runTridiagonalEigenpairs a b bits guard hJ valid = some (.refined out)) :
    storedTridiagonal a b ≠ 0 ∧
      ∃ hn : 2 ≤ n + 1, normalizedEigenpairRun a b bits hn guard hJ valid = some out := by
  unfold runTridiagonalEigenpairs at h
  split at h
  · cases Option.some.inj h
  · rename_i he
    obtain ⟨hne, hn⟩ := (exactBranch_eq_none_iff ..).mp he
    refine ⟨hne, hn, ?_⟩
    cases hr : normalizedEigenpairRun a b bits hn guard hJ valid with
    | none => simp [hr] at h
    | some output =>
      simp only [hr, Option.map_some, Option.some.injEq, NativeTridiagonalOutput.refined.injEq] at h
      simp only [h]

/-- Extract the actual first accepted native run on the normalized bands. -/
theorem normalizedEigenpairRun_retry_some
    {a : Fin (n + 1) → Word p hp} {b : Fin n → Word p hp}
    {bits : ℕ → GateBits n J} {hn : 2 ≤ n + 1} {guard : precisionGuard (n + 1) p}
    {hJ : J.Nonempty} {valid : J ⊆ Finset.Icc 1 (n + 1)}
    {out : NativeAcceptedEigenpairs n p J hp}
    (h : normalizedEigenpairRun a b bits hn guard hJ valid = some out) :
    normalizationExponent a b = some out.scaleExponent ∧
    retryRun (fun i => normalizeTrialWord out.scaleExponent (a i))
      (fun i => normalizeTrialWord out.scaleExponent (b i)) bits = some out.accepted := by
  have he := normalizedEigenpairRun_acceptance a b bits hn guard hJ valid
  rw [h, Option.map_some] at he
  exact normalizedRetryRun_some he.symm

set_option maxHeartbeats 1000000 in
/-- The output slot in the native array uses precisely the working label, shift,
and computed real normalization of the corresponding accepted solve. -/
theorem normalizedEigenpairRun_column
    {a : Fin (n + 1) → Word p hp} {b : Fin n → Word p hp}
    {bits : ℕ → GateBits n J} {hn : 2 ≤ n + 1} {guard : precisionGuard (n + 1) p}
    {hJ : J.Nonempty} {valid : J ⊆ Finset.Icc 1 (n + 1)}
    {out : NativeAcceptedEigenpairs n p J hp}
    (h : normalizedEigenpairRun a b bits hn guard hJ valid = some out) (j : Fin J.card) :
    let bW := fun i => normalizeTrialWord (J := J) out.scaleExponent (b i)
    let rank := (requestedRankArray J valid).get j
    let θ := runAcceptedRefinement out.accepted.trial bW rank
    let η := (acceptedShiftWord n p J).value
    let imag := vectorComputedImaginaryArray (workingPrecision_ge_two (n + 1) J.card p)
      (Nat.succ_pos n) (out.accepted.readMatrix bW) θ.value η
    out.pairs[j.val].label = rescaledLabel p hp out.scaleExponent θ.value ∧
    ∃ hx : Word.euclidean imag.get ≠ 0,
      0 < (Word.roundedNormScan imag).value ∧
      out.pairs[j.val].column = Word.normalizeToScan p hp imag hx ∧
      ∃ v : EuclideanSpace ℝ (Fin (n + 1)),
        (‖v‖ = 1 ∧ (out.accepted.matrix bW).toEuclideanLin v =
          ascendingEigenvalue (out.accepted.matrix_isHermitian bW) rank.val • v) ∧
        ‖toLp 2 (out.columns.col j) - v‖ ≤ 4 * unitRoundoff p := by
  obtain ⟨hr, htrial⟩ := normalizedEigenpairRun_retry_some h
  obtain ⟨ha, hb⟩ := normalizedTrialInput_bounds (J := J) a b hr
  obtain ⟨hx, hnorm, v, hv, heig, herr⟩ := runAcceptedVector_accuracy
    (fun i => normalizeTrialWord out.scaleExponent (a i))
    (fun i => normalizeTrialWord out.scaleExponent (b i)) bits out.accepted hp
    hn guard hJ valid ha hb htrial ((requestedRankArray J valid).get j)
  have hpair :
      out.pairs[j.val].label = rescaledLabel p hp out.scaleExponent
        (runAcceptedRefinement out.accepted.trial
          (fun i => normalizeTrialWord out.scaleExponent (b i))
          ((requestedRankArray J valid).get j)).value ∧
      out.pairs[j.val].column = Word.normalizeToScan p hp
        (vectorComputedImaginaryArray (workingPrecision_ge_two (n + 1) J.card p)
          (Nat.succ_pos n) (out.accepted.matrix (fun i => normalizeTrialWord out.scaleExponent (b i)))
          (runAcceptedRefinement out.accepted.trial (fun i => normalizeTrialWord out.scaleExponent (b i))
            ((requestedRankArray J valid).get j)).value
          (acceptedShiftWord n p J).value) hx := by
    unfold normalizedEigenpairRun at h
    split at h
    · contradiction
    · dsimp only at h
      split at h
      · contradiction
      · obtain rfl := Option.some.inj h
        simp only [acceptedOutputLoop, Vector.getElem_ofFn, RetryResult.readMatrix_eq, and_self]
  dsimp only
  rw [RetryResult.readMatrix_eq]
  refine ⟨hpair.1, hx, hnorm, hpair.2, v, ⟨hv, heig⟩, ?_⟩
  change ‖toLp 2 (fun i => (out.pairs[j.val].column.get i).value) - v‖ ≤ _
  rw [hpair.2]
  exact herr

theorem tridiagonalPostacceptExecution : SourceTargets.tridiagonalPostacceptExecution := by
  intro n p J hp a b bits guard hJ valid out h r accepted aW bW M I N q hExp η Δ hq shift
  obtain ⟨hne, hn, hrun⟩ := runTridiagonalEigenpairs_refined_some h
  obtain ⟨hr, htrial⟩ := normalizedEigenpairRun_retry_some hrun
  obtain ⟨ha, hb⟩ := normalizedTrialInput_bounds (J := J) a b hr
  have hmatrix : M = trialMatrix aW bW (bits accepted.index) := by
    change accepted.readMatrix bW = _
    rw [accepted.readMatrix_eq]
    exact retryRun_matrix htrial
  refine ⟨hn, hne, hr, (retryRun_first htrial).1, hmatrix,
    requestedRankOrder_covers valid, vectorToleranceExponent_add_nine_le (k := J.card) hn guard,
    vectorTolerance_half_eq_roundoff N J.card p, acceptedShiftWord_value, ?_⟩
  intro j θ spectrum imag
  have hθ : θ = runAcceptedRefinement accepted.trial bW ((requestedRankArray J valid).get j) := rfl
  obtain ⟨_, _, hgap, hnear, _⟩ := runAcceptedRefinement_facts aW bW bits accepted hp hn
    guard hJ valid ha hb htrial ((requestedRankArray J valid).get j)
  obtain ⟨hlabel, hx, hpositive, hcolumn, _⟩ := normalizedEigenpairRun_column hrun j
  refine ⟨hnear, hgap, hx, hpositive, hcolumn, ?_⟩
  rw [hlabel, hθ]
  exact rescaledLabel_value p hp r _

end NumStability.CertifiedTridiagonalEigenpairs
