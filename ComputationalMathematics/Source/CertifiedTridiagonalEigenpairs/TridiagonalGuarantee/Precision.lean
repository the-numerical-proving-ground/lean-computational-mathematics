import ComputationalMathematics.Source.CertifiedTridiagonalEigenpairs.TridiagonalEigenpairWork

/-! The precision of the measured phases of the selected tridiagonal solver. -/

namespace NumStability.CertifiedTridiagonalEigenpairs

open FloatingPointFormat.UnboundedBinary ScalarWork

private theorem traceAllowed_mono {p q : ℕ} {trace : List Step}
    (h : TraceAllowed p trace) (hpq : p ≤ q) : TraceAllowed q trace := by
  intro step hstep
  have hs := h step hstep
  cases step with
  | arithmetic => exact ⟨hs.1, hs.2.trans hpq⟩
  | conversion => exact ⟨hs.1, hs.2.1.trans hpq, hs.2.2.1, hs.2.2.2.trans hpq⟩
  | _ => trivial

private theorem normalizationSetupTrace_allowed {n p : ℕ} {hp : 2 ≤ p}
    (a : Fin (n + 1) → Word p hp) (b : Fin n → Word p hp) (J : Finset ℕ) :
    TraceAllowed (workingPrecision (n + 1) J.card p) (normalizationSetupTrace a b J) := by
  let q := workingPrecision (n + 1) J.card p
  have hpq : p ≤ q := by dsimp [q, workingPrecision]; omega
  have hq : 2 ≤ q := hp.trans hpq
  have hscan := traceAllowed_mono (runNormalizationScan_resources a b).2.1 hpq
  intro step hstep
  change step.Allowed q
  unfold normalizationSetupTrace at hstep
  rcases List.mem_append.mp hstep with hs | hs
  · exact hscan step hs
  · split at hs
    · simp only [List.mem_flatten, List.mem_replicate] at hs
      obtain ⟨_, ⟨_, rfl⟩, hs⟩ := hs
      change step ∈ [.index, .scaleByPowerOfTwo, .conversion p q, .index] at hs
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
      rcases hs with rfl | rfl | rfl | rfl <;> simp [Step.Allowed, hp, hpq, hq]
    · cases hs

/-- The exact dispatch uses only input precision, including its materialized
output. When dispatch proceeds to the normalized branch, its measured setup
and every finite trial prefix respect the working precision. So do the
post-accept stages on any returned refined output, with its retained scale
and first accepted trial. -/
def tridiagonalEigenpairRespectsPrecision {n p : ℕ} {J : Finset ℕ} {hp : 2 ≤ p}
    (a : Fin (n + 1) → Word p hp) (b : Fin n → Word p hp)
    (hguard : precisionGuard (n + 1) p) (hJ : J.Nonempty)
    (hJvalid : J ⊆ Finset.Icc 1 (n + 1)) : Prop :=
  let q := workingPrecision (n + 1) J.card p
  let I := requestedRankOrder hJvalid
  TraceAllowed p (runExactBranch a b I).trace ∧
  (exactBranch a b I = none →
    TraceAllowed q (normalizationSetupTrace a b J) ∧
    ∃ r, normalizationExponent a b = some r ∧
      ∀ (bits : ℕ → GateBits n J) (m : ℕ),
        TraceAllowed q (trialTracePrefix (fun i => normalizeTrialWord r (a i))
          (fun i => normalizeTrialWord r (b i)) bits m)) ∧
  ∀ bits out, runTridiagonalEigenpairs a b bits hguard hJ hJvalid = some (.refined out) →
    acceptedOutputRespectsPrecision out.accepted
      (fun i => normalizeTrialWord out.scaleExponent (b i)) hJvalid

theorem tridiagonalEigenpair_respectsPrecision {n p : ℕ} {J : Finset ℕ} {hp : 2 ≤ p}
    (a : Fin (n + 1) → Word p hp) (b : Fin n → Word p hp)
    (hguard : precisionGuard (n + 1) p) (hJ : J.Nonempty)
    (hJvalid : J ⊆ Finset.Icc 1 (n + 1)) :
    tridiagonalEigenpairRespectsPrecision a b hguard hJ hJvalid := by
  unfold tridiagonalEigenpairRespectsPrecision
  refine ⟨(runExactBranch_work a b _ (Finset.card_pos.mpr hJ)).2, ?_, ?_⟩
  · intro he
    obtain ⟨hnonzero, hn⟩ := (exactBranch_eq_none_iff ..).mp he
    cases hr : normalizationExponent a b with
    | none => exact (hnonzero ((normalizationExponent_eq_none_iff a b).mp hr)).elim
    | some r =>
      obtain ⟨ha, hb⟩ := normalizedTrialInput_bounds (J := J) a b hr
      exact ⟨normalizationSetupTrace_allowed a b J, r, rfl, fun bits m =>
        trialTracePrefix_allowed (bits := bits) hn hguard hJ hJvalid ha hb m⟩
  · intro bits out hrun
    have hn : 2 ≤ n + 1 := by
      unfold runTridiagonalEigenpairs at hrun
      split at hrun
      · cases Option.some.inj hrun
      · rename_i he
        exact ((exactBranch_eq_none_iff ..).mp he).2
    exact acceptedOutput_respectsPrecision _ _ hJvalid hp hn

end NumStability.CertifiedTridiagonalEigenpairs
