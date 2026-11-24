import ComputationalMathematics.Source.CertifiedTridiagonalEigenpairs.FiniteTrial.StreamingWorkspace
import ComputationalMathematics.Source.CertifiedTridiagonalEigenpairs.Retry.Execution

/-! Every finite prefix of the retry run is realizable by a constant-state loop. -/

namespace NumStability.CertifiedTridiagonalEigenpairs

variable {n p : ℕ} {J : Finset ℕ}

private noncomputable def retryPrefixStep
    (a : Fin (n + 1) → TrialWord n J p) (b : Fin n → TrialWord n J p)
    (bits : ℕ → GateBits n J) (previous : Option (RetryResult n J p)) (i : ℕ) :
    Option (RetryResult n J p) :=
  match previous with
  | some r => some r
  | none =>
    let trial := runStreamingTrial n p J a b (bits i)
    if h : trial.accepted = true then some ⟨i, ⟨trial, h⟩⟩ else none

/-- Execute at most the specified number of fresh trials. The numerical state
after a rejection is empty. On acceptance one stored diagonal is retained
and the remaining bounded iterations read no fresh bits. -/
noncomputable def retryRunPrefix
    (a : Fin (n + 1) → TrialWord n J p) (b : Fin n → TrialWord n J p)
    (bits : ℕ → GateBits n J) (trials : ℕ) : Option (RetryResult n J p) :=
  Fin.foldl trials (fun previous i => retryPrefixStep a b bits previous i.val) none

variable (a : Fin (n + 1) → TrialWord n J p) (b : Fin n → TrialWord n J p)
  (bits : ℕ → GateBits n J)

private theorem retryRunPrefix_succ (m : ℕ) :
    retryRunPrefix a b bits (m + 1) = retryPrefixStep a b bits (retryRunPrefix a b bits m) m := by
  unfold retryRunPrefix
  rw [Fin.foldl_succ_last]
  rfl

private theorem retryPrefixStep_rejected {i : ℕ} (h : bits i ∈ trialRejected n p J a b) :
    retryPrefixStep a b bits none i = none := by
  have heq : (trialRun n p J a b (bits i)).accepted = false := h
  simp [retryPrefixStep, runStreamingTrial_eq, heq]

private theorem retryPrefixStep_accepted {r : RetryResult n J p}
    (h : retryRun a b bits = some r) : retryPrefixStep a b bits none r.index = some r := by
  simp only [retryPrefixStep, runStreamingTrial_eq, ← (retryRun_first h).1, dif_pos r.trial.property]

/-- Connecting the bounded sequential loop to the full run also identifies
exactly which of its prefixes contain the returned diagonal. -/
theorem retryRunPrefix_eq_filter (m : ℕ) :
    retryRunPrefix a b bits m = (retryRun a b bits).filter (fun r => decide (r.index < m)) := by
  induction m with
  | zero =>
    cases retryRun a b bits <;> simp [retryRunPrefix]
  | succ m ih =>
    rw [retryRunPrefix_succ, ih]
    cases hr : retryRun a b bits with
    | none =>
      rw [Option.filter_none, Option.filter_none]
      exact retryPrefixStep_rejected a b bits (retryRun_eq_none_iff.mp hr m)
    | some r =>
      rcases lt_trichotomy r.index m with hlt | heq | hgt
      · have hs : r.index < m + 1 := by omega
        simp [Option.filter, hlt, hs, retryPrefixStep]
      · have hn : ¬r.index < m := by omega
        have hs : r.index < m + 1 := by omega
        simp only [Option.filter, hn, hs, decide_true, decide_false, Bool.false_eq_true,
          if_false, if_true]
        rw [← heq]
        exact retryPrefixStep_accepted a b bits hr
      · have hn : ¬r.index < m := by omega
        have hs : ¬r.index < m + 1 := by omega
        simp only [Option.filter, hn, hs, decide_false, Bool.false_eq_true, if_false]
        exact retryPrefixStep_rejected a b bits ((retryRun_first hr).2 m hgt)

/-- The measured prefix shares the numerical step and adds a peak counter.
Across attempts only the normalized input, scale and request/cursor state
persist. Once a result is held, no new gate invocation is measured. -/
noncomputable def measuredRetryPrefix (trials : ℕ) : Option (RetryResult n J p) × ℕ :=
  let resident := 2 * (n + 1) + J.card + 8
  Fin.foldl trials (fun previous i =>
    match previous.1 with
    | some _ => previous
    | none =>
      (retryPrefixStep a b bits previous.1 i.val,
        max previous.2 (resident + streamingTrialWorkspace a b (bits i.val)))) (none, resident)

private theorem measuredRetryPrefix_succ (m : ℕ) :
    measuredRetryPrefix a b bits (m + 1) =
      let previous := measuredRetryPrefix a b bits m
      match previous.1 with
      | some _ => previous
      | none => (retryPrefixStep a b bits previous.1 m,
        max previous.2 (2 * (n + 1) + J.card + 8 + streamingTrialWorkspace a b (bits m))) := by
  unfold measuredRetryPrefix
  rw [Fin.foldl_succ_last]
  rfl

/-- Reading the first component of the observer gives the numerical prefix. -/
theorem measuredRetryPrefix_run (m : ℕ) :
    (measuredRetryPrefix a b bits m).1 = retryRunPrefix a b bits m := by
  induction m with
  | zero => simp [measuredRetryPrefix, retryRunPrefix]
  | succ m ih =>
    rw [measuredRetryPrefix_succ, retryRunPrefix_succ, ← ih]
    cases h : (measuredRetryPrefix a b bits m).1 <;> simp [h, retryPrefixStep]

/-- Every new active trial can only raise the observed peak. -/
theorem measuredRetryPrefix_peak_monotone :
    Monotone (fun m => (measuredRetryPrefix a b bits m).2) := by
  apply monotone_nat_of_le_succ
  intro m
  rw [measuredRetryPrefix_succ]
  dsimp only
  split
  · rfl
  · exact le_max_left _ _

/-- After acceptance, neither the stored diagonal nor the space observation
changes on a longer prefix. -/
theorem measuredRetryPrefix_stable (m extra : ℕ) (result : RetryResult n J p)
    (h : (measuredRetryPrefix a b bits m).1 = some result) :
    measuredRetryPrefix a b bits (m + extra) = measuredRetryPrefix a b bits m := by
  induction extra with
  | zero => rfl
  | succ extra ih =>
    rw [Nat.add_succ, measuredRetryPrefix_succ, ih]
    dsimp only
    rw [h]

/-- Peak memory is bounded on every finite prefix, including prefixes of
streams that reject forever. No factor depends on the number of trials. -/
theorem measuredRetryPrefix_workspace (m : ℕ) (hkn : J.card ≤ n + 1) :
    (measuredRetryPrefix a b bits m).2 ≤ 55 * (n + 1) := by
  induction m with
  | zero =>
    simp only [measuredRetryPrefix, Fin.foldl_zero]
    omega
  | succ m ih =>
    rw [measuredRetryPrefix_succ]
    dsimp only
    split
    · exact ih
    · have h := streamingTrialWorkspace_le a b (bits m) hkn
      exact max_le ih (by omega)

end NumStability.CertifiedTridiagonalEigenpairs
