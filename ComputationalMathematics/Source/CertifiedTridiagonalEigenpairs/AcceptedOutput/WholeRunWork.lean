import ComputationalMathematics.Source.CertifiedTridiagonalEigenpairs.AcceptedOutput.Resources
import ComputationalMathematics.Source.CertifiedTridiagonalEigenpairs.ExactBranchExecution
import ComputationalMathematics.Source.CertifiedTridiagonalEigenpairs.Retry.WorkComposition

/-!
# Work of the normalized tridiagonal eigensolver

The work meter follows the same normalization, retry stream, and accepted trial
as `normalizedEigenpairRun`. Counts for the numerical output include every
stored column and label. Setup charges the observed band scan and exact scaling.
-/

open MeasureTheory
open scoped ENNReal

namespace NumStability.CertifiedTridiagonalEigenpairs

open IndependentRetry ScalarWork FloatingPointFormat.UnboundedBinary

/-- Form and store one normalized word using an exact shift and widening. -/
private def normalizationWordSteps (p q : ℕ) : List Step :=
  [.index, .scaleByPowerOfTwo, .conversion p q, .index]

/-- Charge the measured scan of the original bands and the actual scale
selection. A selected exponent is followed by a shift, widening and store
for every entry in both working-precision bands. -/
def normalizationSetupTrace {n p : ℕ} {hp : 2 ≤ p}
    (a : Fin (n + 1) → Word p hp) (b : Fin n → Word p hp) (J : Finset ℕ) : List Step :=
  let observed := runNormalizationScan a b
  let q := workingPrecision (n + 1) J.card p
  observed.trace ++
    (if observed.exponent.isSome then
      (List.replicate (2 * n + 1) (normalizationWordSteps p q)).flatten else [])

theorem normalizationSetupWork_le {n p : ℕ} {hp : 2 ≤ p}
    (a : Fin (n + 1) → Word p hp) (b : Fin n → Word p hp) (J : Finset ℕ) :
    work (normalizationSetupTrace a b J) ≤ 40 * (n + 1) := by
  have hscan := (runNormalizationScan_resources a b).1
  simp only [work] at hscan
  simp only [normalizationSetupTrace, runNormalizationScan_exponent]
  split <;> simp [normalizationWordSteps, work] <;> omega

noncomputable section

variable {n p : ℕ} {J : Finset ℕ} {hp : 2 ≤ p}

private def normalizedDiagonal (a : Fin (n + 1) → Word p hp) (r : ℤ) :
    Fin (n + 1) → TrialWord n J p := fun i => normalizeTrialWord r (a i)

private def normalizedSubdiagonal (b : Fin n → Word p hp) (r : ℤ) :
    Fin n → TrialWord n J p := fun i => normalizeTrialWord r (b i)

private def normalizedPostWork (b : Fin n → Word p hp) (r : ℤ)
    (hJvalid : J ⊆ Finset.Icc 1 (n + 1)) (trial : RetryResult n J p) : ℕ :=
  (acceptedOutputUsage trial (normalizedSubdiagonal b r) hJvalid).work

/-- Charged work on the same stream as the normalized numerical execution.
An input with no normalization exponent is outside this branch. -/
def normalizedEigenpairWork (a : Fin (n + 1) → Word p hp) (b : Fin n → Word p hp)
    (hJvalid : J ⊆ Finset.Icc 1 (n + 1)) (bits : ℕ → GateBits n J) : ℝ≥0∞ :=
  match normalizationExponent a b with
  | none => ⊤
  | some r => retryTotalWork (a := normalizedDiagonal a r) (b := normalizedSubdiagonal b r)
    (work (normalizationSetupTrace a b J)) (normalizedPostWork b r hJvalid) bits

/-- Perturbation count of the normalized branch on the same stream of bits. -/
def normalizedEigenpairAttemptCount (a : Fin (n + 1) → Word p hp) (b : Fin n → Word p hp)
    (bits : ℕ → GateBits n J) : ℝ≥0∞ :=
  match normalizationExponent a b with
  | none => ⊤
  | some r => retryCount (trialRejected n p J (normalizedDiagonal a r) (normalizedSubdiagonal b r)) bits

theorem measurable_normalizedEigenpairWork (a : Fin (n + 1) → Word p hp)
    (b : Fin n → Word p hp) (hJvalid : J ⊆ Finset.Icc 1 (n + 1)) :
    Measurable (normalizedEigenpairWork a b hJvalid) := by
  change Measurable (fun bits => normalizedEigenpairWork a b hJvalid bits)
  cases hs : normalizationExponent a b with
  | none => simpa only [normalizedEigenpairWork, hs] using (measurable_const : Measurable (fun _ : ℕ → GateBits n J => (⊤ : ℝ≥0∞)))
  | some r => simpa only [normalizedEigenpairWork, hs] using
      (measurable_retryTotalWork (a := normalizedDiagonal a r) (b := normalizedSubdiagonal b r)
        (work (normalizationSetupTrace a b J)) (normalizedPostWork b r hJvalid))

section Input

variable (a : Fin (n + 1) → Word p hp) (b : Fin n → Word p hp)
  (hn : 2 ≤ n + 1) (hguard : precisionGuard (n + 1) p)
  (hJ : J.Nonempty) (hJvalid : J ⊆ Finset.Icc 1 (n + 1))

/-- A returned output records the trial whose trace and final meter were charged. -/
theorem normalizedEigenpairWork_eq_of_returns {bits : ℕ → GateBits n J}
    {out : NativeAcceptedEigenpairs n p J hp}
    (h : normalizedEigenpairRun a b bits hn hguard hJ hJvalid = some out) :
    normalizedEigenpairWork a b hJvalid bits =
      (work (normalizationSetupTrace a b J) : ℝ≥0∞) +
      (work (trialTracePrefix (fun i => normalizeTrialWord out.scaleExponent (a i))
        (fun i => normalizeTrialWord out.scaleExponent (b i)) bits (out.accepted.index + 1)) : ℝ≥0∞) +
      ((normalizedAcceptedOutputUsage b hJvalid out).work : ℝ≥0∞) := by
  have hRetry := normalizedEigenpairRun_acceptance a b bits hn hguard hJ hJvalid
  rw [h, Option.map_some] at hRetry
  obtain ⟨hr, htrial⟩ := normalizedRetryRun_some hRetry.symm
  simp only [normalizedEigenpairWork, hr, retryTotalWork, retryPostWork]
  have htrial' : retryRun (normalizedDiagonal a out.scaleExponent)
      (normalizedSubdiagonal b out.scaleExponent) bits = some out.accepted := htrial
  rw [retryTrialWork_eq_work_prefix htrial', htrial', Option.elim_some]
  rfl

theorem normalizedEigenpairWork_eq_top_iff (bits : ℕ → GateBits n J) :
    normalizedEigenpairWork a b hJvalid bits = ⊤ ↔
      normalizedEigenpairRun a b bits hn hguard hJ hJvalid = none := by
  have hRetry := normalizedEigenpairRun_acceptance a b bits hn hguard hJ hJvalid
  have hnone : normalizedEigenpairRun a b bits hn hguard hJ hJvalid = none ↔
      normalizedRetryRun a b bits = none := by
    rw [← hRetry]
    cases normalizedEigenpairRun a b bits hn hguard hJ hJvalid <;> simp
  rw [hnone]
  cases hs : normalizationExponent a b with
  | none => simp [normalizedEigenpairWork, normalizedRetryRun, hs]
  | some r =>
    rw [normalizedEigenpairWork, hs, retryTotalWork_eq_top_iff]
    simp [normalizedRetryRun, hs, Vector.getElem_ofFn]
    rfl

include hn hguard hJ hJvalid in
private theorem normalization_and_post_work_bounds {r : ℤ} (hr : normalizationExponent a b = some r)
    {extra : ℕ} (hextra : extra ≤ 56 * ((n + 1) * J.card)) :
    extra + work (normalizationSetupTrace a b J) ≤ retryTrialWorkScale n J p ∧
    (∀ bits trial,
      retryRun (normalizedDiagonal (J := J) a r) (normalizedSubdiagonal b r) bits = some trial →
      (extra + work (normalizationSetupTrace a b J)) + normalizedPostWork b r hJvalid trial ≤
        retryTrialWorkScale n J p) := by
  have hk : 0 < J.card := Finset.card_pos.mpr hJ
  have hNk : n + 1 ≤ (n + 1) * J.card := Nat.le_mul_of_pos_right _ hk
  have hNkp : n + 1 ≤ (n + 1) * J.card * p :=
    hNk.trans (Nat.le_mul_of_pos_right _ (by omega))
  have hprep := normalizationSetupWork_le a b J
  have hb : work (normalizationSetupTrace a b J) ≤ 40 * ((n + 1) * J.card * p) :=
    hprep.trans (Nat.mul_le_mul_left _ hNkp)
  have he : extra ≤ 56 * ((n + 1) * J.card * p) :=
    hextra.trans (Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_right _ (by omega)))
  constructor
  · unfold retryTrialWorkScale
    nlinarith only [he, hb, show 0 ≤ (n + 1) * J.card * p from Nat.zero_le _]
  · intro bits trial htrial
    obtain ⟨haW, hbW⟩ := normalizedTrialInput_bounds (J := J) a b hr
    have hpost := (acceptedOutputUsage_resources _ _ bits trial hp hn hguard hJ hJvalid
      haW hbW htrial).2.2.2.2.2.1
    unfold normalizedPostWork retryTrialWorkScale
    change (acceptedOutputUsage trial (normalizedSubdiagonal b r) hJvalid).work ≤ _ at hpost
    nlinarith only [he, hb, hpost, show 0 ≤ (n + 1) * J.card * p from Nat.zero_le _]

include hn hguard hJ hJvalid in
/-- All setup and all final output work fit one additional trial-sized budget. -/
theorem normalizedEigenpairWork_addSetup_le {extra : ℕ} (hextra : extra ≤ 56 * ((n + 1) * J.card))
    (bits : ℕ → GateBits n J) :
    (extra : ℝ≥0∞) + normalizedEigenpairWork a b hJvalid bits ≤ (retryTrialWorkScale n J p : ℝ≥0∞) *
      (normalizedEigenpairAttemptCount a b bits + 1) := by
  cases hr : normalizationExponent a b with
  | none =>
    have hpositive : retryTrialWorkScale n J p ≠ 0 := by
      have := Finset.card_pos.mpr hJ
      unfold retryTrialWorkScale
      positivity
    simp [normalizedEigenpairWork, normalizedEigenpairAttemptCount, hr, hpositive]
  | some r =>
    obtain ⟨haW, hbW⟩ := normalizedTrialInput_bounds (J := J) a b hr
    obtain ⟨hsetup, hafter⟩ := normalization_and_post_work_bounds a b hn hguard hJ hJvalid hr hextra
    simp only [normalizedEigenpairWork, normalizedEigenpairAttemptCount, hr, retryTotalWork_add_setup]
    exact retryTotalWork_le hn hguard hJ hJvalid haW hbW le_rfl hsetup hafter bits

include hn hguard hJ hJvalid in
theorem normalizedEigenpairWork_le (bits : ℕ → GateBits n J) :
    normalizedEigenpairWork a b hJvalid bits ≤ (retryTrialWorkScale n J p : ℝ≥0∞) *
      (normalizedEigenpairAttemptCount a b bits + 1) := by
  simpa only [Nat.cast_zero, zero_add] using normalizedEigenpairWork_addSetup_le a b hn hguard hJ hJvalid
    (extra := 0) (Nat.zero_le _) bits

include hn hguard hJ hJvalid in
/-- Full normalized-run work, including the exact sampler charges and the
post-accept outputs, has the paper's mean and work-tail bounds. -/
theorem normalizedEigenpairWork_addSetup_expectation_tail (hnonzero : storedTridiagonal a b ≠ 0)
    {extra : ℕ} (hextra : extra ≤ 56 * ((n + 1) * J.card)) :
    (∫⁻ bits, (extra : ℝ≥0∞) + normalizedEigenpairWork a b hJvalid bits ∂retryBitMeasure n J) ≤
      3 * (retryTrialWorkScale n J p : ℝ≥0∞) ∧
    ∀ m : ℕ, retryBitMeasure n J
      {bits | (retryTrialWorkScale n J p : ℝ≥0∞) * ((m : ℝ≥0∞) + 1) <
        (extra : ℝ≥0∞) + normalizedEigenpairWork a b hJvalid bits} ≤
        ENNReal.ofReal (rejectionBound (n + 1)) ^ m := by
  cases hr : normalizationExponent a b with
  | none => exact (hnonzero ((normalizationExponent_eq_none_iff a b).mp hr)).elim
  | some r =>
    obtain ⟨haW, hbW⟩ := normalizedTrialInput_bounds (J := J) a b hr
    obtain ⟨hsetup, hafter⟩ := normalization_and_post_work_bounds a b hn hguard hJ hJvalid hr hextra
    simp_rw [normalizedEigenpairWork, hr, retryTotalWork_add_setup]
    exact retryTotalWork_expectation_tail hn hguard hJ hJvalid haW hbW le_rfl hsetup hafter

include hn hguard hJ hJvalid in
theorem normalizedEigenpairWork_expectation_tail (hnonzero : storedTridiagonal a b ≠ 0) :
    (∫⁻ bits, normalizedEigenpairWork a b hJvalid bits ∂retryBitMeasure n J) ≤
      3 * (retryTrialWorkScale n J p : ℝ≥0∞) ∧
    ∀ m : ℕ, retryBitMeasure n J
      {bits | (retryTrialWorkScale n J p : ℝ≥0∞) * ((m : ℝ≥0∞) + 1) <
        normalizedEigenpairWork a b hJvalid bits} ≤ ENNReal.ofReal (rejectionBound (n + 1)) ^ m := by
  simpa only [Nat.cast_zero, zero_add] using
    normalizedEigenpairWork_addSetup_expectation_tail a b hn hguard hJ hJvalid hnonzero
      (extra := 0) (Nat.zero_le _)

include hn hguard hJ hJvalid in
/-- Both source confidence thresholds refer to the same complete work meter. -/
theorem normalizedEigenpairWork_confidence (hnonzero : storedTridiagonal a b ≠ 0) :
    (∀ c : ℝ, 0 < c → 1 - ENNReal.ofReal ((n + 1 : ℝ) ^ (-c)) ≤
      retryBitMeasure n J {bits | normalizedEigenpairWork a b hJvalid bits ≤
        (retryTrialWorkScale n J p : ℝ≥0∞) * ((polynomialConfidenceTrials c : ℝ≥0∞) + 1)}) ∧
    (∀ ε : ℝ, 0 < ε → ε < 1 → 1 - ENNReal.ofReal ε ≤
      retryBitMeasure n J {bits | normalizedEigenpairWork a b hJvalid bits ≤
        (retryTrialWorkScale n J p : ℝ≥0∞) *
          ((arbitraryConfidenceTrials (nextPowerOfTwo (n + 1)) ε : ℝ≥0∞) + 1)}) := by
  let μ := retryBitMeasure n J
  let scale : ℝ≥0∞ := retryTrialWorkScale n J p
  have hmeas := measurable_normalizedEigenpairWork a b hJvalid
  have htail := (normalizedEigenpairWork_expectation_tail a b hn hguard hJ hJvalid hnonzero).2
  have hN := le_nextPowerOfTwo (n + 1)
  refine ⟨?_, ?_⟩
  · intro c hc
    simpa only [Nat.cast_succ] using work_polynomialConfidence μ hmeas scale
      (fun m _ => htail m) (Nat.succ_pos n) hN hc
  · intro ε hε hε1
    exact work_arbitraryConfidence μ hmeas scale ((Nat.succ_pos n).trans_le hN)
      (fun m _ => htail m) hε hε1

end Input
end

end NumStability.CertifiedTridiagonalEigenpairs
