import ComputationalMathematics.Source.CertifiedTridiagonalEigenpairs.AcceptedOutput.ExactBranchWork
import ComputationalMathematics.Source.CertifiedTridiagonalEigenpairs.TridiagonalEigenpairRun

/-! Whole-execution work and confidence on the streams of the tridiagonal solver. -/

open MeasureTheory
open scoped ENNReal

namespace NumStability.CertifiedTridiagonalEigenpairs

open ScalarWork FloatingPointFormat.UnboundedBinary

noncomputable section

variable {n p : ℕ} {J : Finset ℕ} {hp : 2 ≤ p}

/-- Charge the exact dispatch on every execution. On a nontrivial input its
scan returns no output, and the normalization, retry and accepted output charges
are added. Successful exact dispatch already charges its full dense output. -/
def tridiagonalEigenpairWork (a : Fin (n + 1) → Word p hp) (b : Fin n → Word p hp)
    (hJvalid : J ⊆ Finset.Icc 1 (n + 1)) (bits : ℕ → GateBits n J) : ℝ≥0∞ :=
  match exactBranch a b (requestedRankOrder hJvalid) with
  | some _ => exactEigenpairWork a b hJvalid
  | none => exactEigenpairWork a b hJvalid + normalizedEigenpairWork a b hJvalid bits

/-- Exact branches draw zero trial blocks. The normalized branch counts every invocation. -/
def tridiagonalEigenpairAttemptCount (a : Fin (n + 1) → Word p hp) (b : Fin n → Word p hp)
    (hJvalid : J ⊆ Finset.Icc 1 (n + 1)) (bits : ℕ → GateBits n J) : ℝ≥0∞ :=
  match exactBranch a b (requestedRankOrder hJvalid) with
  | some _ => 0
  | none => normalizedEigenpairAttemptCount a b bits

variable (a : Fin (n + 1) → Word p hp) (b : Fin n → Word p hp)
  (hguard : precisionGuard (n + 1) p)
  (hJ : J.Nonempty) (hJvalid : J ⊆ Finset.Icc 1 (n + 1))

theorem measurable_tridiagonalEigenpairWork : Measurable (tridiagonalEigenpairWork a b hJvalid) := by
  change Measurable (fun bits => tridiagonalEigenpairWork a b hJvalid bits)
  cases h : exactBranch a b (requestedRankOrder hJvalid) with
  | none => simp only [tridiagonalEigenpairWork, h]; exact
      measurable_const.add (measurable_normalizedEigenpairWork a b hJvalid)
  | some out => simp only [tridiagonalEigenpairWork, h]; exact measurable_const

/-- Whole work is infinite exactly on streams where the very same solver does not return. -/
theorem tridiagonalEigenpairWork_eq_top_iff (bits : ℕ → GateBits n J) :
    tridiagonalEigenpairWork a b hJvalid bits = ⊤ ↔
      runTridiagonalEigenpairs a b bits hguard hJ hJvalid = none := by
  unfold runTridiagonalEigenpairs
  split
  · rename_i out h
    simp [tridiagonalEigenpairWork, exactEigenpairWork, h]
  · rename_i h
    have hn := ((exactBranch_eq_none_iff ..).mp h).2
    simp only [tridiagonalEigenpairWork, h, ENNReal.add_eq_top, exactEigenpairWork,
      ENNReal.natCast_ne_top, false_or, normalizedEigenpairWork_eq_top_iff a b hn hguard hJ hJvalid]
    cases normalizedEigenpairRun a b bits hn hguard hJ hJvalid <;> simp

include hguard hJ in
/-- Complete work is finite almost surely for the same reason the solver returns. -/
theorem ae_tridiagonalEigenpairWork_finite :
    ∀ᵐ bits ∂retryBitMeasure n J, tridiagonalEigenpairWork a b hJvalid bits < ⊤ := by
  filter_upwards [runTridiagonalEigenpairs_returns a b hguard hJ hJvalid] with bits hbits
  obtain ⟨out, hout⟩ := hbits
  rw [lt_top_iff_ne_top, ne_eq, tridiagonalEigenpairWork_eq_top_iff a b hguard hJ hJvalid, hout]
  exact Option.some_ne_none _

/-- The exact work is the measured scan and write cost for the materialized
list returned by the solver. -/
theorem tridiagonalEigenpairWork_eq_of_exact {bits : ℕ → GateBits n J}
    {out : ExactBranchOutput p hp n J.card} {words : List (Word p hp)}
    (h : runTridiagonalEigenpairs a b bits hguard hJ hJvalid = some (.exact out words)) :
    tridiagonalEigenpairWork a b hJvalid bits = exactEigenpairWork a b hJvalid ∧
    (runExactBranch a b (requestedRankOrder hJvalid)).words = words ∧
    tridiagonalEigenpairAttemptCount a b hJvalid bits = 0 := by
  unfold runTridiagonalEigenpairs at h
  split at h
  · rename_i exactOut he
    cases Option.some.inj h
    simp [tridiagonalEigenpairWork, tridiagonalEigenpairAttemptCount, he,
      (runExactBranch_output a b (requestedRankOrder hJvalid)).2]
  · rename_i he
    have hn := ((exactBranch_eq_none_iff ..).mp he).2
    cases hr : normalizedEigenpairRun a b bits hn hguard hJ hJvalid <;> simp [hr] at h

/-- The nontrivial output is tied to the dispatch, scale, actual trial prefix,
and final meter charged on its retained accepted trial. -/
theorem tridiagonalEigenpairWork_eq_of_refined {bits : ℕ → GateBits n J}
    {out : NativeAcceptedEigenpairs n p J hp}
    (h : runTridiagonalEigenpairs a b bits hguard hJ hJvalid = some (.refined out)) :
    tridiagonalEigenpairWork a b hJvalid bits = exactEigenpairWork a b hJvalid +
      ((work (normalizationSetupTrace a b J) : ℝ≥0∞) +
      (work (trialTracePrefix (fun i => normalizeTrialWord out.scaleExponent (a i))
        (fun i => normalizeTrialWord out.scaleExponent (b i)) bits (out.accepted.index + 1)) : ℝ≥0∞) +
      ((normalizedAcceptedOutputUsage b hJvalid out).work : ℝ≥0∞)) := by
  unfold runTridiagonalEigenpairs at h
  split at h
  · cases Option.some.inj h
  · rename_i he
    have hn := ((exactBranch_eq_none_iff ..).mp he).2
    cases hr : normalizedEigenpairRun a b bits hn hguard hJ hJvalid with
    | none => simp [hr] at h
    | some refined =>
      simp only [hr, Option.map_some] at h
      cases Option.some.inj h
      simp only [tridiagonalEigenpairWork, he,
        normalizedEigenpairWork_eq_of_returns a b hn hguard hJ hJvalid hr]

include hguard hJ in
/-- Every stream has the complete pathwise bound, with zero trials on exact inputs. -/
theorem tridiagonalEigenpairWork_le (bits : ℕ → GateBits n J) :
    tridiagonalEigenpairWork a b hJvalid bits ≤ (retryTrialWorkScale n J p : ℝ≥0∞) *
      (tridiagonalEigenpairAttemptCount a b hJvalid bits + 1) := by
  cases h : exactBranch a b (requestedRankOrder hJvalid) with
  | some out => simpa only [tridiagonalEigenpairWork, tridiagonalEigenpairAttemptCount, h, zero_add, mul_one]
      using exactEigenpairWork_le a b hJ hJvalid
  | none =>
    have hn := ((exactBranch_eq_none_iff ..).mp h).2
    have hsetup := (runExactBranch_work a b (requestedRankOrder hJvalid) (Finset.card_pos.mpr hJ)).1
    simpa only [tridiagonalEigenpairWork, tridiagonalEigenpairAttemptCount, h, exactEigenpairWork]
      using normalizedEigenpairWork_addSetup_le a b hn hguard hJ hJvalid hsetup bits

include hguard hJ in
/-- The expected complete work and the work-tail event use one common constant
and the same input and random execution, including exact branches. -/
theorem tridiagonalEigenpairWork_expectation_tail :
    (∫⁻ bits, tridiagonalEigenpairWork a b hJvalid bits ∂retryBitMeasure n J) ≤
      3 * (retryTrialWorkScale n J p : ℝ≥0∞) ∧
    ∀ m : ℕ, retryBitMeasure n J
      {bits | (retryTrialWorkScale n J p : ℝ≥0∞) * ((m : ℝ≥0∞) + 1) <
        tridiagonalEigenpairWork a b hJvalid bits} ≤ ENNReal.ofReal (rejectionBound (n + 1)) ^ m := by
  cases h : exactBranch a b (requestedRankOrder hJvalid) with
  | some out =>
    have ⟨hmean, htail⟩ := exactEigenpairWork_expectation_tail a b hJ hJvalid
    simp_rw [tridiagonalEigenpairWork, h]
    exact ⟨hmean, fun m => (htail m).trans_le bot_le⟩
  | none =>
    obtain ⟨hnonzero, hn⟩ := (exactBranch_eq_none_iff ..).mp h
    have hsetup := (runExactBranch_work a b (requestedRankOrder hJvalid) (Finset.card_pos.mpr hJ)).1
    simp_rw [tridiagonalEigenpairWork, h, exactEigenpairWork]
    exact normalizedEigenpairWork_addSetup_expectation_tail a b hn hguard hJ hJvalid hnonzero hsetup

include hguard hJ in
/-- The trial-count bounds hold for the same execution as the work bounds,
with a zero count on the exact branches. -/
theorem tridiagonalEigenpairAttemptCount_expectation_tail :
    (∀ m : ℕ, retryBitMeasure n J
      {bits | (m : ℝ≥0∞) < tridiagonalEigenpairAttemptCount a b hJvalid bits} ≤
        ENNReal.ofReal (rejectionBound (n + 1)) ^ m) ∧
    (∫⁻ bits, tridiagonalEigenpairAttemptCount a b hJvalid bits ∂retryBitMeasure n J) ≤
      ENNReal.ofReal ((1 - rejectionBound (n + 1))⁻¹) ∧
    ENNReal.ofReal ((1 - rejectionBound (n + 1))⁻¹) < 2 := by
  have hN : 0 < nextPowerOfTwo (n + 1) :=
    (Nat.succ_pos n).trans_le (le_nextPowerOfTwo (n + 1))
  have hβ : rejectionBound (n + 1) < 1 / 2 := trialRejectionBound_lt_half hN
  have hden : 0 < 1 - rejectionBound (n + 1) := by linarith
  have hmean : ENNReal.ofReal ((1 - rejectionBound (n + 1))⁻¹) < 2 := by
    rw [← ENNReal.ofReal_ofNat, ENNReal.ofReal_lt_ofReal_iff (by norm_num), ← one_div,
      div_lt_iff₀ hden]
    linarith
  cases he : exactBranch a b (requestedRankOrder hJvalid) with
  | some out =>
    simp only [tridiagonalEigenpairAttemptCount, he, lintegral_zero, zero_le, true_and]
    refine ⟨fun m => ?_, hmean⟩
    have hempty : {_bits : ℕ → GateBits n J | (m : ℝ≥0∞) < 0} = ∅ :=
      Set.eq_empty_iff_forall_notMem.mpr fun _ => by simp
    rw [hempty, measure_empty]
    exact bot_le
  | none =>
    obtain ⟨hnonzero, hn⟩ := (exactBranch_eq_none_iff ..).mp he
    cases hr : normalizationExponent a b with
    | none => exact (hnonzero ((normalizationExponent_eq_none_iff a b).mp hr)).elim
    | some r =>
      obtain ⟨ha, hb⟩ := normalizedTrialInput_bounds (J := J) a b hr
      simp only [tridiagonalEigenpairAttemptCount, he, normalizedEigenpairAttemptCount, hr]
      exact (certifiedRetryRun _ _ hn hguard hJ hJvalid ha hb).2

include hguard hJ in
/-- Varying confidence changes the threshold in the same work event. -/
theorem tridiagonalEigenpairWork_confidence :
    (∀ c : ℝ, 0 < c → 1 - ENNReal.ofReal ((n + 1 : ℝ) ^ (-c)) ≤
      retryBitMeasure n J {bits | tridiagonalEigenpairWork a b hJvalid bits ≤
        (retryTrialWorkScale n J p : ℝ≥0∞) * ((polynomialConfidenceTrials c : ℝ≥0∞) + 1)}) ∧
    (∀ ε : ℝ, 0 < ε → ε < 1 → 1 - ENNReal.ofReal ε ≤
      retryBitMeasure n J {bits | tridiagonalEigenpairWork a b hJvalid bits ≤
        (retryTrialWorkScale n J p : ℝ≥0∞) *
          ((arbitraryConfidenceTrials (nextPowerOfTwo (n + 1)) ε : ℝ≥0∞) + 1)}) := by
  let μ := retryBitMeasure n J
  let scale : ℝ≥0∞ := retryTrialWorkScale n J p
  have hmeas := measurable_tridiagonalEigenpairWork a b hJvalid
  have htail := (tridiagonalEigenpairWork_expectation_tail a b hguard hJ hJvalid).2
  have hN := le_nextPowerOfTwo (n + 1)
  refine ⟨?_, ?_⟩
  · intro c hc
    simpa only [Nat.cast_succ] using work_polynomialConfidence μ hmeas scale
      (fun m _ => htail m) (Nat.succ_pos n) hN hc
  · intro ε hε hε1
    exact work_arbitraryConfidence μ hmeas scale ((Nat.succ_pos n).trans_le hN)
      (fun m _ => htail m) hε hε1

end

end NumStability.CertifiedTridiagonalEigenpairs
