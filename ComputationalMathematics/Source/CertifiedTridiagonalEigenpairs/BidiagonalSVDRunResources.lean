import ComputationalMathematics.Source.CertifiedTridiagonalEigenpairs.BidiagonalSVDResourceTarget

/-! Complete work, peak words and the polynomial confidence bound of the selected SVD. -/

open MeasureTheory
open scoped ENNReal

namespace NumStability.CertifiedTridiagonalEigenpairs.BidiagonalSVDRequest

open FloatingPointFormat.UnboundedBinary ScalarWork

noncomputable section

variable {n k p : ℕ} {hp : 2 ≤ p}
variable {upper : Bool} {a : Fin (n + 1) → Word p hp} {b : Fin n → Word p hp}
  {I : Fin k ↪o Fin (n + 1)}
  {cmp : EmptyBinScan.Comparison (svdLabelPrecision k p) (svdLabelPrecision_ge_two k p)}
  {hk : 1 ≤ k} {hguard : precisionGuard (n + 1) p}

theorem dispatchTrace_work (d : ℕ) (hd : 1 ≤ d) :
    ScalarWork.work (dispatchTrace d) ≤ 18 * d := by
  simp [dispatchTrace, ScalarWork.work]
  omega

theorem exactWriteTrace_work (d k : ℕ) :
    ScalarWork.work (exactWriteTrace d k) = 8 * (d * k) + 3 * k := by
  simp [exactWriteTrace, ScalarWork.work]
  ring

theorem RunPlan.measurable_work (plan : RunPlan upper a b I cmp hk hguard) :
    Measurable plan.work := by
  cases plan with
  | exact => exact measurable_const
  | nontrivial _ call =>
    exact measurable_const.add
      (measurable_normalizedEigenpairWork call.diagonal.get call.edges.get call.oneBasedRanks_subset)

/-- The recorded work diverges exactly when the same native run has no return. -/
theorem RunPlan.work_eq_top_iff (plan : RunPlan upper a b I cmp hk hguard) (bits : plan.Bits) :
    plan.work bits = ⊤ ↔ plan.run bits = none := by
  cases plan with
  | exact => simp [RunPlan.work, RunPlan.run, ENNReal.natCast_ne_top]
  | nontrivial hn call hprep hscale =>
    rw [RunPlan.nontrivial_run_eq_none hn call hprep hscale bits]
    let legal := call.admissible hk hguard
    simp only [RunPlan.work, ENNReal.add_eq_top, ENNReal.natCast_ne_top, false_or]
    exact normalizedEigenpairWork_eq_top_iff call.diagonal.get call.edges.get legal.1
      legal.2.2.2.2.2.1 legal.2.1 call.oneBasedRanks_subset bits

include hp I hk in
private theorem base_factors :
    k ≤ n + 1 ∧ n + 1 ≤ (n + 1) * k ∧ k ≤ (n + 1) * k ∧
      (n + 1) * k ≤ (n + 1) * k * p := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa using Fintype.card_le_of_injective I I.injective
  · simpa using Nat.mul_le_mul_left (n + 1) hk
  · simpa using Nat.mul_le_mul_right k (Nat.le_add_left 1 n)
  · simpa using Nat.mul_le_mul_left ((n + 1) * k) (show 1 ≤ p by omega)

private theorem TridiagonalCall.outerWork_le (hn : 2 ≤ n + 1) (call : TridiagonalCall n k p)
    (hprep : prepareTridiagonalCall upper a b I cmp hn hk hguard I.strictMono = some call) :
    call.outerWork upper a b I cmp ≤ 1200 * ((n + 1) * k * p) := by
  obtain ⟨hkn, hn', hk', hkp⟩ := base_factors (hp := hp) (I := I) (hk := hk)
  have hdispatch := dispatchTrace_work (n + 1) (by omega)
  have hprepWork := (call.preparation_resources upper a b I cmp hn hk hguard I.strictMono hprep).1
  let flags := assembleLowFlags cmp call.preprocessing call.labelCount
  have hf := (lowFlagsTrace_resources (svdWorkingPrecision (n + 1) k p) k).1
  have hr := (call.nativeRankPlan_resources flags (svdWorkingPrecision (n + 1) k p)).1
  have hfinish := (finish_resources (n + 1) k p (by omega) hk hkn hp).1
  change ScalarWork.work (dispatchTrace (n + 1)) + ScalarWork.work (call.preparationTrace upper a b I) +
    ScalarWork.work (lowFlagsTrace k) + ScalarWork.work (call.nativeRankPlanTrace flags) +
    ScalarWork.work (finishTrace (n + 1) k p) ≤ _
  omega

include hk hguard in
private theorem TridiagonalCall.retryScale_le (call : TridiagonalCall n k p) :
    retryTrialWorkScale (edgeCount n) call.oneBasedRanks (svdAuxiliaryPrecision k p) ≤
      64000 * ((n + 1) * k * p) := by
  have hkn : k ≤ n + 1 := by simpa using Fintype.card_le_of_injective call.slots call.slots.injective
  have hr := (call.admissible hk hguard).2.2.2.2.1
  have h := (svd_tridiagonal_resource_factors_le (by omega : 0 < k) hkn hr hguard).1
  have hd : edgeCount n + 1 = 2 * (n + 1) := by unfold edgeCount; omega
  unfold retryTrialWorkScale
  rw [hd, show 4000 * (2 * (n + 1)) * call.oneBasedRanks.card * svdAuxiliaryPrecision k p =
      4000 * ((2 * (n + 1)) * call.oneBasedRanks.card * svdAuxiliaryPrecision k p) by ring]
  omega

include hp hk in
private theorem exactWork_le :
    ScalarWork.work (dispatchTrace (n + 1)) + ScalarWork.work (exactWriteTrace (n + 1) k) ≤
      32 * ((n + 1) * k * p) := by
  have hn' : n + 1 ≤ (n + 1) * k := by simpa using Nat.mul_le_mul_left (n + 1) hk
  have hk' : k ≤ (n + 1) * k := by simpa using Nat.mul_le_mul_right k (Nat.le_add_left 1 n)
  have hp' : (n + 1) * k ≤ (n + 1) * k * p := by
    simpa using Nat.mul_le_mul_left ((n + 1) * k) (show 1 ≤ p by omega)
  rw [exactWriteTrace_work]
  have ht := dispatchTrace_work (n + 1) (by omega)
  omega

/-- Uniform pathwise bound including the full tridiagonal retry workspace,
its returned accepted arrays, and explicit storage of both SVD families. -/
theorem RunPlan.workspaceBound_le (plan : RunPlan upper a b I cmp hk hguard) (bits : plan.Bits) :
    plan.workspaceBound bits ≤ 500 * ((n + 1) + (n + 1) * k) := by
  obtain ⟨hkn, hn', hk', _⟩ := base_factors (hp := hp) (I := I) (hk := hk)
  cases plan with
  | exact => simp only [workspaceBound, exactPeakWords]; omega
  | nontrivial hn call hprep _ =>
    let legal := call.admissible hk hguard
    let flags := assembleLowFlags cmp call.preprocessing call.labelCount
    have hP := (call.preparation_resources upper a b I cmp hn hk hguard I.strictMono hprep).2.1
    have hR := (call.nativeRankPlan_resources flags (svdWorkingPrecision (n + 1) k p)).2.1
    have hF := (finish_resources (n + 1) k p (by omega) hk hkn hp).2.1
    have hO := normalizedEigenpairWorkspace_le call.diagonal.get call.edges.get bits
      legal.1 legal.2.2.2.2.2.1 legal.2.1 call.oneBasedRanks_subset
    have hS := (svd_tridiagonal_resource_factors_le (by omega : 0 < k) hkn
      legal.2.2.2.2.1 hguard).2
    have hd : edgeCount n + 1 = 2 * (n + 1) := by unfold edgeCount; omega
    have hSize : edgeCount n + 1 + (edgeCount n + 1) * call.oneBasedRanks.card ≤
        4 * ((n + 1) + (n + 1) * k) := by rw [hd]; exact hS
    change storage (call.preparationLiveWords upper a b I) + k +
      storage (call.nativeRankPlanLiveWords flags) +
      normalizedEigenpairWorkspace call.diagonal.get call.edges.get bits
        legal.1 legal.2.2.2.2.2.1 legal.2.1 call.oneBasedRanks_subset +
      (if (call.solve hk hguard bits).isSome then storage (finishLiveWords (n + 1) k) else 0) ≤ _
    split <;> omega

/-- The expected complete work on the same streams as the returned triplets. -/
theorem RunPlan.expectation_work_le (plan : RunPlan upper a b I cmp hk hguard) :
    (∫⁻ bits, plan.work bits ∂plan.bitMeasure) ≤ (200000 * ((n + 1) * k * p) : ℕ) := by
  cases plan with
  | exact =>
    change (∫⁻ _ : Unit, ((ScalarWork.work (dispatchTrace (n + 1)) +
      ScalarWork.work (exactWriteTrace (n + 1) k) : ℕ) : ℝ≥0∞) ∂Measure.dirac ()) ≤ _
    rw [lintegral_const]
    simp only [measure_univ, mul_one, Nat.cast_le]
    have h := exactWork_le (n := n) (hp := hp) (hk := hk)
    omega
  | nontrivial hn call hprep _ =>
    let μ := retryBitMeasure (edgeCount n) call.oneBasedRanks
    let ω := normalizedEigenpairWork call.diagonal.get call.edges.get call.oneBasedRanks_subset
    let legal := call.admissible hk hguard
    let outer := call.outerWork upper a b I cmp
    have hnz := prepareTridiagonalCall_nonzero upper a b I cmp hn hk hguard I.strictMono hprep
    have hμ := (normalizedEigenpairWork_expectation_tail call.diagonal.get call.edges.get
      legal.1 legal.2.2.2.2.2.1 legal.2.1 call.oneBasedRanks_subset hnz).1
    have houter := call.outerWork_le hn hprep
    have hscale := call.retryScale_le (hk := hk) (hguard := hguard)
    have hsum : outer + 3 * retryTrialWorkScale (edgeCount n) call.oneBasedRanks
        (svdAuxiliaryPrecision k p) ≤ 200000 * ((n + 1) * k * p) :=
      (Nat.add_le_add houter (Nat.mul_le_mul_left 3 hscale)).trans (by omega)
    change (∫⁻ bits, (outer : ℝ≥0∞) + ω bits ∂μ) ≤ _
    rw [lintegral_add_left measurable_const, lintegral_const]
    simp only [measure_univ, mul_one]
    refine (add_le_add (le_refl (outer : ℝ≥0∞)) hμ).trans ?_
    exact_mod_cast hsum

/-- Polynomial confidence for the complete observed SVD work. The real
parameter changes the work threshold on the very same run and bit law. -/
theorem RunPlan.work_confidence (plan : RunPlan upper a b I cmp hk hguard)
    (c : ℝ) (hc : 0 < c) :
    1 - ENNReal.ofReal ((n + 1 : ℝ) ^ (-c)) ≤
      plan.bitMeasure {bits | plan.work bits ≤
        ((66000 * ((n + 1) * k * p) : ℕ) : ℝ≥0∞) *
          ((polynomialConfidenceTrials c : ℝ≥0∞) + 1)} := by
  let scale : ℝ≥0∞ := (66000 * ((n + 1) * k * p) : ℕ)
  let m : ℝ≥0∞ := (polynomialConfidenceTrials c : ℝ≥0∞) + 1
  have hm : 1 ≤ m := by dsimp [m]; exact le_add_self
  cases plan with
  | exact =>
    change _ ≤ (Measure.dirac ()) {bits : Unit | _ ≤ scale * m}
    rw [Measure.dirac_apply_of_mem]
    · exact tsub_le_self
    · have h := exactWork_le (n := n) (hp := hp) (hk := hk)
      have h' : ((ScalarWork.work (dispatchTrace (n + 1)) +
          ScalarWork.work (exactWriteTrace (n + 1) k) : ℕ) : ℝ≥0∞) ≤ scale := by
        dsimp [scale]
        exact_mod_cast (show ScalarWork.work (dispatchTrace (n + 1)) +
          ScalarWork.work (exactWriteTrace (n + 1) k) ≤ 66000 * ((n + 1) * k * p) by omega)
      exact h'.trans (le_mul_of_one_le_right (zero_le _) hm)
  | nontrivial hn call hprep _ =>
    let μ := retryBitMeasure (edgeCount n) call.oneBasedRanks
    let ω := normalizedEigenpairWork call.diagonal.get call.edges.get call.oneBasedRanks_subset
    let legal := call.admissible hk hguard
    let outer := call.outerWork upper a b I cmp
    let oracleScale : ℕ := retryTrialWorkScale (edgeCount n) call.oneBasedRanks
      (svdAuxiliaryPrecision k p)
    have hnz := prepareTridiagonalCall_nonzero upper a b I cmp hn hk hguard I.strictMono hprep
    have hconfidence := (normalizedEigenpairWork_confidence call.diagonal.get call.edges.get
      legal.1 legal.2.2.2.2.2.1 legal.2.1 call.oneBasedRanks_subset hnz).1 c hc
    have houter := call.outerWork_le hn hprep
    have hscale := call.retryScale_le (hk := hk) (hguard := hguard)
    have hsum : (outer : ℝ≥0∞) + oracleScale ≤ scale := by
      dsimp [scale]
      exact_mod_cast (show outer + oracleScale ≤ 66000 * ((n + 1) * k * p) from
        (Nat.add_le_add houter hscale).trans (by omega))
    have hdim : edgeCount n + 1 = 2 * (n + 1) := by unfold edgeCount; omega
    have hdim' : (edgeCount n : ℝ) + 1 = 2 * (n + 1 : ℝ) := by exact_mod_cast hdim
    have hpow : ((edgeCount n : ℝ) + 1) ^ (-c) ≤ (n + 1 : ℝ) ^ (-c) := by
      rw [hdim']
      simpa only [Nat.cast_succ] using svd_polynomial_failure_probability_le (Nat.succ_pos n) hc
    refine (tsub_le_tsub_left (ENNReal.ofReal_le_ofReal hpow) 1).trans
      (hconfidence.trans (measure_mono ?_))
    change {bits | ω bits ≤ (oracleScale : ℝ≥0∞) * m} ⊆
      {bits | (outer : ℝ≥0∞) + ω bits ≤ scale * m}
    intro bits hbits
    change ω bits ≤ (oracleScale : ℝ≥0∞) * m at hbits
    change (outer : ℝ≥0∞) + ω bits ≤ scale * m
    calc
      _ ≤ (outer : ℝ≥0∞) * m + (oracleScale : ℝ≥0∞) * m := by
        simpa only [one_mul] using add_le_add
          (le_mul_of_one_le_right (zero_le (outer : ℝ≥0∞)) hm) hbits
      _ = ((outer : ℝ≥0∞) + oracleScale) * m := (add_mul ..).symm
      _ ≤ scale * m := mul_le_mul_left hsum _

/-- The exact branch cap is the input precision; the remaining stages fit
the paper's SVD working precision and its simplified guard-dependent bound. -/
theorem RunPlan.precision_le (plan : RunPlan upper a b I cmp hk hguard) :
    p ≤ plan.precision ∧ plan.precision ≤ svdWorkingPrecision (n + 1) k p ∧
      plan.precision ≤ 10 * p + 14 := by
  cases plan with
  | exact =>
    change p ≤ p ∧ p ≤ svdWorkingPrecision (n + 1) k p ∧ p ≤ 10 * p + 14
    exact ⟨le_rfl, (svd_stage_precisions_le (n + 1) k p).2.2, by omega⟩
  | nontrivial hn call =>
    have hkn : k ≤ n + 1 := by simpa using Fintype.card_le_of_injective I I.injective
    exact ⟨(svd_stage_precisions_le (n + 1) k p).2.2, le_rfl,
      svdWorkingPrecision_le hn hkn hguard⟩

theorem RunPlan.nontrivial_precision (hn : 2 ≤ n + 1) (call : TridiagonalCall n k p)
    (hprep : prepareTridiagonalCall upper a b I cmp hn hk hguard I.strictMono = some call)
    (hscale : ∃ r, normalizationExponent a b = some r) :
    let plan : RunPlan upper a b I cmp hk hguard := .nontrivial hn call hprep hscale
    let flags := assembleLowFlags cmp call.preprocessing call.labelCount
    TraceAllowed plan.precision (call.preparationTrace upper a b I) ∧
      TraceAllowed plan.precision (lowFlagsTrace k) ∧
      TraceAllowed plan.precision (call.nativeRankPlanTrace flags) ∧
      TraceAllowed plan.precision (finishTrace (n + 1) k p) ∧
      workingPrecision (edgeCount n + 1) call.oneBasedRanks.card
        (svdAuxiliaryPrecision k p) ≤ plan.precision := by
  intro plan flags
  have hkn : k ≤ n + 1 := by simpa using Fintype.card_le_of_injective I I.injective
  exact ⟨(call.preparation_resources upper a b I cmp hn hk hguard I.strictMono hprep).2.2,
    (lowFlagsTrace_resources plan.precision k).2,
    (call.nativeRankPlan_resources flags plan.precision).2.2,
    (finish_resources (n + 1) k p (by omega) hk hkn hp).2.2,
    (call.admissible hk hguard).2.2.2.2.2.2⟩

/-- Deterministic work outside the oracle fits in the same pathwise
trial-count bound as every rejected trial and the accepted output. -/
theorem RunPlan.work_le_attemptCount (plan : RunPlan upper a b I cmp hk hguard) (bits : plan.Bits) :
    plan.work bits ≤ ((66000 * ((n + 1) * k * p) : ℕ) : ℝ≥0∞) *
      (plan.attemptCount bits + 1) := by
  let scale : ℝ≥0∞ := (66000 * ((n + 1) * k * p) : ℕ)
  cases plan with
  | exact =>
    simp only [RunPlan.work, RunPlan.attemptCount, zero_add, mul_one, Nat.cast_le]
    have h := exactWork_le (n := n) (hp := hp) (hk := hk)
    omega
  | nontrivial hn call hprep _ =>
    let legal := call.admissible hk hguard
    let outer := call.outerWork upper a b I cmp
    let oracleScale : ℕ := retryTrialWorkScale (edgeCount n) call.oneBasedRanks
      (svdAuxiliaryPrecision k p)
    let m := normalizedEigenpairAttemptCount call.diagonal.get call.edges.get bits + 1
    have hm : 1 ≤ m := le_add_self
    have horacle := normalizedEigenpairWork_le call.diagonal.get call.edges.get
      legal.1 legal.2.2.2.2.2.1 legal.2.1 call.oneBasedRanks_subset bits
    have houter := call.outerWork_le hn hprep
    have hscale := call.retryScale_le (hk := hk) (hguard := hguard)
    have hsum : (outer : ℝ≥0∞) + oracleScale ≤ scale := by
      dsimp [scale]
      exact_mod_cast (show outer + oracleScale ≤ 66000 * ((n + 1) * k * p) from
        (Nat.add_le_add houter hscale).trans (by omega))
    change (outer : ℝ≥0∞) + _ ≤ scale * m
    calc
      _ ≤ (outer : ℝ≥0∞) * m + (oracleScale : ℝ≥0∞) * m :=
        add_le_add (le_mul_of_one_le_right (zero_le _) hm) horacle
      _ = ((outer : ℝ≥0∞) + oracleScale) * m := (add_mul ..).symm
      _ ≤ scale * m := mul_le_mul_left hsum m


/-- The oracle prefix on a returned run is exactly the number of trials
recorded by that oracle, with no omission of earlier rejected trials. -/
theorem RunPlan.work_eq_of_prepared_returns (hn : 2 ≤ n + 1) (call : TridiagonalCall n k p)
    (hprep : prepareTridiagonalCall upper a b I cmp hn hk hguard I.strictMono = some call)
    (hscale : ∃ r, normalizationExponent a b = some r)
    (bits : ℕ → GateBits (edgeCount n) call.oneBasedRanks) (out : call.NativeParities)
    (hrun : call.solvePreparedParities hn hprep bits = some out) :
    let plan : RunPlan upper a b I cmp hk hguard := .nontrivial hn call hprep hscale
    let av := fun i => normalizeTrialWord out.oracle.scaleExponent (call.diagonal.get i)
    let bv := fun i => normalizeTrialWord out.oracle.scaleExponent (call.edges.get i)
    let trialOps := trialTracePrefix av bv bits (out.oracle.accepted.index + 1)
    plan.work bits = (call.outerWork upper a b I cmp : ℝ≥0∞) +
      ((ScalarWork.work (normalizationSetupTrace call.diagonal.get call.edges.get
        call.oneBasedRanks) : ℝ≥0∞) +
       (ScalarWork.work trialOps : ℝ≥0∞) +
       ((normalizedAcceptedOutputUsage call.edges.get call.oneBasedRanks_subset out.oracle).work :
        ℝ≥0∞)) ∧
      TraceAllowed plan.precision trialOps ∧
      trialOps.countP isFairBit = (out.oracle.accepted.index + 1) *
        ((edgeCount n + 1) * rngBits (edgeCount n + 1) call.oneBasedRanks.card) := by
  intro plan av bv trialOps
  let legal := call.admissible hk hguard
  have hsolved := (call.solvePreparedParities_eq hn hprep bits).symm.trans hrun
  have horacle := (call.solveParities_native upper hk hguard bits out hsolved).1
  have hrunOracle : normalizedEigenpairRun call.diagonal.get call.edges.get bits legal.1
      legal.2.2.2.2.2.1 legal.2.1 call.oneBasedRanks_subset = some out.oracle := horacle
  have hRetry := normalizedEigenpairRun_acceptance call.diagonal.get call.edges.get bits
    legal.1 legal.2.2.2.2.2.1 legal.2.1 call.oneBasedRanks_subset
  rw [hrunOracle, Option.map_some] at hRetry
  obtain ⟨hr, _⟩ := normalizedRetryRun_some hRetry.symm
  obtain ⟨ha, hb⟩ := normalizedTrialInput_bounds (J := call.oneBasedRanks)
    call.diagonal.get call.edges.get hr
  refine ⟨?_, ?_, ?_⟩
  · change (call.outerWork upper a b I cmp : ℝ≥0∞) + _ = _
    rw [normalizedEigenpairWork_eq_of_returns call.diagonal.get call.edges.get legal.1
      legal.2.2.2.2.2.1 legal.2.1 call.oneBasedRanks_subset hrunOracle]
  · have hallowed := trialTracePrefix_allowed (a := av) (b := bv) (bits := bits) legal.1 legal.2.2.2.2.2.1 legal.2.1
      call.oneBasedRanks_subset ha hb (out.oracle.accepted.index + 1)
    have hcap : workingPrecision (edgeCount n + 1) call.oneBasedRanks.card
        (svdAuxiliaryPrecision k p) ≤ plan.precision := legal.2.2.2.2.2.2
    intro step hstep
    have h := hallowed step hstep
    cases step with
    | arithmetic q => exact ⟨h.1, h.2.trans hcap⟩
    | conversion s t => exact ⟨h.1, h.2.1.trans hcap, h.2.2.1, h.2.2.2.trans hcap⟩
    | _ => trivial
  · exact trialTracePrefix_fairBits (a := av) (b := bv) (bits := bits) legal.1 legal.2.2.2.2.2.1 legal.2.1
      call.oneBasedRanks_subset ha hb (out.oracle.accepted.index + 1)

/-- Exact plans use the input precision. A nontrivial plan cannot arise on
a zero matrix or a scalar input. -/
theorem RunPlan.precision_eq_input_of_exact (plan : RunPlan upper a b I cmp hk hguard)
    (he : storedBidiagonal upper a b = 0 ∨ n = 0) :
    plan.precision = p := by
  cases plan with
  | exact => rfl
  | nontrivial hn call hprep hscale =>
    obtain ⟨r, hr⟩ := hscale
    rcases he with hzero | hscalar
    · have hnone := (bidiagonal_normalizationExponent_eq_none_iff upper a b).mpr hzero
      rw [hnone] at hr
      contradiction
    · omega


private theorem dispatchTrace_allowed (d cap : ℕ) : TraceAllowed cap (dispatchTrace d) := by
  intro step hs
  simp only [dispatchTrace, List.mem_append, List.mem_flatten, List.mem_replicate] at hs
  rcases hs with ⟨_, ⟨_, rfl⟩, hs⟩ | hs
  all_goals cases step <;> simp [Step.Allowed] at hs ⊢

private theorem exactWriteTrace_allowed (d k cap : ℕ) : TraceAllowed cap (exactWriteTrace d k) := by
  intro step hs
  simp only [exactWriteTrace, List.mem_append, List.mem_flatten, List.mem_replicate] at hs
  rcases hs with ⟨_, ⟨_, rfl⟩, hs⟩ | ⟨_, ⟨_, rfl⟩, hs⟩
  all_goals cases step <;> simp [Step.Allowed] at hs ⊢

/-- The floating-point steps in the actual bidiagonal phases and every trial
prefix respect the cap determined before random bits are drawn. -/
theorem RunPlan.respectsPrecision (plan : RunPlan upper a b I cmp hk hguard) :
    plan.RespectsPrecision := by
  cases plan with
  | exact =>
    intro step hs
    change step ∈ dispatchTrace (n + 1) ++ exactWriteTrace (n + 1) k at hs
    rcases List.mem_append.mp hs with hs | hs
    · exact dispatchTrace_allowed _ _ _ hs
    · exact exactWriteTrace_allowed _ _ _ _ hs
  | nontrivial hn call hprep hscale =>
    obtain ⟨hP, hF, hR, hO, hcap⟩ :=
      RunPlan.nontrivial_precision hn call hprep hscale
    refine ⟨dispatchTrace_allowed _ _, hP, hF, hR, hO, hcap, ?_⟩
    intro e he bits m step hs
    let legal := call.admissible hk hguard
    obtain ⟨ha, hb⟩ := normalizedTrialInput_bounds (J := call.oneBasedRanks)
      call.diagonal.get call.edges.get he
    have h := trialTracePrefix_allowed (bits := bits) legal.1 legal.2.2.2.2.2.1
      legal.2.1 call.oneBasedRanks_subset ha hb m step hs
    cases step with
    | arithmetic q => exact ⟨h.1, h.2.trans hcap⟩
    | conversion s t => exact ⟨h.1, h.2.1.trans hcap, h.2.2.1, h.2.2.2.trans hcap⟩
    | _ => trivial

/-- The work, storage, confidence, and precision bounds for the actual
prepared execution with the default stored-word comparisons. -/
theorem svdCompleteResources : SourceTargets.svdCompleteResources := by
  intro n k p hp upper a b I hk hguard
  dsimp only
  let plan := prepareRun upper a b I (EmptyBinScan.defaultComparison
    (svdLabelPrecision k p) (svdLabelPrecision_ge_two k p)) hk hguard
  exact ⟨plan.expectation_work_le, plan.workspaceBound_le, plan.work_confidence,
    plan.work_le_attemptCount, plan.respectsPrecision, plan.precision_le,
    plan.precision_eq_input_of_exact⟩


end

end NumStability.CertifiedTridiagonalEigenpairs.BidiagonalSVDRequest
