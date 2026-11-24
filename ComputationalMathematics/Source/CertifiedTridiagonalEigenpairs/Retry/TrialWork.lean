import ComputationalMathematics.Source.CertifiedTridiagonalEigenpairs.Retry.CertifiedExecution

/-!
# Work charged by the perturb-and-retry loop

Each started trial contributes its actual rounded gate trace. The trace includes
random-bit generation and all operations of rejected as well as accepted trials.
The nonnegative work on an infinite execution is the sum over all started trials.
-/

open MeasureTheory
open scoped ENNReal

namespace NumStability.CertifiedTridiagonalEigenpairs

open IndependentRetry ScalarWork

variable {n p : ℕ} {J : Finset ℕ}

/-- Concatenate the traces of this many consecutive invocations of the gate. -/
noncomputable def trialTracePrefix
    (a : Fin (n + 1) → TrialWord n J p) (b : Fin n → TrialWord n J p)
    (bits : ℕ → GateBits n J) : ℕ → List Step
  | 0 => []
  | m + 1 => trialTracePrefix a b bits m ++ trialTrace a b (bits m)

/-- For a returning run the complete perturbation trace ends at the accepted trial. -/
noncomputable def retryTrialTrace
    (a : Fin (n + 1) → TrialWord n J p) (b : Fin n → TrialWord n J p)
    (bits : ℕ → GateBits n J) : Option (List Step) :=
  (retryRun a b bits).map fun result => trialTracePrefix a b bits (result.index + 1)

/-- Work of the perturbation loop on a complete stream of bit blocks. Trial `j`
is charged precisely when the preceding `j` invocations all reject. -/
noncomputable def retryTrialWork
    (a : Fin (n + 1) → TrialWord n J p) (b : Fin n → TrialWord n J p)
    (bits : ℕ → GateBits n J) : ℝ≥0∞ :=
  ∑' j : ℕ, (rejectionPrefix (trialRejected n p J a b) j).indicator
    (fun x => (work (trialTrace a b (x j)) : ℝ≥0∞)) bits

/-- A bound on the work of one complete trial, at the guarded output precision. -/
def retryTrialWorkScale (n : ℕ) (J : Finset ℕ) (p : ℕ) : ℕ := 4000 * (n + 1) * J.card * p

section Work

variable {a : Fin (n + 1) → TrialWord n J p} {b : Fin n → TrialWord n J p}
  {bits : ℕ → GateBits n J} {result : RetryResult n J p}

private theorem trialTracePrefix_work (m : ℕ) :
    work (trialTracePrefix a b bits m) = ∑ j ∈ Finset.range m, work (trialTrace a b (bits j)) := by
  induction m with
  | zero => simp [trialTracePrefix, work]
  | succ m ih => simpa [trialTracePrefix, Finset.sum_range_succ, ← ih, work]

theorem retryTrialTrace_eq_some (h : retryRun a b bits = some result) :
    retryTrialTrace a b bits = some (trialTracePrefix a b bits (result.index + 1)) := by
  simp [retryTrialTrace, h]

private theorem attempted_iff (h : retryRun a b bits = some result) (j : ℕ) :
    bits ∈ rejectionPrefix (trialRejected n p J a b) j ↔ j ≤ result.index := by
  rw [← retryCount_tail_event, Set.mem_setOf_eq, retryRun_retryCount_eq h, ← Nat.cast_one,
    ← Nat.cast_add, Nat.cast_lt]
  omega

theorem retryTrialWork_eq_work_prefix (h : retryRun a b bits = some result) :
    retryTrialWork a b bits = (work (trialTracePrefix a b bits (result.index + 1)) : ℝ≥0∞) := by
  classical
  rw [retryTrialWork, tsum_eq_sum (s := Finset.range (result.index + 1))]
  · rw [trialTracePrefix_work, Nat.cast_sum]
    refine Finset.sum_congr rfl fun j hj => Set.indicator_of_mem ?_ _
    exact (attempted_iff h j).mpr (Nat.le_of_lt_succ (Finset.mem_range.mp hj))
  · intro j hj
    apply Set.indicator_of_notMem
    simpa only [Finset.mem_range, Nat.lt_succ_iff, attempted_iff h] using hj

theorem measurable_retryTrialWork (a : Fin (n + 1) → TrialWord n J p)
    (b : Fin n → TrialWord n J p) : Measurable (retryTrialWork a b) := by
  have hr : MeasurableSet (trialRejected n p J a b) := (trialRejected n p J a b).to_countable.measurableSet
  apply Measurable.ennreal_tsum
  intro j
  have hcost : Measurable (fun words : GateBits n J => (work (trialTrace a b words) : ℝ≥0∞)) :=
    Measurable.of_discrete
  exact (hcost.comp (measurable_pi_apply j)).indicator (measurableSet_rejectionPrefix hr j)

private theorem retryCount_le_retryTrialWork :
    retryCount (trialRejected n p J a b) bits ≤ retryTrialWork a b bits := by
  unfold retryCount retryTrialWork
  refine ENNReal.tsum_le_tsum fun j => ?_
  by_cases hj : bits ∈ rejectionPrefix (trialRejected n p J a b) j
  · rw [Set.indicator_of_mem hj, Set.indicator_of_mem hj]
    norm_cast
    simp [trialTrace, work]
    omega
  · simp only [Set.indicator_of_notMem hj, le_rfl]

theorem retryTrialWork_eq_top_iff : retryTrialWork a b bits = ⊤ ↔ retryRun a b bits = none := by
  cases h : retryRun a b bits with
  | none =>
    have hcount := retryRun_count_top_iff.mpr h
    have hwork : retryTrialWork a b bits = ⊤ := top_unique (hcount ▸ retryCount_le_retryTrialWork)
    simp [hwork]
  | some result => simp [retryTrialWork_eq_work_prefix h]

section Bounds

variable (hn : 2 ≤ n + 1) (hguard : precisionGuard (n + 1) p)
  (hJ : J.Nonempty) (hJbounds : J ⊆ Finset.Icc 1 (n + 1))
  (ha : ∀ i, |(a i).value| ≤ 1 / 4) (hb : ∀ i, |(b i).value| ≤ 1 / 4)

include hn hguard hJ hJbounds ha hb

private theorem trialTrace_work_le (words : GateBits n J) :
    work (trialTrace a b words) ≤ retryTrialWorkScale n J p := by
  obtain ⟨_, _, _, _, _, _, _, hwork, _⟩ := finiteTrialCertificate n p J a b hn hguard hJ hJbounds ha hb words
  have hL := clog_add_le_of_precisionGuard (by omega : 0 < n + 1) hguard
  calc
    _ ≤ 2000 * (n + 1) * J.card * (p + Nat.clog 2 (n + 1)) := hwork
    _ ≤ 2000 * (n + 1) * J.card * (2 * p) := by gcongr; omega
    _ = _ := by unfold retryTrialWorkScale; ring

/-- The prefix repeats exactly the prescribed sampler bit budget on each trial. -/
theorem trialTracePrefix_fairBits (m : ℕ) :
    (trialTracePrefix a b bits m).countP isFairBit = m * ((n + 1) * rngBits (n + 1) J.card) := by
  induction m with
  | zero => simp [trialTracePrefix]
  | succ m ih =>
    obtain ⟨_, _, _, _, _, _, hbits, _, _⟩ := finiteTrialCertificate n p J a b hn hguard hJ hJbounds ha hb (bits m)
    rw [trialTracePrefix, List.countP_append, ih, hbits]
    ring

/-- Every started trial's trace respects the common working precision. -/
theorem trialTracePrefix_allowed (m : ℕ) :
    TraceAllowed (workingPrecision (n + 1) J.card p) (trialTracePrefix a b bits m) := by
  induction m with
  | zero => simp [trialTracePrefix, TraceAllowed]
  | succ m ih =>
    obtain ⟨_, _, _, _, _, _, _, _, hallowed⟩ := finiteTrialCertificate n p J a b hn hguard hJ hJbounds ha hb (bits m)
    intro step hs
    rw [trialTracePrefix, List.mem_append] at hs
    exact hs.elim (ih step) (hallowed step)

/-- Pathwise perturbation work is bounded by the per-trial budget times the
number of trial invocations, including rejected ones. -/
theorem retryTrialWork_le :
    retryTrialWork a b bits ≤ (retryTrialWorkScale n J p : ℝ≥0∞) *
      retryCount (trialRejected n p J a b) bits := by
  unfold retryTrialWork retryCount
  rw [← ENNReal.tsum_mul_left]
  refine ENNReal.tsum_le_tsum fun j => ?_
  by_cases hj : bits ∈ rejectionPrefix (trialRejected n p J a b) j
  · rw [Set.indicator_of_mem hj, Set.indicator_of_mem hj, mul_one]
    exact Nat.cast_le.mpr (trialTrace_work_le hn hguard hJ hJbounds ha hb (bits j))
  · simp only [Set.indicator_of_notMem hj, mul_zero, le_rfl]

/-- Expected work and the work tail for the complete perturbation phase. -/
theorem retryTrialWork_expectation_tail :
    (∫⁻ bits, retryTrialWork a b bits ∂retryBitMeasure n J) ≤
        (retryTrialWorkScale n J p : ℝ≥0∞) * 2 ∧
    ∀ m : ℕ, retryBitMeasure n J
      {bits | (retryTrialWorkScale n J p : ℝ≥0∞) * (m : ℝ≥0∞) < retryTrialWork a b bits} ≤
        ENNReal.ofReal (rejectionBound (n + 1)) ^ m := by
  obtain ⟨_, htail, hmean, hlt⟩ := certifiedRetryRun a b hn hguard hJ hJbounds ha hb
  have hwork := fun bits : ℕ → GateBits n J => retryTrialWork_le (bits := bits) hn hguard hJ hJbounds ha hb
  constructor
  · refine (lintegral_mono hwork).trans ?_
    have hr : MeasurableSet (trialRejected n p J a b) := (trialRejected n p J a b).to_countable.measurableSet
    rw [lintegral_const_mul _ (measurable_retryCount hr)]
    gcongr
    exact hmean.trans hlt.le
  · intro m
    refine (measure_mono ?_).trans (htail m)
    intro x hx
    change _ < retryTrialWork a b x at hx
    change (m : ℝ≥0∞) < retryCount (trialRejected n p J a b) x
    by_contra! hm
    exact (not_lt_of_ge ((hwork x).trans (by gcongr))) hx

end Bounds
end Work

end NumStability.CertifiedTridiagonalEigenpairs
