import ComputationalMathematics.Source.CertifiedTridiagonalEigenpairs.Retry.Confidence
import ComputationalMathematics.Source.CertifiedTridiagonalEigenpairs.Retry.FiniteTrialTarget
import ComputationalMathematics.Source.CertifiedTridiagonalEigenpairs.FiniteSampler

/-! Probability laws, mean, and work-tail transfers for fresh finite trials. -/

open MeasureTheory
open scoped ENNReal

namespace NumStability.CertifiedTridiagonalEigenpairs

open IndependentRetry

private theorem uniformPi_eq_pi {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α] [Nonempty α]
    [MeasurableSpace α] [MeasurableSingletonClass α] :
    (PMF.uniformOfFintype (ι → α)).toMeasure =
      Measure.pi (fun _ : ι => (PMF.uniformOfFintype α).toMeasure) := by
  classical
  apply Measure.ext_of_singleton
  intro x
  rw [Measure.pi_singleton]
  simp [Fintype.card_pi, ENNReal.inv_pow]

/-- The tuple law is the product of the uniform laws of the individual integers. -/
theorem trialDrawMeasure_eq_pi (n bits : ℕ) :
    trialDrawMeasure n bits =
      Measure.pi (fun _ : Fin n => (PMF.uniformOfFintype (Fin (2 ^ bits))).toMeasure) :=
  uniformPi_eq_pi (ι := Fin n) (α := Fin (2 ^ bits))

/-- The actual sampler's decoded tuple has the one-trial law used by retries. -/
theorem trialDrawMeasure_eq_map_samplerBits (n k : ℕ) :
    (trialBitLaw n k).toMeasure.map (trialDraws n k) = trialDrawMeasure n (rngBits n k) := by
  letI : NeZero (2 ^ rngBits n k) := ⟨by positivity⟩
  rw [PMF.toMeasure_map _ _ Measurable.of_discrete, trialDraws_law]
  rfl

/-- Decode each fresh bit draw using the same sampler used on a single trial. -/
theorem trialStreamMeasure_eq_map_samplerBits (n k : ℕ) :
    (streamMeasure (trialBitLaw n k).toMeasure).map
      (fun x j => trialDraws n k (x j)) = streamMeasure (trialDrawMeasure n (rngBits n k)) := by
  unfold streamMeasure
  rw [Measure.infinitePi_map_pi (fun _ : ℕ => (trialBitLaw n k).toMeasure)
    (f := fun _ : ℕ => trialDraws n k) (fun _ => Measurable.of_discrete)]
  simp_rw [trialDrawMeasure_eq_map_samplerBits]

/-- Bounds for the positive-length retry loop, using the one-trial rejection
certificate at the fixed input. -/
theorem finiteTrial_retryGuarantees {n bits N : ℕ} (hN : 0 < N)
    {reject : Set (TrialDraws n bits)}
    (hβ : trialDrawMeasure n bits reject ≤ ENNReal.ofReal (trialRejectionBound N)) :
    (∀ᵐ x ∂streamMeasure (trialDrawMeasure n bits), ∃ j : ℕ, x j ∉ reject) ∧
    (∀ m : ℕ, streamMeasure (trialDrawMeasure n bits)
      {x | (m : ℝ≥0∞) < retryCount reject x} ≤ ENNReal.ofReal (trialRejectionBound N) ^ m) ∧
    ((∫⁻ x, retryCount reject x ∂streamMeasure (trialDrawMeasure n bits)) ≤
      ENNReal.ofReal ((1 - trialRejectionBound N)⁻¹)) ∧
    ENNReal.ofReal ((1 - trialRejectionBound N)⁻¹) < 2 := by
  have hr : MeasurableSet reject := reject.to_countable.measurableSet
  have hlt := trialRejectionBound_lt_half hN
  have hpos := trialRejectionBound_pos hN
  have hβlt : ENNReal.ofReal (trialRejectionBound N) < 1 := by
    rw [← ENNReal.ofReal_one]
    exact (ENNReal.ofReal_lt_ofReal_iff (by norm_num)).mpr (by linarith)
  refine ⟨ae_exists_accept _ hr (hβ.trans_lt hβlt), ?_, ?_, ?_⟩
  · intro m
    rw [measure_retryCount_tail _ hr]
    gcongr
  · rw [lintegral_retryCount _ hr, ENNReal.ofReal_inv_of_pos (by linarith),
      ENNReal.ofReal_sub _ hpos.le, ENNReal.ofReal_one]
    gcongr
  · rw [← ENNReal.ofReal_ofNat]
    apply (ENNReal.ofReal_lt_ofReal_iff (by norm_num)).mpr
    rw [← one_div, div_lt_iff₀ (by linarith)]
    linarith

/-- Transfer the per-stream work accounting to expected work and the work tail. -/
theorem finiteTrial_workGuarantees {n bits N : ℕ} (hN : 0 < N)
    {reject : Set (TrialDraws n bits)}
    (hβ : trialDrawMeasure n bits reject ≤ ENNReal.ofReal (trialRejectionBound N))
    {work : (ℕ → TrialDraws n bits) → ℝ≥0∞} {scale : ℝ≥0∞}
    (hwork : ∀ x, work x ≤ scale * (retryCount reject x + 1)) :
    ((∫⁻ x, work x ∂streamMeasure (trialDrawMeasure n bits)) ≤ 3 * scale) ∧
    (∀ m : ℕ, streamMeasure (trialDrawMeasure n bits)
      {x | scale * ((m : ℝ≥0∞) + 1) < work x} ≤ ENNReal.ofReal (trialRejectionBound N) ^ m) := by
  have hr : MeasurableSet reject := reject.to_countable.measurableSet
  refine ⟨?_, measure_work_tail_le _ hr hwork hβ⟩
  have ⟨_, _, havg, hlt⟩ := finiteTrial_retryGuarantees hN hβ
  rw [lintegral_retryCount _ hr] at havg
  calc
    _ ≤ scale * ((1 - trialDrawMeasure n bits reject)⁻¹ + 1) := lintegral_work_le _ hr hwork
    _ ≤ scale * (2 + 1) := by gcongr; exact (havg.trans_lt hlt).le
    _ = 3 * scale := by rw [mul_comm]; norm_num

theorem tridiagonalRetryTransfer : SourceTargets.tridiagonalRetryTransfer := by
  intro n k _ _ _ bits reject hβ μ
  exact finiteTrial_retryGuarantees (N := nextPowerOfTwo n) (by unfold nextPowerOfTwo; positivity) hβ

theorem tridiagonalRetryWorkTransfer : SourceTargets.tridiagonalRetryWorkTransfer := by
  intro n k p _ _ _ bits reject work C hβ scale hwork μ
  have hN : 0 < nextPowerOfTwo n := by unfold nextPowerOfTwo; positivity
  obtain ⟨hmean, htail⟩ := finiteTrial_workGuarantees hN hβ hwork
  exact ⟨hmean, fun m _ => htail m⟩

end NumStability.CertifiedTridiagonalEigenpairs
