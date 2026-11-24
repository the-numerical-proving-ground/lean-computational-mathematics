import ComputationalMathematics.Source.CertifiedTridiagonalEigenpairs.ArithmeticWorkModelSuccessorTarget

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace NumStability.CertifiedTridiagonalEigenpairs

open FloatingPointFormat.UnboundedBinary
open ScalarWork
open ArithmeticNotation

private theorem positivePrecisionArithmetic : SourceTargets.positivePrecisionArithmetic := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro t ht x
    exact ⟨roundAt_nearest t ht x, abs_roundAt_sub_le t ht x⟩
  · intro t ht x hx
    rw [roundAt_eq_roundToEven t ht]
    exact roundToEven_policy_of_ne_zero t ht hx
  · exact fun _ => roundAt_oneBit_evidence
  · exact fun _ => oneBit_significand_eq_one
  · intros
    rfl
  · intro t ht x hx
    exact ⟨Real.sqrt_nonneg _, Real.sq_sqrt hx⟩
  · intros
    rfl
  · intro t ht operation
    change roundAt t (by omega) (ArithmeticOperationAt.ofStoredOperation operation).exactValue = _
    rw [roundAt_eq_roundToEven t ht, ScalarOperation.eval, Word.value_round]
    congr 1
    cases operation <;> rfl
  · intro t ht word k
    exact ⟨word.value_scale k, word.exponent_scale k⟩

theorem fairBitStreamMeasure_coordinate (j : ℕ) (b : Bool) :
    fairBitStreamMeasure {stream | stream j = b} = (1 / 2 : ℝ≥0∞) := by
  calc
    fairBitStreamMeasure {stream | stream j = b} =
        fairBitStreamMeasure.map (fun stream => stream j) {b} := by
          rw [Measure.map_apply (measurable_pi_apply j) (measurableSet_singleton b)]
          rfl
    _ = (PMF.uniformOfFintype Bool).toMeasure {b} := by
          rw [fairBitStreamMeasure, Measure.infinitePi_map_eval]
    _ = (1 / 2 : ℝ≥0∞) := by
          simp [PMF.uniformOfFintype_apply, one_div]

theorem fairBitStreamMeasure_independent :
    iIndepFun (fun j (stream : ℕ → Bool) => stream j) fairBitStreamMeasure := by
  unfold fairBitStreamMeasure
  exact iIndepFun_infinitePi (X := fun _ : ℕ => id) (fun _ => measurable_id)

private theorem executionResources : SourceTargets.executionResources := by
  refine ⟨?_, ?_, ?_, ?_, fairBitStreamMeasure_coordinate, fairBitStreamMeasure_independent⟩
  · intro n p hn hguard
    exact (Nat.le_add_left 7 (Nat.clog 2 n)).trans (clog_add_le_of_precisionGuard hn hguard)
  · intro n k p hn hguard
    have hp : 0 < p := by have := clog_add_le_of_precisionGuard hn hguard; omega
    have hq : 0 < workingPrecision n k p := by unfold workingPrecision; omega
    have hpq : p ≤ workingPrecision n k p := by unfold workingPrecision; omega
    have haux : 0 < svdAuxiliaryPrecision k p := by unfold svdAuxiliaryPrecision; omega
    obtain ⟨_, hacap, hpcap⟩ := svd_stage_precisions_le n k p
    exact ⟨⟨hn, hguard, hp, hp, le_rfl, le_rfl⟩,
      ⟨hn, hguard, hp, hq, hpq, le_rfl⟩, ⟨hn, hguard, hp, haux, hpcap, hacap⟩⟩
  · intro n p q cap prec stream run
    refine ⟨?_, ?_, fun _ => storage_le_iff, run.drawsFromStream⟩
    · intro step h
      obtain ⟨executed, _, rfl⟩ := List.mem_map.mp h
      cases executed with
      | arithmetic _ => exact ⟨prec.working_pos, prec.working_le_cap⟩
      | conversion _ _ hs ht hscap htcap _ => exact ⟨hs, hscap, ht, htcap⟩
      | comparison | index | fairBit | readExponent | scaleByPowerOfTwo => exact trivial
    · simp [work, ArithmeticExecution.trace]
  · intro cap step h
    cases step <;> simp_all [Step.Allowed, chargeAtLeastTwo, chargeAllowed] <;> omega

private theorem notationConventions : SourceTargets.notationConventions := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n 𝕜 _ x
    exact PiLp.norm_eq_of_L2 x
  · intro m n 𝕜 _ a
    refine ⟨Matrix.l2_opNorm_def a, ?_⟩
    rw [frobeniusNorm, Matrix.frobenius_norm_def, Real.sqrt_eq_rpow]
    simp only [← Real.rpow_natCast]
    norm_num
  · intro n 𝕜 _ i j
    exact Matrix.one_apply
  · intros
    rfl
  · intros
    rfl
  · intro n a i j
    change (2 * Complex.I : ℂ)⁻¹ * (a i j - star (a j i)) = _
    rw [div_eq_mul_inv, mul_comm]
  · intro x hx
    exact ⟨rfl, Real.exp_log hx⟩

theorem arithmeticWorkModelSuccessor : SourceTargets.arithmeticWorkModelSuccessor :=
  ⟨positivePrecisionArithmetic, executionResources, notationConventions⟩

end NumStability.CertifiedTridiagonalEigenpairs
