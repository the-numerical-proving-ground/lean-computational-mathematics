import ComputationalMathematics.Source.CertifiedTridiagonalEigenpairs.Retry.TrialWork

/-! Measurable work of setup, concrete trials, and processing the accepted result. -/

open MeasureTheory
open scoped ENNReal

namespace NumStability.CertifiedTridiagonalEigenpairs

open IndependentRetry

variable {n p : ℕ} {J : Finset ℕ}
  {a : Fin (n + 1) → TrialWord n J p} {b : Fin n → TrialWord n J p}

/-- The final meter runs only on the result returned by the actual retry loop. -/
noncomputable def retryPostWork (after : RetryResult n J p → ℕ) (bits : ℕ → GateBits n J) : ℝ≥0∞ :=
  ((retryRun a b bits).elim 0 after : ℕ)

private noncomputable def trialPostCharge (after : RetryResult n J p → ℕ)
    (j : ℕ) (words : GateBits n J) : ℝ≥0∞ := by
  classical
  exact if h : trialAccepts n p J a b words = true then
    (after ⟨j, ⟨trialRun n p J a b words, h⟩⟩ : ℝ≥0∞) else 0

private theorem retryPostWork_eq_tsum (after : RetryResult n J p → ℕ) (bits : ℕ → GateBits n J) :
    retryPostWork (a := a) (b := b) after bits =
      ∑' j : ℕ, (rejectionPrefix (trialRejected n p J a b) j).indicator
        (fun x => trialPostCharge (a := a) (b := b) after j (x j)) bits := by
  cases hrun : retryRun a b bits with
  | none =>
    have hreject := retryRun_eq_none_iff.mp hrun
    simp only [retryPostWork, hrun, Option.elim_none, Nat.cast_zero]
    symm
    apply ENNReal.tsum_eq_zero.mpr
    intro j
    rw [Set.indicator_of_mem (mem_rejectionPrefix.mpr fun i _ => hreject i), trialPostCharge]
    exact dif_neg (Bool.eq_false_iff.mp (hreject j))
  | some result =>
    obtain ⟨htrial, hreject⟩ := retryRun_first hrun
    have haccept := retryRun_accepts hrun
    rw [tsum_eq_single result.index]
    · rw [Set.indicator_of_mem (mem_rejectionPrefix.mpr hreject), trialPostCharge, dif_pos haccept]
      simp only [retryPostWork, hrun, Option.elim_some]
      congr 1
      cases result with
      | mk index trial =>
        dsimp only at htrial ⊢
        congr 1
        exact congrArg (RetryResult.mk index) (Subtype.ext htrial)
    · intro j hj
      rcases lt_or_gt_of_ne hj with hlt | hgt
      · rw [Set.indicator_of_mem (mem_rejectionPrefix.mpr fun i hi => hreject i (hi.trans hlt)),
          trialPostCharge, dif_neg (Bool.eq_false_iff.mp (hreject j hlt))]
      · apply Set.indicator_of_notMem
        intro hx
        exact Bool.eq_false_iff.mp (mem_rejectionPrefix.mp hx result.index hgt) haccept

theorem measurable_retryPostWork (after : RetryResult n J p → ℕ) :
    Measurable (retryPostWork (a := a) (b := b) after) := by
  change Measurable (fun bits => retryPostWork (a := a) (b := b) after bits)
  simp_rw [retryPostWork_eq_tsum]
  apply Measurable.ennreal_tsum
  intro j
  have hcharge : Measurable (trialPostCharge (a := a) (b := b) after j) := Measurable.of_discrete
  have hr : MeasurableSet (trialRejected n p J a b) := (trialRejected n p J a b).to_countable.measurableSet
  exact (hcharge.comp (measurable_pi_apply j)).indicator (measurableSet_rejectionPrefix hr j)

/-- The setup, every started trial, and the final work on the returned trial. -/
noncomputable def retryTotalWork (setup : ℕ) (after : RetryResult n J p → ℕ)
    (bits : ℕ → GateBits n J) : ℝ≥0∞ :=
  (setup : ℝ≥0∞) + retryTrialWork a b bits + retryPostWork (a := a) (b := b) after bits

theorem retryTotalWork_add_setup (extra setup : ℕ) (after : RetryResult n J p → ℕ)
    (bits : ℕ → GateBits n J) :
    (extra : ℝ≥0∞) + retryTotalWork (a := a) (b := b) setup after bits =
      retryTotalWork (a := a) (b := b) (extra + setup) after bits := by
  simp only [retryTotalWork, Nat.cast_add, add_assoc]

theorem measurable_retryTotalWork (setup : ℕ) (after : RetryResult n J p → ℕ) :
    Measurable (retryTotalWork (a := a) (b := b) setup after) :=
  (measurable_const.add (measurable_retryTrialWork a b)).add (measurable_retryPostWork after)

theorem retryTotalWork_eq_top_iff (setup : ℕ) (after : RetryResult n J p → ℕ)
    (bits : ℕ → GateBits n J) :
    retryTotalWork (a := a) (b := b) setup after bits = ⊤ ↔ retryRun a b bits = none := by
  simp [retryTotalWork, retryPostWork, retryTrialWork_eq_top_iff]

section Bounds

variable (hn : 2 ≤ n + 1) (hguard : precisionGuard (n + 1) p)
  (hJ : J.Nonempty) (hJbounds : J ⊆ Finset.Icc 1 (n + 1))
  (ha : ∀ i, |(a i).value| ≤ 1 / 4) (hb : ∀ i, |(b i).value| ≤ 1 / 4)

include hn hguard hJ hJbounds ha hb

theorem retryTotalWork_le {setup budget : ℕ} {after : RetryResult n J p → ℕ}
    (htrialScale : retryTrialWorkScale n J p ≤ budget) (hsetup : setup ≤ budget)
    (hafter : ∀ bits r, retryRun a b bits = some r → setup + after r ≤ budget)
    (bits : ℕ → GateBits n J) :
    retryTotalWork (a := a) (b := b) setup after bits ≤ (budget : ℝ≥0∞) *
      (retryCount (trialRejected n p J a b) bits + 1) := by
  have hwork := retryTrialWork_le (bits := bits) hn hguard hJ hJbounds ha hb
  have hsum : (setup : ℝ≥0∞) + retryPostWork (a := a) (b := b) after bits ≤ budget := by
    cases hr : retryRun a b bits with
    | none => simpa [retryPostWork, hr] using (Nat.cast_le.mpr hsetup : (setup : ℝ≥0∞) ≤ budget)
    | some r => simpa [retryPostWork, hr, ← Nat.cast_add] using
        (Nat.cast_le.mpr (hafter bits r hr) : ((setup + after r : ℕ) : ℝ≥0∞) ≤ budget)
  unfold retryTotalWork
  calc
    _ = retryTrialWork a b bits + ((setup : ℝ≥0∞) + retryPostWork (a := a) (b := b) after bits) := by
      rw [add_comm (setup : ℝ≥0∞) (retryTrialWork a b bits), add_assoc]
    _ ≤ (budget : ℝ≥0∞) * retryCount (trialRejected n p J a b) bits + budget := by
      apply add_le_add _ hsum
      exact hwork.trans (mul_le_mul_left (Nat.cast_le.mpr htrialScale) _)
    _ = _ := by rw [mul_add, mul_one]

theorem retryTotalWork_expectation_tail {setup budget : ℕ} {after : RetryResult n J p → ℕ}
    (htrialScale : retryTrialWorkScale n J p ≤ budget) (hsetup : setup ≤ budget)
    (hafter : ∀ bits r, retryRun a b bits = some r → setup + after r ≤ budget) :
    (∫⁻ bits, retryTotalWork (a := a) (b := b) setup after bits ∂retryBitMeasure n J) ≤
      3 * (budget : ℝ≥0∞) ∧
    ∀ m : ℕ, retryBitMeasure n J
      {bits | (budget : ℝ≥0∞) * ((m : ℝ≥0∞) + 1) < retryTotalWork (a := a) (b := b) setup after bits} ≤
        ENNReal.ofReal (rejectionBound (n + 1)) ^ m := by
  have hβ := finiteTrialUniformRejection n p J a b hn hguard hJ hJbounds ha hb
  have hr : MeasurableSet (trialRejected n p J a b) := (trialRejected n p J a b).to_countable.measurableSet
  have hw := retryTotalWork_le hn hguard hJ hJbounds ha hb htrialScale hsetup hafter
  refine ⟨?_, measure_work_tail_le _ hr hw hβ⟩
  have ⟨hmean, hlt⟩ := retryRun_attemptExpectation_le hβ
  have ht := hmean.trans hlt.le
  rw [lintegral_retryCount _ hr] at ht
  calc
    _ ≤ (budget : ℝ≥0∞) * ((1 - (trialBitLaw (n + 1) J.card).toMeasure (trialRejected n p J a b))⁻¹ + 1) :=
      lintegral_work_le _ hr hw
    _ ≤ (budget : ℝ≥0∞) * (2 + 1) := by gcongr
    _ = _ := by rw [mul_comm]; norm_num

end Bounds

end NumStability.CertifiedTridiagonalEigenpairs
