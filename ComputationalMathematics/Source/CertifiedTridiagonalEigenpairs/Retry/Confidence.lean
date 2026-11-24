import ComputationalMathematics.Source.CertifiedTridiagonalEigenpairs.Retry.ConfidenceTarget

/-!
# Retry thresholds for the tridiagonal eigensolver

The two thresholds in the work-confidence corollary use the same algorithm and
one-trial rejection bound. A tail estimate for runtime therefore suffices for
both confidence statements.
-/

open MeasureTheory
open scoped ENNReal

namespace NumStability.CertifiedTridiagonalEigenpairs

lemma trialRejectionBound_pos {N : ℕ} (hN : 0 < N) : 0 < trialRejectionBound N := by
  unfold trialRejectionBound
  positivity

lemma trialRejectionBound_lt_half {N : ℕ} (hN : 0 < N) : trialRejectionBound N < 1 / 2 := by
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hsq : (1 : ℝ) ≤ (N : ℝ) ^ 2 := by nlinarith
  unfold trialRejectionBound
  rw [div_lt_iff₀ (by positivity)]
  linarith

theorem polynomialConfidenceTrials_pos {c : ℝ} (hc : 0 < c) :
    0 < polynomialConfidenceTrials c := by
  unfold polynomialConfidenceTrials
  exact Nat.ceil_pos.mpr (by positivity)

theorem trialRejectionBound_pow_polynomialConfidenceTrials_le {n N : ℕ} {c : ℝ}
    (hn : 0 < n) (hN : n ≤ N) :
    trialRejectionBound N ^ polynomialConfidenceTrials c ≤ (n : ℝ) ^ (-c) := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hN' : (n : ℝ) ≤ N := by exact_mod_cast hN
  have hnpos : (0 : ℝ) < n := by positivity
  have hNpos : (0 : ℝ) < N := hnpos.trans_le hN'
  have hbase : trialRejectionBound N ≤ ((n : ℝ) ^ 2)⁻¹ := by
    unfold trialRejectionBound
    rw [div_le_iff₀ (by positivity), ← div_eq_inv_mul, le_div_iff₀ (by positivity)]
    have hsq : (n : ℝ) ^ 2 ≤ (N : ℝ) ^ 2 := by gcongr
    nlinarith
  let m := polynomialConfidenceTrials c
  have hm : c ≤ 2 * (m : ℝ) := by
    have := Nat.le_ceil (c / 2)
    change c / 2 ≤ (m : ℝ) at this
    linarith
  calc
    trialRejectionBound N ^ m ≤ (((n : ℝ) ^ 2)⁻¹) ^ m := by
      gcongr
      exact (trialRejectionBound_pos (hn.trans_le hN)).le
    _ = (n : ℝ) ^ (-(2 * (m : ℝ))) := by
      rw [← inv_pow, ← pow_mul, Real.rpow_neg hnpos.le, ← Nat.cast_ofNat (R := ℝ),
        ← Nat.cast_mul, Real.rpow_natCast, inv_pow]
    _ ≤ (n : ℝ) ^ (-c) := Real.rpow_le_rpow_of_exponent_le hn' (neg_le_neg hm)

private lemma log_inv_trialRejectionBound_pos {N : ℕ} (hN : 0 < N) :
    0 < Real.log (2048 * (N : ℝ) ^ 2 / 3) := by
  have hpos := trialRejectionBound_pos hN
  have hlt := trialRejectionBound_lt_half hN
  rw [show 2048 * (N : ℝ) ^ 2 / 3 = (trialRejectionBound N)⁻¹ by simp [trialRejectionBound]]
  apply Real.log_pos
  exact (one_lt_inv₀ hpos).2 (by linarith)

theorem arbitraryConfidenceTrials_pos {N : ℕ} {ε : ℝ} (hN : 0 < N) (hε : 0 < ε)
    (hε1 : ε < 1) : 0 < arbitraryConfidenceTrials N ε := by
  have hnum : 0 < Real.log (1 / ε) := Real.log_pos ((one_lt_div hε).2 (by simpa using hε1))
  exact Nat.ceil_pos.mpr (div_pos hnum (log_inv_trialRejectionBound_pos hN))

theorem trialRejectionBound_pow_arbitraryConfidenceTrials_le {N : ℕ} {ε : ℝ}
    (hN : 0 < N) (hε : 0 < ε) :
    trialRejectionBound N ^ arbitraryConfidenceTrials N ε ≤ ε := by
  have hden := log_inv_trialRejectionBound_pos hN
  have hbase := trialRejectionBound_pos hN
  have hlog : Real.log (2048 * (N : ℝ) ^ 2 / 3) = -Real.log (trialRejectionBound N) := by
    rw [← Real.log_inv]
    simp [trialRejectionBound]
  have hm := (div_le_iff₀ hden).mp
    (Nat.le_ceil (Real.log (1 / ε) / Real.log (2048 * (N : ℝ) ^ 2 / 3)))
  change Real.log (1 / ε) ≤ (arbitraryConfidenceTrials N ε : ℝ) * _ at hm
  rw [one_div, Real.log_inv, hlog] at hm
  apply (Real.log_le_log_iff (pow_pos hbase _) hε).mp
  rw [Real.log_pow]
  linarith

section Work

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
  {work : Ω → ℝ≥0∞} (hw : Measurable work) (scale : ℝ≥0∞) {N : ℕ} (hN : 0 < N)
  (htail : ∀ m : ℕ, 0 < m → μ {x | scale * ((m : ℝ≥0∞) + 1) < work x} ≤
    ENNReal.ofReal (trialRejectionBound N) ^ m)

include hw htail

private theorem workConfidence_of_power_le {m : ℕ} (hm : 0 < m) {ε : ℝ}
    (hε : ENNReal.ofReal (trialRejectionBound N) ^ m ≤ ENNReal.ofReal ε) :
    1 - ENNReal.ofReal ε ≤ μ {x | work x ≤ scale * ((m : ℝ≥0∞) + 1)} := by
  have hset : MeasurableSet {x | scale * ((m : ℝ≥0∞) + 1) < work x} :=
    measurableSet_lt measurable_const hw
  have hcompl : {x | work x ≤ scale * ((m : ℝ≥0∞) + 1)} =
      {x | scale * ((m : ℝ≥0∞) + 1) < work x}ᶜ := by ext x; simp
  rw [hcompl, prob_compl_eq_one_sub hset]
  exact tsub_le_tsub_left ((htail m hm).trans hε) _

theorem work_polynomialConfidence {n : ℕ} (hn : 0 < n) (hnN : n ≤ N) {c : ℝ} (hc : 0 < c) :
    1 - ENNReal.ofReal ((n : ℝ) ^ (-c)) ≤
      μ {x | work x ≤ scale * ((polynomialConfidenceTrials c : ℝ≥0∞) + 1)} := by
  apply workConfidence_of_power_le μ hw scale htail (polynomialConfidenceTrials_pos hc)
  rw [← ENNReal.ofReal_pow (trialRejectionBound_pos (hn.trans_le hnN)).le]
  exact ENNReal.ofReal_le_ofReal (trialRejectionBound_pow_polynomialConfidenceTrials_le hn hnN)

include hN in
theorem work_arbitraryConfidence {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1) :
    1 - ENNReal.ofReal ε ≤
      μ {x | work x ≤ scale * ((arbitraryConfidenceTrials N ε : ℝ≥0∞) + 1)} := by
  apply workConfidence_of_power_le μ hw scale htail (arbitraryConfidenceTrials_pos hN hε hε1)
  rw [← ENNReal.ofReal_pow (trialRejectionBound_pos hN).le]
  exact ENNReal.ofReal_le_ofReal (trialRejectionBound_pow_arbitraryConfidenceTrials_le hN hε)

end Work

theorem tridiagonalWorkConfidenceTransfer : SourceTargets.tridiagonalWorkConfidenceTransfer := by
  intro Ω _ μ _ work hw n k p N C hn hnN scale htail
  exact ⟨fun _ hc => work_polynomialConfidence μ hw scale htail hn hnN hc,
    fun _ hε hε1 => work_arbitraryConfidence μ hw scale (hn.trans_le hnN) htail hε hε1⟩

end NumStability.CertifiedTridiagonalEigenpairs
