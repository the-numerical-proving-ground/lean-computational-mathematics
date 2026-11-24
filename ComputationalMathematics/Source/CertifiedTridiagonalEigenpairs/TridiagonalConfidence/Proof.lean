import ComputationalMathematics.Source.CertifiedTridiagonalEigenpairs.TridiagonalConfidence.Target
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-! The work thresholds of `main:high-probability` are the existing retry cutoffs. -/

open MeasureTheory
open scoped ENNReal

namespace NumStability.CertifiedTridiagonalEigenpairs

/-- The dyadic parameter in the algorithm is the manuscript's `2^⌈log₂ d⌉`. -/
theorem nextPowerOfTwo_eq_pow_ceil_logb (d : ℕ) (hd : 0 < d) :
    (nextPowerOfTwo d : ℝ) = (2 : ℝ) ^ ⌈Real.logb 2 (d : ℝ)⌉ := by
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hlog : 0 ≤ Real.logb 2 (d : ℝ) := Real.logb_nonneg (by norm_num) hd'
  have hceil : ⌈Real.logb 2 (d : ℝ)⌉₊ = Nat.clog 2 d := by
    simpa only [Nat.cast_ofNat] using Real.natCeil_logb_natCast 2 d
  rw [← Int.natCast_ceil_eq_ceil hlog, hceil, zpow_natCast, nextPowerOfTwo, Nat.cast_pow]
  norm_num

/-- For a nonnegative integer threshold the real cutoff agrees with the
extended nonnegative arithmetic used by the work meter. -/
theorem manuscriptWorkCutoff_nat (C d k p m : ℕ) :
    manuscriptWorkCutoff C d k p m = ((C * d * k * p : ℕ) : ℝ≥0∞) * ((m : ℝ≥0∞) + 1) := by
  unfold manuscriptWorkCutoff
  have h : (C : ℝ) * (((m : ℤ) : ℝ) + 1) * d * k * p =
      ((C * d * k * p * (m + 1) : ℕ) : ℝ) := by
    push_cast
    ring
  rw [h, ENNReal.ofReal_natCast, Nat.cast_mul, Nat.cast_add, Nat.cast_one]

theorem manuscriptWorkCutoff_polynomial (C d k p : ℕ) {c : ℝ} (hc : 0 < c) :
    manuscriptWorkCutoff C d k p ⌈c / 2⌉ =
      ((C * d * k * p : ℕ) : ℝ≥0∞) * ((polynomialConfidenceTrials c : ℝ≥0∞) + 1) := by
  rw [← Int.natCast_ceil_eq_ceil (show 0 ≤ c / 2 by positivity)]
  exact manuscriptWorkCutoff_nat C d k p (polynomialConfidenceTrials c)

theorem manuscriptWorkCutoff_arbitrary (C d k p : ℕ) {N : ℕ} {ε : ℝ}
    (hN : 0 < N) (hε : 0 < ε) (hε1 : ε < 1) :
    manuscriptWorkCutoff C d k p ⌈Real.log (1 / ε) / Real.log (2048 * (N : ℝ) ^ 2 / 3)⌉ =
      ((C * d * k * p : ℕ) : ℝ≥0∞) * ((arbitraryConfidenceTrials N ε : ℝ≥0∞) + 1) := by
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNsq : (1 : ℝ) ≤ (N : ℝ) ^ 2 := by nlinarith
  have hlogN : 0 ≤ Real.log (2048 * (N : ℝ) ^ 2 / 3) :=
    Real.log_nonneg ((le_div_iff₀ (by norm_num)).mpr (by linarith))
  have hlogε : 0 ≤ Real.log (1 / ε) :=
    Real.log_nonneg ((le_div_iff₀ hε).mpr (by simpa using hε1.le))
  rw [← Int.natCast_ceil_eq_ceil (div_nonneg hlogε hlogN)]
  exact manuscriptWorkCutoff_nat C d k p (arbitraryConfidenceTrials N ε)

theorem tridiagonalPrescribedConfidence : SourceTargets.tridiagonalPrescribedConfidence := by
  refine ⟨4000, by decide, ?_⟩
  intro n p hp J a b hguard hJ hJvalid d k N μ W
  have hN : 0 < N := (Nat.succ_pos n).trans_le (le_nextPowerOfTwo (n + 1))
  have htail := (tridiagonalEigenpairWork_expectation_tail a b hguard hJ hJvalid).2
  obtain ⟨hpoly, harb⟩ := tridiagonalEigenpairWork_confidence a b hguard hJ hJvalid
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro m _
    simp only [manuscriptWorkCutoff_nat]
    exact htail m
  · intro c hc
    rw [manuscriptWorkCutoff_polynomial _ _ _ _ hc]
    simpa only [d, Nat.cast_succ] using hpoly c hc
  · intro ε hε hε1
    rw [manuscriptWorkCutoff_arbitrary _ _ _ _ hN hε hε1]
    exact harb ε hε hε1
  · intro bits out hout
    exact runTridiagonalEigenpairs_accuracy a b bits hguard hJ hJvalid out hout

end NumStability.CertifiedTridiagonalEigenpairs
