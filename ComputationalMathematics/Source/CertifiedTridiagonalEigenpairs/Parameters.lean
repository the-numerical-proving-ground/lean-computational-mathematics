import ComputationalMathematics.Analysis.FloatingPointArithmetic.UnboundedBinary.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Log

/-!
# Parameters for selected tridiagonal eigenpairs

This file formalizes the precision and scales in the paper *Stable selected
singular triplets of bidiagonal matrices*, equations `main:precision` and
`alg:parameters`. The precision checks are from `rand:rounding-budget` and
`proof:vector-precision`.
-/

namespace NumStability.CertifiedTridiagonalEigenpairs

open FloatingPointFormat.UnboundedBinary (unitRoundoff)

noncomputable section

/-- Input guard `main:guard`. -/
def precisionGuard (n p : ℕ) : Prop :=
  (n : ℝ) * unitRoundoff p ≤ 1 / 128

/-- The integer power `N = 2^L`, where `L = Nat.clog 2 n`. Using
`k` as the argument gives the paper's `N_k`. -/
def nextPowerOfTwo (n : ℕ) : ℕ :=
  2 ^ Nat.clog 2 n

/-- Power of two `N₁⁄₄` with exponent the ceiling of `L / 4`. -/
def quarterPowerOfTwo (n : ℕ) : ℕ :=
  2 ^ ((Nat.clog 2 n + 3) / 4)

/-- The working significand precision `q` from `main:precision`. -/
def workingPrecision (n k p : ℕ) : ℕ :=
  2 * p + 3 * Nat.clog 2 n + Nat.clog 2 k + 32

/-- The trial bit count per coordinate, `b_rng`. -/
def rngBits (n k : ℕ) : ℕ :=
  3 * Nat.clog 2 n + Nat.clog 2 k + 16

/-- The trial rejection-probability bound `β`. -/
def rejectionBound (n : ℕ) : ℝ :=
  3 / (2048 * (nextPowerOfTwo n : ℝ) ^ 2)

/-- The diagonal perturbation scale `δ`. -/
def perturbationScale (p : ℕ) : ℝ :=
  unitRoundoff p / 256

/-- The gap scale `g`. -/
def gapScale (n k p : ℕ) : ℝ :=
  perturbationScale p / (1024 * (nextPowerOfTwo n : ℝ) ^ 3 * nextPowerOfTwo k)

/-- The certified gap threshold `Δ`. -/
def certifiedGap (n k p : ℕ) : ℝ :=
  gapScale n k p / 2

/-- The preliminary label error bound `α`. -/
def gapLabelError (n k p : ℕ) : ℝ :=
  gapScale n k p / 64

/-- The preliminary refinement tolerance `ε_gap`. -/
def gapTolerance (n k p : ℕ) : ℝ :=
  gapScale n k p / 128

/-- The vector extraction tolerance `η`. -/
def vectorTolerance (n k p : ℕ) : ℝ :=
  certifiedGap n k p * unitRoundoff ((p + 1) / 2) / (16 * quarterPowerOfTwo n)

/-- The preliminary refinement exponent `r` such that
`ε_gap = 2⁻ʳ`. -/
def gapToleranceExponent (n k p : ℕ) : ℕ :=
  p + 3 * Nat.clog 2 n + Nat.clog 2 k + 25

/-- The vector extraction exponent `h` such that `η = 2⁻ʰ`. -/
def vectorToleranceExponent (n k p : ℕ) : ℕ :=
  p + (p + 1) / 2 + 3 * Nat.clog 2 n + Nat.clog 2 k + (Nat.clog 2 n + 3) / 4 + 23

/-- The working roundoff `ω`. -/
def workingRoundoff (n k p : ℕ) : ℝ :=
  unitRoundoff (workingPrecision n k p)

private theorem roundoff_eq_inv (p : ℕ) :
    unitRoundoff p = ((2 : ℝ) ^ p)⁻¹ := by
  simp [unitRoundoff, zpow_neg]

private theorem roundoff_add (p t : ℕ) :
    unitRoundoff (p + t) = unitRoundoff p * unitRoundoff t := by
  rw [roundoff_eq_inv, pow_add, mul_inv, ← roundoff_eq_inv, ← roundoff_eq_inv]

private theorem roundoff_antitone : Antitone unitRoundoff := by
  intro a b hab
  simp only [roundoff_eq_inv]
  exact inv_anti₀ (by positivity) (pow_le_pow_right₀ (by norm_num) hab)

theorem le_nextPowerOfTwo (n : ℕ) : n ≤ nextPowerOfTwo n :=
  Nat.le_pow_clog (by decide) n

/-- The guard gives `L + 7 ≤ p` for each positive matrix dimension. -/
theorem clog_add_le_of_precisionGuard {n p : ℕ} (hn : 0 < n)
    (guard : precisionGuard n p) : Nat.clog 2 n + 7 ≤ p := by
  simp only [precisionGuard, roundoff_eq_inv, ← div_eq_mul_inv] at guard
  have hpow : 0 < (2 : ℝ) ^ p := by positivity
  have hnp : (n : ℝ) * 128 ≤ (2 : ℝ) ^ p := by
    linarith [(div_le_iff₀ hpow).mp guard]
  have hp : 7 ≤ p := by
    by_contra! hp
    have hp' := pow_lt_pow_right₀ (a := (2 : ℝ)) (by norm_num) hp
    have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
    norm_num at hp'
    linarith
  have hbound : (n : ℝ) ≤ (2 : ℝ) ^ (p - 7) := by
    have hsplit : (2 : ℝ) ^ p = (2 : ℝ) ^ (p - 7) * 128 := by
      have hseven : (2 : ℝ) ^ 7 = 128 := by norm_num
      rw [← hseven]
      rw [← pow_add (2 : ℝ) (p - 7) 7, Nat.sub_add_cancel hp]
    linarith
  have hclog : Nat.clog 2 n ≤ p - 7 :=
    Nat.clog_le_of_le_pow (by exact_mod_cast hbound)
  omega

theorem clog_le_sub_of_precisionGuard {n p : ℕ} (hn : 0 < n)
    (guard : precisionGuard n p) : Nat.clog 2 n ≤ p - 7 := by
  have := clog_add_le_of_precisionGuard hn guard
  omega

/-- The two working-precision bounds in `main:precision`. -/
theorem workingPrecision_bounds {n k p : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n)
    (guard : precisionGuard n p) :
    workingPrecision n k p ≤ 2 * p + 4 * Nat.clog 2 n + 32 ∧
    2 * p + 4 * Nat.clog 2 n + 32 ≤ 6 * p + 4 := by
  have hlog := Nat.clog_mono_right 2 hkn
  have hp := clog_add_le_of_precisionGuard (lt_of_lt_of_le (by decide : 0 < 1) (hk.trans hkn)) guard
  unfold workingPrecision
  omega

theorem rngBits_add_one_lt_workingPrecision (n k p : ℕ) :
    rngBits n k + 1 < workingPrecision n k p := by
  unfold rngBits workingPrecision
  omega

theorem rngBits_le {n k : ℕ} (hkn : k ≤ n) :
    rngBits n k ≤ 4 * Nat.clog 2 n + 16 := by
  have := Nat.clog_mono_right 2 hkn
  unfold rngBits
  omega

/-- For a draw from the prescribed finite range, the grid size, doubled draw
plus one, and signed cell-center numerator all fit in `b_rng + 1` bits. -/
theorem samplerIntegers_lt_two_pow {n k r : ℕ} (hr : r < 2 ^ rngBits n k) :
    2 ^ rngBits n k < 2 ^ (rngBits n k + 1) ∧
    2 * r + 1 < 2 ^ (rngBits n k + 1) ∧
    (2 * (r : ℤ) + 1 - 2 ^ rngBits n k).natAbs < 2 ^ (rngBits n k + 1) := by
  let b := rngBits n k
  have hpos : 0 < (2 : ℕ) ^ b := by positivity
  have hbound : 2 ^ (b + 1) = (2 : ℕ) ^ b * 2 := by rw [pow_succ]
  have hcast : ((2 ^ b : ℕ) : ℤ) = (2 : ℤ) ^ b := by push_cast; rfl
  change r < 2 ^ b at hr
  change 2 ^ b < 2 ^ (b + 1) ∧ 2 * r + 1 < 2 ^ (b + 1) ∧
    (2 * (r : ℤ) + 1 - 2 ^ b).natAbs < 2 ^ (b + 1)
  rw [hbound, ← hcast]
  omega

theorem perturbationScale_eq_roundoff (p : ℕ) :
    perturbationScale p = unitRoundoff (p + 8) := by
  rw [perturbationScale, roundoff_add, roundoff_eq_inv 8]
  norm_num [div_eq_mul_inv]

theorem gapScale_eq_roundoff (n k p : ℕ) :
    gapScale n k p = unitRoundoff (p + 3 * Nat.clog 2 n + Nat.clog 2 k + 18) := by
  rw [gapScale, perturbationScale_eq_roundoff]
  rw [mul_comm 3 (Nat.clog 2 n)]
  simp only [nextPowerOfTwo, Nat.cast_pow, Nat.cast_ofNat, roundoff_eq_inv, pow_add,
    pow_mul]
  norm_num
  field_simp
  ring

/-- The two displayed formulas for the gap scale in `alg:parameters`. -/
theorem gapScale_eq_scaled (n k p : ℕ) :
    gapScale n k p =
      unitRoundoff p * unitRoundoff 18 * ((nextPowerOfTwo n : ℝ) ^ 3)⁻¹ *
        (nextPowerOfTwo k : ℝ)⁻¹ := by
  unfold gapScale perturbationScale
  rw [roundoff_eq_inv 18]
  norm_num
  field_simp [nextPowerOfTwo]
  ring

theorem certifiedGap_eq_scaled (n k p : ℕ) :
    certifiedGap n k p =
      unitRoundoff p / (2 ^ 19 * (nextPowerOfTwo n : ℝ) ^ 3 * nextPowerOfTwo k) := by
  unfold certifiedGap gapScale perturbationScale
  norm_num
  field_simp [nextPowerOfTwo]
  ring

theorem certifiedGap_eq_roundoff (n k p : ℕ) :
    certifiedGap n k p = unitRoundoff (p + 3 * Nat.clog 2 n + Nat.clog 2 k + 19) := by
  rw [certifiedGap, gapScale_eq_roundoff,
    show p + 3 * Nat.clog 2 n + Nat.clog 2 k + 19 =
      (p + 3 * Nat.clog 2 n + Nat.clog 2 k + 18) + 1 by omega,
    roundoff_add (p + 3 * Nat.clog 2 n + Nat.clog 2 k + 18) 1, roundoff_eq_inv 1]
  norm_num [div_eq_mul_inv]

theorem gapLabelError_eq_roundoff (n k p : ℕ) :
    gapLabelError n k p = unitRoundoff (p + 3 * Nat.clog 2 n + Nat.clog 2 k + 24) := by
  rw [gapLabelError, gapScale_eq_roundoff,
    show p + 3 * Nat.clog 2 n + Nat.clog 2 k + 24 =
      (p + 3 * Nat.clog 2 n + Nat.clog 2 k + 18) + 6 by omega,
    roundoff_add (p + 3 * Nat.clog 2 n + Nat.clog 2 k + 18) 6, roundoff_eq_inv 6]
  norm_num [div_eq_mul_inv]

theorem gapTolerance_eq_roundoff (n k p : ℕ) :
    gapTolerance n k p = unitRoundoff (gapToleranceExponent n k p) := by
  rw [gapTolerance, gapToleranceExponent, gapScale_eq_roundoff,
    show p + 3 * Nat.clog 2 n + Nat.clog 2 k + 25 =
      (p + 3 * Nat.clog 2 n + Nat.clog 2 k + 18) + 7 by omega,
    roundoff_add (p + 3 * Nat.clog 2 n + Nat.clog 2 k + 18) 7, roundoff_eq_inv 7]
  norm_num [div_eq_mul_inv]

theorem vectorTolerance_eq_roundoff (n k p : ℕ) :
    vectorTolerance n k p = unitRoundoff (vectorToleranceExponent n k p) := by
  rw [vectorTolerance, certifiedGap_eq_roundoff, vectorToleranceExponent,
    show p + (p + 1) / 2 + 3 * Nat.clog 2 n + Nat.clog 2 k + (Nat.clog 2 n + 3) / 4 + 23 =
      (p + 3 * Nat.clog 2 n + Nat.clog 2 k + 19) + (p + 1) / 2 +
      (Nat.clog 2 n + 3) / 4 + 4 by omega]
  simp only [quarterPowerOfTwo, Nat.cast_pow, Nat.cast_ofNat, roundoff_eq_inv, pow_add]
  norm_num
  field_simp

theorem gapToleranceExponent_add_eight_le {n k p : ℕ} (hp : 1 ≤ p) :
    gapToleranceExponent n k p + 8 ≤ workingPrecision n k p := by
  unfold gapToleranceExponent workingPrecision
  omega

theorem gapTolerance_twice (n k p : ℕ) :
    2 * gapTolerance n k p = gapLabelError n k p := by
  unfold gapTolerance gapLabelError
  ring

theorem perturbationScale_div_rng (n k p : ℕ) :
    perturbationScale p / (2 : ℝ) ^ rngBits n k = gapLabelError n k p := by
  rw [perturbationScale_eq_roundoff, gapLabelError_eq_roundoff,
    div_eq_mul_inv, ← roundoff_eq_inv, ← roundoff_add, rngBits]
  congr 1
  omega

theorem workingRoundoff_eq (n k p : ℕ) :
    workingRoundoff n k p = unitRoundoff p * certifiedGap n k p / 8192 := by
  rw [workingRoundoff, workingPrecision, certifiedGap_eq_roundoff,
    show 2 * p + 3 * Nat.clog 2 n + Nat.clog 2 k + 32 =
      p + (p + 3 * Nat.clog 2 n + Nat.clog 2 k + 19) + 13 by omega,
    roundoff_add, roundoff_add, roundoff_eq_inv 13]
  norm_num [div_eq_mul_inv]

/-- Rounding and storage error allowances used in the proof of `rand:trial`. -/
theorem trialPrecisionBudget {n k p : ℕ} (hn : 2 ≤ n) (guard : precisionGuard n p) :
    2 * workingRoundoff n k p ≤ gapLabelError n k p ∧
    workingRoundoff n k p ≤ 1 / 128 ∧
    2 * workingRoundoff n k p ≤ perturbationScale p ∧
    perturbationScale p + 2 * workingRoundoff n k p ≤ unitRoundoff p / 128 ∧
    gapToleranceExponent n k p + 8 ≤ workingPrecision n k p := by
  have hp := clog_add_le_of_precisionGuard (by omega : 0 < n) guard
  have hsmall {t : ℕ} (ht : t + 1 ≤ workingPrecision n k p) :
      2 * workingRoundoff n k p ≤ unitRoundoff t := by
    have h := roundoff_antitone ht
    rw [roundoff_add, roundoff_eq_inv 1] at h
    norm_num at h
    unfold workingRoundoff
    linarith
  have hgap : 2 * workingRoundoff n k p ≤ gapLabelError n k p := by
    rw [gapLabelError_eq_roundoff]
    apply hsmall
    unfold workingPrecision
    omega
  have hpert : 2 * workingRoundoff n k p ≤ perturbationScale p := by
    rw [perturbationScale_eq_roundoff]
    apply hsmall
    unfold workingPrecision
    omega
  refine ⟨hgap, ?_, hpert, ?_, gapToleranceExponent_add_eight_le (by omega)⟩
  · have hw := roundoff_antitone (show 7 ≤ workingPrecision n k p by
      unfold workingPrecision
      omega)
    norm_num [roundoff_eq_inv 7] at hw
    exact hw
  · unfold perturbationScale at *
    linarith

/-- The final eigenvalue refinement has at least twelve bits beyond the
exponent of `η`, as used before `proof:vector-precision`. -/
theorem vectorTolerance_precision_margin {n k p : ℕ} (hn : 2 ≤ n)
    (guard : precisionGuard n p) :
    workingPrecision n k p - vectorToleranceExponent n k p =
      p / 2 - (Nat.clog 2 n + 3) / 4 + 9 ∧
    12 ≤ workingPrecision n k p - vectorToleranceExponent n k p := by
  have hlog : 0 < Nat.clog 2 n := Nat.clog_pos (by decide) (by omega)
  have hp := clog_add_le_of_precisionGuard (by omega : 0 < n) guard
  unfold workingPrecision vectorToleranceExponent
  omega

theorem vectorTolerance_half_eq_roundoff (n k p : ℕ) :
    vectorTolerance n k p / 2 = unitRoundoff (vectorToleranceExponent n k p + 1) := by
  rw [vectorTolerance_eq_roundoff, roundoff_add, roundoff_eq_inv 1]
  norm_num [div_eq_mul_inv]

theorem vectorToleranceExponent_add_nine_le {n k p : ℕ} (hn : 2 ≤ n)
    (guard : precisionGuard n p) :
    vectorToleranceExponent n k p + 9 ≤ workingPrecision n k p := by
  have := (vectorTolerance_precision_margin (k := k) hn guard).2
  omega

theorem rpow_quarter_le_quarterPowerOfTwo (n : ℕ) :
    (n : ℝ) ^ (1 / 4 : ℝ) ≤ (quarterPowerOfTwo n : ℝ) := by
  have hlog : Nat.clog 2 n ≤ ((Nat.clog 2 n + 3) / 4) * 4 := by omega
  have hn : n ≤ quarterPowerOfTwo n ^ 4 := by
    unfold quarterPowerOfTwo
    rw [← pow_mul]
    exact (le_nextPowerOfTwo n).trans (Nat.pow_le_pow_right (by decide) hlog)
  have hr : (n : ℝ) ≤ (quarterPowerOfTwo n : ℝ) ^ 4 := by exact_mod_cast hn
  have hx : 0 ≤ (quarterPowerOfTwo n : ℝ) := by positivity
  calc
    (n : ℝ) ^ (1 / 4 : ℝ) ≤ ((quarterPowerOfTwo n : ℝ) ^ 4) ^ (1 / 4 : ℝ) :=
      Real.rpow_le_rpow (by positivity) hr (by norm_num)
    _ = (quarterPowerOfTwo n : ℝ) := by
      rw [← Real.rpow_natCast_mul hx, show (4 : ℕ) * (1 / 4 : ℝ) = 1 by norm_num,
        Real.rpow_one]

/-- The vector extraction tolerance is at most the real fourth-root scale
in the precision check for the tridiagonal algorithm. -/
theorem vectorTolerance_le_root_scale {n : ℕ} (hn : 0 < n) (k p : ℕ) :
    vectorTolerance n k p ≤
      certifiedGap n k p * Real.sqrt (unitRoundoff p) / (16 * (n : ℝ) ^ (1 / 4 : ℝ)) := by
  have hhalf : unitRoundoff ((p + 1) / 2) ≤ Real.sqrt (unitRoundoff p) := by
    apply Real.le_sqrt_of_sq_le
    rw [sq, ← roundoff_add]
    exact roundoff_antitone (by omega)
  have hden : 0 < 16 * (n : ℝ) ^ (1 / 4 : ℝ) := by positivity
  have hgap : 0 < certifiedGap n k p := by
    rw [certifiedGap_eq_roundoff]
    exact FloatingPointFormat.UnboundedBinary.unitRoundoff_pos _
  have hpow := rpow_quarter_le_quarterPowerOfTwo n
  unfold vectorTolerance
  apply div_le_div₀
  · exact (mul_nonneg hgap.le (Real.sqrt_nonneg _))
  · exact mul_le_mul_of_nonneg_left hhalf hgap.le
  · exact hden
  · linarith

theorem vectorTolerance_lt_half (n k p : ℕ) :
    vectorTolerance n k p < 1 / 2 := by
  rw [vectorTolerance_eq_roundoff]
  have h := roundoff_antitone (show 2 ≤ vectorToleranceExponent n k p by
    unfold vectorToleranceExponent
    omega)
  norm_num [roundoff_eq_inv 2] at h
  linarith

theorem dimension_mul_certifiedGap_lt {n k p : ℕ} (guard : precisionGuard n p) :
    (n : ℝ) * certifiedGap n k p < 1 / 8 := by
  have hroundoff := roundoff_antitone
    (show p ≤ p + 3 * Nat.clog 2 n + Nat.clog 2 k + 19 by omega)
  rw [certifiedGap_eq_roundoff]
  have := mul_le_mul_of_nonneg_left hroundoff (by positivity : 0 ≤ (n : ℝ))
  unfold precisionGuard at guard
  linarith

/-- The three working-roundoff requirements in `proof:vector-precision`. -/
theorem acceptedPrecisionBudget {n k p : ℕ} (hn : 2 ≤ n) (guard : precisionGuard n p) :
    workingRoundoff n k p ≤ vectorTolerance n k p / 4096 ∧
    workingRoundoff n k p = unitRoundoff p * certifiedGap n k p / 8192 ∧
    (n : ℝ) * workingRoundoff n k p ≤ unitRoundoff p / 65536 := by
  refine ⟨?_, workingRoundoff_eq n k p, ?_⟩
  · have hmargin := (vectorTolerance_precision_margin (k := k) hn guard).2
    have hroundoff := roundoff_antitone
      (show vectorToleranceExponent n k p + 12 ≤ workingPrecision n k p by omega)
    rw [roundoff_add, roundoff_eq_inv 12] at hroundoff
    norm_num at hroundoff
    simpa [workingRoundoff, vectorTolerance_eq_roundoff, div_eq_mul_inv] using hroundoff
  · have hgap := dimension_mul_certifiedGap_lt (k := k) guard
    have hu := FloatingPointFormat.UnboundedBinary.unitRoundoff_pos p
    have hprod := mul_le_mul_of_nonneg_right hgap.le hu.le
    rw [workingRoundoff_eq]
    calc
      (n : ℝ) * (unitRoundoff p * certifiedGap n k p / 8192) =
          ((n : ℝ) * certifiedGap n k p) * unitRoundoff p / 8192 := by ring
      _ ≤ (1 / 8) * unitRoundoff p / 8192 := by gcongr
      _ = unitRoundoff p / 65536 := by ring

end

end NumStability.CertifiedTridiagonalEigenpairs
