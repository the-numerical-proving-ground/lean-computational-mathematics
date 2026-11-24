import ComputationalMathematics.Source.CertifiedTridiagonalEigenpairs.Parameters
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Precision for selected bidiagonal singular triplets

The auxiliary precision, scale parameters, and per-stage bit bounds from
`svd:working-precision`, `svd:parameters`, and “Precision and complete work.”
-/

namespace NumStability.CertifiedTridiagonalEigenpairs

open FloatingPointFormat.UnboundedBinary (unitRoundoff)

/-- The SVD construction's working precision. -/
def svdWorkingPrecision (n k p : ℕ) : ℕ :=
  4 * p + 3 * Nat.clog 2 n + 3 * Nat.clog 2 k + 56

/-- The auxiliary precision for tridiagonal output and column normalization. -/
def svdAuxiliaryPrecision (k p : ℕ) : ℕ :=
  2 * p + Nat.clog 2 k + 10

/-- The binary scale of the number of requested singular triplets. -/
def svdKappa (k : ℕ) : ℕ := 2 ^ Nat.clog 2 k

/-- The mass shift used in the bidiagonal construction. -/
noncomputable def svdAlpha (k p : ℕ) : ℝ :=
  unitRoundoff p / svdKappa k

theorem le_svdKappa (k : ℕ) : k ≤ svdKappa k :=
  Nat.le_pow_clog (by decide) k

theorem svdAlpha_eq_unitRoundoff (k p : ℕ) :
    svdAlpha k p = unitRoundoff (p + Nat.clog 2 k) := by
  simp only [svdAlpha, svdKappa, unitRoundoff, zpow_neg, zpow_natCast, Nat.cast_pow,
    Nat.cast_ofNat, pow_add]
  field_simp

theorem svd_unitRoundoff_auxiliary_eq (k p : ℕ) :
    unitRoundoff (svdAuxiliaryPrecision k p) = unitRoundoff p ^ 2 / (1024 * svdKappa k) := by
  simp only [unitRoundoff, zpow_neg, zpow_natCast, svdAuxiliaryPrecision, svdKappa,
    Nat.cast_pow, Nat.cast_ofNat]
  rw [Nat.mul_comm 2 p, pow_add, pow_add, pow_mul]
  norm_num
  field_simp

/-- The scalar refinement tolerance is the roundoff at precision `Paux + 7`. -/
theorem svd_refinement_tolerance_eq (k p : ℕ) :
    unitRoundoff (svdAuxiliaryPrecision k p) / 128 =
      unitRoundoff (svdAuxiliaryPrecision k p + 7) := by
  simp only [unitRoundoff, zpow_neg, zpow_natCast, pow_add]
  norm_num
  field_simp

/-- The SVD input guard implies the guard for the dimension-`2n` call. -/
theorem svd_tridiagonal_precisionGuard {n k p : ℕ} (hguard : precisionGuard n p) :
    precisionGuard (2 * n) (svdAuxiliaryPrecision k p) := by
  have hε : unitRoundoff (svdAuxiliaryPrecision k p) ≤ unitRoundoff p / 2 := by
    simp only [unitRoundoff, zpow_neg, zpow_natCast]
    rw [show ((2 : ℝ) ^ p)⁻¹ / 2 = ((2 : ℝ) ^ (p + 1))⁻¹ by
      rw [pow_succ]
      field_simp]
    apply inv_anti₀ (by positivity)
    apply pow_le_pow_right₀ (by norm_num)
    unfold svdAuxiliaryPrecision
    omega
  calc
    ((2 * n : ℕ) : ℝ) * unitRoundoff (svdAuxiliaryPrecision k p)
        ≤ ((2 * n : ℕ) : ℝ) * (unitRoundoff p / 2) :=
      mul_le_mul_of_nonneg_left hε (Nat.cast_nonneg _)
    _ = (n : ℝ) * unitRoundoff p := by push_cast; ring
    _ ≤ 1 / 128 := hguard

private theorem clog_two_mul {n : ℕ} (hn : 0 < n) :
    Nat.clog 2 (2 * n) = Nat.clog 2 n + 1 := by
  have h := Nat.clog_of_two_le (by decide : 1 < 2) (show 2 ≤ 2 * n by omega)
  rwa [show (2 * n + 2 - 1) / 2 = n by omega] at h

/-- The tridiagonal call's working bits fit the SVD budget. -/
theorem svd_tridiagonal_workingPrecision_le {n k r p : ℕ} (hn : 0 < n) (hk : 0 < k)
    (hr : r ≤ 2 * k) :
    workingPrecision (2 * n) r (svdAuxiliaryPrecision k p) ≤ svdWorkingPrecision n k p := by
  have hlog := (Nat.clog_mono_right 2 hr).trans_eq (clog_two_mul hk)
  unfold workingPrecision svdAuxiliaryPrecision svdWorkingPrecision
  rw [clog_two_mul hn]
  omega

/-- Working bits for scalar refinement, column normalization, and output rounding. -/
theorem svd_stage_precisions_le (n k p : ℕ) :
    svdAuxiliaryPrecision k p + 15 ≤ svdWorkingPrecision n k p ∧
    svdAuxiliaryPrecision k p ≤ svdWorkingPrecision n k p ∧
    p ≤ svdWorkingPrecision n k p := by
  unfold svdAuxiliaryPrecision svdWorkingPrecision
  omega

theorem svdAuxiliaryPrecision_le {n k p : ℕ} (hn : 0 < n) (hkn : k ≤ n)
    (hguard : precisionGuard n p) : svdAuxiliaryPrecision k p ≤ 3 * p + 3 := by
  have hL := clog_add_le_of_precisionGuard hn hguard
  have hLk := Nat.clog_mono_right 2 hkn
  unfold svdAuxiliaryPrecision
  omega

theorem svdWorkingPrecision_le {n k p : ℕ} (hn : 2 ≤ n) (hkn : k ≤ n)
    (hguard : precisionGuard n p) : svdWorkingPrecision n k p ≤ 10 * p + 14 := by
  have hL := clog_add_le_of_precisionGuard (show 0 < n by omega) hguard
  have hLk := Nat.clog_mono_right 2 hkn
  unfold svdWorkingPrecision
  omega

end NumStability.CertifiedTridiagonalEigenpairs
