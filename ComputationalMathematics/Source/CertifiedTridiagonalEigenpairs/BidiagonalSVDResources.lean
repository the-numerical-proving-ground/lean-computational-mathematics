import ComputationalMathematics.Source.CertifiedTridiagonalEigenpairs.BidiagonalSVDPrecision
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Resource bounds for the dimension-`2n` reduction

These inequalities compare the work and storage factors in “Precision and
complete work” and transfer the confidence term to the original dimension.
-/

namespace NumStability.CertifiedTridiagonalEigenpairs

/-- The scalar refinement and the deterministic assembly factors fit the
`n k p` work scale. The refinement's dyadic tolerance has exponent
`Paux + 7`. -/
theorem svd_deterministic_work_factors_le {n k p : ℕ} (hk : 0 < k) (hkn : k ≤ n)
    (hguard : precisionGuard n p) :
    n * k * (svdAuxiliaryPrecision k p + 7) ≤ 5 * (n * k * p) ∧
      n + n * k ≤ 2 * (n * k * p) := by
  have hn := hk.trans_le hkn
  have hL := clog_add_le_of_precisionGuard hn hguard
  have hprec := svdAuxiliaryPrecision_le hn hkn hguard
  have hscalar : svdAuxiliaryPrecision k p + 7 ≤ 5 * p := by omega
  have hrows : n ≤ n * k := by simpa using Nat.mul_le_mul_left n (show 1 ≤ k by omega)
  have hwork : n * k ≤ n * k * p := by
    simpa using Nat.mul_le_mul_left (n * k) (show 1 ≤ p by omega)
  constructor
  · simpa [Nat.mul_left_comm, Nat.mul_comm, Nat.mul_assoc] using
      Nat.mul_le_mul_left (n * k) hscalar
  · omega

/-- The tridiagonal call's work and storage factors fit the original SVD scales. -/
theorem svd_tridiagonal_resource_factors_le {n k r p : ℕ} (hk : 0 < k) (hkn : k ≤ n)
    (hr : r ≤ 2 * k) (hguard : precisionGuard n p) :
    (2 * n) * r * svdAuxiliaryPrecision k p ≤ 16 * (n * k * p) ∧
      2 * n + (2 * n) * r ≤ 4 * (n + n * k) := by
  have hn := hk.trans_le hkn
  have hL := clog_add_le_of_precisionGuard hn hguard
  have hprec := svdAuxiliaryPrecision_le hn hkn hguard
  have haux : svdAuxiliaryPrecision k p ≤ 4 * p := by omega
  have hprod : (2 * n) * r ≤ 4 * (n * k) := by
    calc
      (2 * n) * r ≤ (2 * n) * (2 * k) := Nat.mul_le_mul_left _ hr
      _ = 4 * (n * k) := by ring
  constructor
  · calc
      (2 * n) * r * svdAuxiliaryPrecision k p ≤ (4 * (n * k)) * (4 * p) :=
        Nat.mul_le_mul hprod haux
      _ = 16 * (n * k * p) := by ring
  · omega

theorem svd_polynomial_failure_probability_le {n : ℕ} (hn : 0 < n) {c : ℝ} (hc : 0 < c) :
    (2 * (n : ℝ)) ^ (-c) ≤ (n : ℝ) ^ (-c) :=
  Real.rpow_le_rpow_of_nonpos (by exact_mod_cast hn) (by linarith [Nat.cast_nonneg (α := ℝ) n])
    (by linarith)

end NumStability.CertifiedTridiagonalEigenpairs
