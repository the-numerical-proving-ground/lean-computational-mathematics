import ComputationalMathematics.Source.CertifiedTridiagonalEigenpairs.Scaling
import Mathlib.Analysis.CStarAlgebra.Matrix

/-!
# Transfer from stored scaling to the original units

The norm and inverse scaling identities supply the scale premises of the
returned-error bounds. A final label is rounded once and then rescaled by
an exact exponent shift at the same precision.
-/

namespace NumStability.CertifiedTridiagonalEigenpairs

open FloatingPointFormat.UnboundedBinary
open scoped Matrix.Norms.L2Operator

variable {p n : ℕ} {hp : 2 ≤ p}

/-- The original matrix is exactly the normalized matrix scaled by `R`. -/
theorem storedTridiagonal_eq_normalization_smul
    (a : Fin (n + 1) → Word p hp) (b : Fin n → Word p hp) (r : ℤ) :
    storedTridiagonal a b = (2 : ℝ) ^ r • normalizedTridiagonal a b r := by
  rw [normalizedTridiagonal_eq, smul_smul, mul_inv_cancel₀ (by positivity), one_smul]

/-- The normalization facts in the operator-norm notation used by the final
error bounds. -/
theorem normalization_for_returned_errors
    (a : Fin (n + 1) → Word p hp) (b : Fin n → Word p hp)
    {r : ℤ} (hr : normalizationExponent a b = some r) :
    let R := (2 : ℝ) ^ r
    let T := storedTridiagonal a b
    let S := normalizedTridiagonal a b r
    0 < R ∧ T = R • S ∧ R < 8 * ‖T‖ ∧ ‖S‖ ≤ 3 / 4 := by
  obtain ⟨_, hop, hrow, hstrict⟩ := normalizedTridiagonal_bounds a b hr
  exact ⟨by positivity, storedTridiagonal_eq_normalization_smul a b r,
    hstrict, hop.trans hrow⟩

/-- The native output label, with one nearest-even rounding before scaling. -/
noncomputable def rescaledLabel (p : ℕ) (hp : 2 ≤ p) (r : ℤ) (theta : ℝ) : Word p hp :=
  (Word.round p hp theta).scale r

theorem rescaledLabel_value (p : ℕ) (hp : 2 ≤ p) (r : ℤ) (theta : ℝ) :
    (rescaledLabel p hp r theta).value = (2 : ℝ) ^ r * roundToEven p hp theta := by
  rw [rescaledLabel, Word.value_scale, Word.value_round]

end NumStability.CertifiedTridiagonalEigenpairs
