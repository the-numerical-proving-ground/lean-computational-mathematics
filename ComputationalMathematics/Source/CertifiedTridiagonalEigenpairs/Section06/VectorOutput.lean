import ComputationalMathematics.Analysis.FloatingPointArithmetic.UnboundedBinary.VectorNormalization

/-! # Final rounding of a Section 6 eigenvector -/

namespace NumStability.CertifiedTridiagonalEigenpairs

open FloatingPointFormat.UnboundedBinary

variable {n p q : ℕ} {hq : 2 ≤ q}

theorem roundedImaginaryVector_ne_zero (x : Fin n → Word q hq)
    {y : EuclideanSpace ℝ (Fin n)} (hy : y ≠ 0)
    (hp : 2 ≤ p)
    (hpath : ‖Word.euclidean x - y‖ ≤ (3 * unitRoundoff p / 1024) * ‖y‖) :
    Word.euclidean x ≠ 0 := by
  have hcoef : 3 * unitRoundoff p / 1024 < 1 := by
    linarith [unitRoundoff_le_quarter p hp]
  have hy' := norm_pos_iff.mpr hy
  intro hx
  rw [hx, zero_sub, norm_neg] at hpath
  have h := mul_lt_mul_of_pos_right hcoef hy'
  linarith

/-- Normalize the computed imaginary vector and return a word at precision
`p` for each coordinate. The relative path estimate guarantees a positive
computed denominator. -/
noncomputable def roundedRealVector (p : ℕ) (hp : 2 ≤ p) (x : Fin n → Word q hq)
    {y : EuclideanSpace ℝ (Fin n)} (hy : y ≠ 0)
    (hpath : ‖Word.euclidean x - y‖ ≤ (3 * unitRoundoff p / 1024) * ‖y‖) :
    Fin n → Word p hp :=
  Word.normalizeTo p hp x (roundedImaginaryVector_ne_zero x hy hp hpath)

/-- The source's rounding bound relative to the exact normalized imaginary
vector, before invoking the spectral direction estimate. -/
theorem roundedRealVector_error (hp : 2 ≤ p) (x : Fin n → Word q hq)
    {y : EuclideanSpace ℝ (Fin n)} (hy : y ≠ 0)
    (hn : 2 ≤ n) (hguard : (n : ℝ) * unitRoundoff p ≤ 1 / 128)
    (hprecision : (n : ℝ) * unitRoundoff q ≤ unitRoundoff p / 65536)
    (hpath : ‖Word.euclidean x - y‖ ≤ (3 * unitRoundoff p / 1024) * ‖y‖) :
    let error := 6 * unitRoundoff p / 1024 + 4 * n * unitRoundoff q +
      unitRoundoff p * (1 + 4 * n * unitRoundoff q)
    ‖Word.euclidean (roundedRealVector p hp x hy hpath) - ‖y‖⁻¹ • y‖ ≤ error ∧
      error < 2 * unitRoundoff p := by
  have hn1 : 1 ≤ n := le_trans (by decide) hn
  have hny : 0 < ‖y‖ := norm_pos_iff.mpr hy
  have hu : 0 < unitRoundoff p := unitRoundoff_pos p
  have hup : unitRoundoff p ≤ 1 / 128 :=
    (le_mul_of_one_le_left hu.le (by exact_mod_cast hn1)).trans hguard
  have hb : (n : ℝ) * unitRoundoff q ≤ 1 / 128 := by
    linarith
  have hnorm := Word.normalizeTo_error p hp x (roundedImaginaryVector_ne_zero x hy hp hpath)
    hy hn1 hb
  have hrelative : 2 * ‖Word.euclidean x - y‖ / ‖y‖ ≤ 6 * unitRoundoff p / 1024 := by
    rw [div_le_iff₀ hny]
    linarith
  have haux : 4 * n * unitRoundoff q ≤ unitRoundoff p / 16384 := by linarith
  have hcross : unitRoundoff p * (4 * n * unitRoundoff q) ≤ unitRoundoff p / 65536 := by
    have hbudget : 4 * n * unitRoundoff q ≤ 1 / 65536 := by linarith
    linarith [mul_le_mul_of_nonneg_left hbudget hu.le]
  dsimp only
  exact ⟨by unfold roundedRealVector; linarith, by linarith⟩

/-- Assemble the stored vector error with the exact spectral direction from
the same Section 6 computation. -/
theorem roundedRealVector_direction (hp : 2 ≤ p) (x : Fin n → Word q hq)
    {y v : EuclideanSpace ℝ (Fin n)} (hy : y ≠ 0)
    (hn : 2 ≤ n) (hguard : (n : ℝ) * unitRoundoff p ≤ 1 / 128)
    (hprecision : (n : ℝ) * unitRoundoff q ≤ unitRoundoff p / 65536)
    (hpath : ‖Word.euclidean x - y‖ ≤ (3 * unitRoundoff p / 1024) * ‖y‖)
    (hdirection : ∃ sign : ℝ, (sign = -1 ∨ sign = 1) ∧
      ‖‖y‖⁻¹ • y - sign • v‖ < unitRoundoff p / 4) :
    ∃ sign : ℝ, (sign = -1 ∨ sign = 1) ∧
      ‖Word.euclidean (roundedRealVector p hp x hy hpath) - sign • v‖ <
        9 * unitRoundoff p / 4 ∧
      ‖Word.euclidean (roundedRealVector p hp x hy hpath) - sign • v‖ <
        4 * unitRoundoff p := by
  obtain ⟨sign, hsign, hangle⟩ := hdirection
  let output := Word.euclidean (roundedRealVector p hp x hy hpath)
  have herr := roundedRealVector_error hp x hy hn hguard hprecision hpath
  have houtput : ‖output - ‖y‖⁻¹ • y‖ < 2 * unitRoundoff p := herr.1.trans_lt herr.2
  have h := norm_sub_le_norm_sub_add_norm_sub output (‖y‖⁻¹ • y) (sign • v)
  have hfinal : ‖output - sign • v‖ < 9 * unitRoundoff p / 4 := by linarith
  exact ⟨sign, hsign, hfinal, by linarith [unitRoundoff_pos p]⟩

end NumStability.CertifiedTridiagonalEigenpairs
