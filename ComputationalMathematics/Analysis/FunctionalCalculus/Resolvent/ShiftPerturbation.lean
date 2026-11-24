import ComputationalMathematics.Analysis.FunctionalCalculus.Resolvent.ImaginaryShift
import Mathlib.Analysis.Normed.Ring.Units

/-! # Operator norm and identities for a perturbed imaginary shift -/

open Matrix
open scoped Matrix.Norms.L2Operator

namespace NumStability.MatrixResolvent

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- A perturbation of norm less than the shift height preserves invertibility. The inverse
satisfies both orders of the resolvent identity and the reciprocal gap norm bound. -/
theorem imaginaryShift_perturbation {A E : Matrix n n ℂ} (hA : A.IsHermitian)
    {shift η : ℝ} (hη : 0 < η) (hE : ‖E‖ < η) :
    let K := imaginaryShift A shift η
    let G := K⁻¹
    let H := (K + E)⁻¹
    IsUnit (K + E) ∧ ‖H‖ ≤ (η - ‖E‖)⁻¹ ∧
      H - G = -(H * E * G) ∧ H = G - G * E * H := by
  let K := imaginaryShift A shift η
  let G := K⁻¹
  let H := (K + E)⁻¹
  have hK : IsUnit K := isUnit_imaginaryShift hA shift hη
  have hGnorm : ‖G‖ ≤ η⁻¹ := norm_inv_imaginaryShift_le hA shift hη
  have hKmulG : K * G = 1 :=
    Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hK)
  have hsmall : ‖-(G * E)‖ < 1 := by
    rw [norm_neg]
    calc
      ‖G * E‖ ≤ ‖G‖ * ‖E‖ := Matrix.l2_opNorm_mul _ _
      _ ≤ η⁻¹ * ‖E‖ := mul_le_mul_of_nonneg_right hGnorm (norm_nonneg E)
      _ < η⁻¹ * η := mul_lt_mul_of_pos_left hE (inv_pos.mpr hη)
      _ = 1 := inv_mul_cancel₀ hη.ne'
  have hUnit : IsUnit (1 + G * E) := by
    have h := (Units.oneSub (-(G * E)) hsmall).isUnit
    rwa [Units.val_oneSub, sub_neg_eq_add] at h
  have hKadd : IsUnit (K + E) := by
    have h := hK.mul hUnit
    rwa [Matrix.mul_add, Matrix.mul_one, ← Matrix.mul_assoc, hKmulG, Matrix.one_mul] at h
  have hLeft : H - G = -(H * E * G) := by
    rw [show H - G = H * (K - (K + E)) * G from
      Matrix.inv_sub_inv (iff_of_true hKadd hK)]
    rw [sub_add_cancel_left, Matrix.mul_neg, Matrix.neg_mul]
  have hRight : H = G - G * E * H := by
    have h : G - H = G * ((K + E) - K) * H :=
      Matrix.inv_sub_inv (iff_of_true hK hKadd)
    rw [add_sub_cancel_left] at h
    exact eq_sub_of_add_eq (by simpa [add_comm] using ((sub_eq_iff_eq_add).1 h).symm)
  have hHnorm : ‖H‖ ≤ (η - ‖E‖)⁻¹ := by
    have hpre : ‖H‖ ≤ η⁻¹ + (‖H‖ * ‖E‖) * η⁻¹ := by
      have hsum : H = G - H * E * G := by
        simpa [sub_eq_add_neg, add_comm] using (sub_eq_iff_eq_add.1 hLeft)
      calc
        ‖H‖ = ‖G - H * E * G‖ := congrArg norm hsum
        _ ≤ ‖G‖ + ‖H * E * G‖ := norm_sub_le _ _
        _ ≤ η⁻¹ + (‖H‖ * ‖E‖) * η⁻¹ := by
          refine add_le_add hGnorm ((Matrix.l2_opNorm_mul _ _).trans ?_)
          exact mul_le_mul
            (Matrix.l2_opNorm_mul _ _) hGnorm (norm_nonneg _) (by positivity)
    have hmul := mul_le_mul_of_nonneg_left hpre hη.le
    have hsimp : η * (η⁻¹ + (‖H‖ * ‖E‖) * η⁻¹) = 1 + ‖H‖ * ‖E‖ := by
      field_simp
    rw [hsimp] at hmul
    rw [inv_eq_one_div, le_div_iff₀ (sub_pos.mpr hE)]
    nlinarith
  exact ⟨hKadd, hHnorm, hLeft, hRight⟩

end NumStability.MatrixResolvent
