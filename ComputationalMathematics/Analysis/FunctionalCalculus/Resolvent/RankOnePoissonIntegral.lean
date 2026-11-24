import ComputationalMathematics.Analysis.SpecialFunctions.PoissonKernel
import ComputationalMathematics.Analysis.FunctionalCalculus.Resolvent.RankOne

/-! The full-line integral for the diagonal entry of a rank-one resolvent. -/

open MeasureTheory

namespace NumStability

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Integrating the imaginary part of the perturbed diagonal resolvent over
the perturbation gives `π` at each spectral parameter in the upper half-plane. -/
theorem integral_im_diagonal_rankOne_resolvent {A : Matrix ι ι ℂ}
    (hA : A.IsHermitian) (i : ι) {z : ℂ} (hz : 0 < z.im) :
    ∫ t : ℝ, ((A + Matrix.diagonal (Pi.single i (t : ℂ)) - z • 1)⁻¹ i i).im = Real.pi := by
  simp_rw [diagonal_rankOne_resolvent hA i _ hz, im_inv_ofReal_sub_eq_poissonKernel]
  exact integral_poissonKernel _ (hz.trans_le (le_im_coordinateResolventCenter hA i hz))

end NumStability
