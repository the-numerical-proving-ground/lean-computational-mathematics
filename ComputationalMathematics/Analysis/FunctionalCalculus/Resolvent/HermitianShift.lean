import Mathlib.Analysis.Matrix.Spectrum

/-! # Nonreal shifts of Hermitian matrices -/

namespace NumStability.MatrixResolvent

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A Hermitian matrix has an invertible shift at every nonreal complex number. -/
theorem isUnit_sub_smul_one {A : Matrix ι ι ℂ} (hA : A.IsHermitian)
    {z : ℂ} (hz : z.im ≠ 0) : IsUnit (A - z • 1) := by
  have h : z ∉ spectrum ℂ A := by
    rw [hA.spectrum_eq_image_range]
    rintro ⟨r, -, hr⟩
    exact hz (hr ▸ Complex.ofReal_im r)
  have hu := spectrum.notMem_iff.mp h
  rw [Algebra.algebraMap_eq_smul_one] at hu
  simpa only [neg_sub] using hu.neg

end NumStability.MatrixResolvent
