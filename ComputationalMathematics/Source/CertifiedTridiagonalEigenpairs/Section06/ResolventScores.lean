import ComputationalMathematics.Analysis.FunctionalCalculus.Resolvent.ImaginaryShift

/-! # Exact resolvent scores for certified tridiagonal eigenvectors -/

open Matrix
open scoped Matrix.Norms.L2Operator

namespace NumStability.CertifiedTridiagonalEigenpairs

/-- The shifted matrix is invertible, its inverse satisfies the positive imaginary-part identity,
and a nearby eigenvalue guarantees a diagonal score of at least `1 / (2 n η)`.
These exact estimates apply to real symmetric inputs, including the tridiagonal matrices in
Section 6 of *Certified tridiagonal eigenpairs in expected linear work*. -/
theorem exactResolventScores {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsSymm)
    {shift target η : ℝ} (hη : 0 < η) (htarget : target ∈ spectrum ℝ A)
    (hnear : |shift - target| ≤ η) :
    let K := MatrixResolvent.imaginaryShift (A.map Complex.ofReal) shift η
    let G := K⁻¹
    IsUnit K ∧ ‖G‖ ≤ η⁻¹ ∧
      (2 * Complex.I : ℂ)⁻¹ • (G - Gᴴ) = (η : ℂ) • (Gᴴ * G) ∧
      ∃ r : Fin n, (2 * (n : ℝ) * η)⁻¹ ≤ (G r r).im := by
  have hAc := MatrixResolvent.isHermitian_map_ofReal hA
  have htargetC : target ∈ spectrum ℝ (A.map Complex.ofReal) := by
    rw [← spectrum.algebraMap_mem_iff ℂ, Matrix.mem_spectrum_iff_isRoot_charpoly]
    change (A.map Complex.ofRealHom).charpoly.IsRoot (Complex.ofRealHom target)
    rw [Matrix.charpoly_map, Polynomial.isRoot_map_iff Complex.ofReal_injective]
    exact Matrix.mem_spectrum_iff_isRoot_charpoly.1 htarget
  obtain ⟨j, rfl⟩ := hAc.spectrum_real_eq_range_eigenvalues ▸ htargetC
  refine ⟨MatrixResolvent.isUnit_imaginaryShift hAc shift hη,
    MatrixResolvent.norm_inv_imaginaryShift_le hAc shift hη,
    MatrixResolvent.imaginaryPart_inv_imaginaryShift hAc shift hη, ?_⟩
  simpa using MatrixResolvent.exists_inv_imaginaryShift_diagonal_im_ge hAc shift hη j hnear

end NumStability.CertifiedTridiagonalEigenpairs
