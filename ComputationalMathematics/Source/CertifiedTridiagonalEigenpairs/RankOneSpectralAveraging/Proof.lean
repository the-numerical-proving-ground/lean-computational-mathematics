import ComputationalMathematics.Source.CertifiedTridiagonalEigenpairs.RankOneSpectralAveraging.Target

/-! The source statement follows from the rank-one interval averaging estimates. -/

open MeasureTheory

namespace NumStability.CertifiedTridiagonalEigenpairs

private theorem rankOneCoordinateProjectionWeight_eq {n : ℕ} {C : Matrix (Fin n) (Fin n) ℂ}
    (hC : C.IsHermitian) (i : Fin n) (I : Set ℝ) (t : ℝ) :
    rankOneCoordinateProjectionWeight hC i I t =
      coordinateSpectralWeight (isHermitian_add_diagonal_single hC i t) i I := by
  rw [rankOneCoordinateProjectionWeight, matrixSpectralProjection_apply_diag, Complex.ofReal_re]

theorem rankOneSpectralAveraging : SourceTargets.rankOneSpectralAveraging.{u} := by
  intro n i
  constructor
  · intro C hC I hI
    obtain ⟨a, b, hab, hIopen, hIclosed⟩ := hI
    simp only [rankOneCoordinateProjectionWeight_eq]
    exact ⟨integral_coordinateSpectralWeight_interval_le hC i hab hIopen hIclosed,
      fun ρ d hd _ hρ =>
        integral_coordinateSpectralWeight_interval_withDensity_le hC i hab hIopen hIclosed
          hd ρ hρ⟩
  · intro Ω _ ν _ κ _ C hC I hI ρ hκ
    filter_upwards [hκ] with ω hω
    obtain ⟨d, hd, hρ, hκω⟩ := hω
    obtain ⟨a, b, hab, hIopen, hIclosed⟩ := hI ω
    simp only [hκω, rankOneCoordinateProjectionWeight_eq]
    exact integral_coordinateSpectralWeight_interval_withDensity_le (hC ω) i hab hIopen hIclosed
      hd ρ hρ

end NumStability.CertifiedTridiagonalEigenpairs
