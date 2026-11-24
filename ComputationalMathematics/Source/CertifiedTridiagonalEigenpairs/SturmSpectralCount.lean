import ComputationalMathematics.Source.CertifiedTridiagonalEigenpairs.SturmSpectralCountTarget
import ComputationalMathematics.Analysis.Eigenvalues.HermitianWeyl

namespace NumStability.CertifiedTridiagonalEigenpairs

open Classical NoisyRankCertificate CongruenceInertia

theorem sturmSpectralCount : SourceTargets.sturmSpectralCount := by
  refine ⟨?_, ?_, ?_⟩
  · intro n H hH t
    refine ⟨ascendingEigenvalue_monotone hH, rfl, ?_, ?_⟩
    · rw [roots_charpoly_eq_ascendingEigenvalues hH, Multiset.filter_map, Multiset.card_map]
      rfl
    · exact (ScalarShift.negative_shifted_count_eq_strictBelowCount H hH t).symm
  · intro n H E hH hE j
    simpa only [add_sub_cancel_left] using
      Matrix.IsHermitian.abs_orderedEigenvaluesFin_sub_le_operatorNorm (hH.add hE) hH j.rev
  · exact fun _ _ _ hA hB L hcong => negative_eigenvalue_count_eq_congruence hA hB L hcong

end NumStability.CertifiedTridiagonalEigenpairs
