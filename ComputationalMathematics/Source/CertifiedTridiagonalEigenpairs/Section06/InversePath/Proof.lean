import ComputationalMathematics.Source.CertifiedTridiagonalEigenpairs.Section06.InversePath.Target

namespace NumStability.CertifiedTridiagonalEigenpairs

theorem vectorInverseRecurrence : SourceTargets.vectorInverseRecurrence := by
  intro q hq n a b η r
  obtain ⟨hroot, hscore, hstep⟩ := vectorRoundedInverseColumn_recurrence q hq n a b η r
  refine ⟨hroot, hscore, hstep, fun i j hj hz => ?_⟩
  exact roundedInversePath_zero_of_mem q hq _ _ _ _
    (List.mem_map.mpr ⟨j, hj, rfl⟩) hz

theorem vectorRoundedPath : SourceTargets.vectorRoundedPath := by
  intro q hq n hn a b η r hη u
  exact vectorRoundedInverseColumn_bounds q hq n hn a b η r hη

end NumStability.CertifiedTridiagonalEigenpairs
