import ComputationalMathematics.Source.CertifiedTridiagonalEigenpairs.SVDFirstWitnessProof
import ComputationalMathematics.Source.CertifiedTridiagonalEigenpairs.SVDFirstWitnessSourceTarget

namespace NumStability.CertifiedTridiagonalEigenpairs.ClaimTargets

/-- The general block-replacement theorem at the source's strict Gram bounds. -/
theorem svdFirstWitnessSource_proof : svdFirstWitnessSource := by
  intro n k p hk hkn B Uhat Vhat s u z S HU HV R₁ R₂ _hs hsmall hGramU hGramV hResidual
  exact svdFirstWitness_proof n k p hk hkn B Uhat Vhat s hsmall hGramU.le hGramV.le hResidual

end NumStability.CertifiedTridiagonalEigenpairs.ClaimTargets
