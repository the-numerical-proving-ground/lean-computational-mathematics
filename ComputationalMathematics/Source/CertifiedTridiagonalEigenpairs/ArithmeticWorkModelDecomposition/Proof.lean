import ComputationalMathematics.Source.CertifiedTridiagonalEigenpairs.ArithmeticWorkModelDecomposition.Reassembly
import ComputationalMathematics.Source.CertifiedTridiagonalEigenpairs.ArithmeticWorkModelSuccessor

/-! Proofs of the individual obligations from the checked arithmetic model. -/

namespace NumStability.CertifiedTridiagonalEigenpairs

private theorem arithmeticWorkModelParts : SourceTargets.arithmeticWorkModelParts :=
  arithmeticWorkModelParts_iff_successor.mpr arithmeticWorkModelSuccessor

theorem binaryRoundingModel : SourceTargets.binaryRoundingModel :=
  arithmeticWorkModelParts.1

theorem roundedScalarOperations : SourceTargets.roundedScalarOperations :=
  arithmeticWorkModelParts.2.1

theorem arithmeticRoutinePrecisions : SourceTargets.arithmeticRoutinePrecisions :=
  arithmeticWorkModelParts.2.2.1

theorem arithmeticExecutionCharges : SourceTargets.arithmeticExecutionCharges :=
  arithmeticWorkModelParts.2.2.2.1

theorem arithmeticFairBitLaw : SourceTargets.arithmeticFairBitLaw :=
  arithmeticWorkModelParts.2.2.2.2.1

theorem arithmeticNormNotation : SourceTargets.arithmeticNormNotation :=
  arithmeticWorkModelParts.2.2.2.2.2.1

theorem arithmeticMatrixNotation : SourceTargets.arithmeticMatrixNotation :=
  arithmeticWorkModelParts.2.2.2.2.2.2.1

theorem arithmeticLogNotation : SourceTargets.arithmeticLogNotation :=
  arithmeticWorkModelParts.2.2.2.2.2.2.2

end NumStability.CertifiedTridiagonalEigenpairs
