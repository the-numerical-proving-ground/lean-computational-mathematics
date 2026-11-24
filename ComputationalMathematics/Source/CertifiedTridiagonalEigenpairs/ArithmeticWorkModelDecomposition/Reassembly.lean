import ComputationalMathematics.Source.CertifiedTridiagonalEigenpairs.ArithmeticWorkModelDecomposition.Target
import ComputationalMathematics.Source.CertifiedTridiagonalEigenpairs.ArithmeticWorkModelSuccessorTarget

/-! The proof-free obligations reassemble into the full arithmetic target. -/

namespace NumStability.CertifiedTridiagonalEigenpairs

open SourceTargets

theorem arithmeticWorkModelParts_iff_successor :
    arithmeticWorkModelParts ↔ arithmeticWorkModelSuccessor := by
  simp only [arithmeticWorkModelParts, arithmeticWorkModelSuccessor,
    binaryRoundingModel, roundedScalarOperations, positivePrecisionArithmetic,
    arithmeticRoutinePrecisions, arithmeticExecutionCharges, arithmeticFairBitLaw,
    executionResources, arithmeticNormNotation, arithmeticMatrixNotation,
    arithmeticLogNotation, notationConventions, and_assoc]

theorem arithmeticWorkModelSuccessor_of_parts
    (rounding : binaryRoundingModel)
    (operations : roundedScalarOperations)
    (precisions : arithmeticRoutinePrecisions)
    (charges : arithmeticExecutionCharges)
    (bits : arithmeticFairBitLaw)
    (norms : arithmeticNormNotation)
    (matrices : arithmeticMatrixNotation)
    (logarithms : arithmeticLogNotation) :
    arithmeticWorkModelSuccessor :=
  arithmeticWorkModelParts_iff_successor.mp
    ⟨rounding, operations, precisions, charges, bits, norms, matrices, logarithms⟩

end NumStability.CertifiedTridiagonalEigenpairs
