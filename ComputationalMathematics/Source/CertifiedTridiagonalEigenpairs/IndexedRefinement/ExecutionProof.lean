import ComputationalMathematics.Source.CertifiedTridiagonalEigenpairs.IndexedRefinement.ExecutionTarget
import ComputationalMathematics.Source.CertifiedTridiagonalEigenpairs.IndexedRefinement.Execution

/-! The enclosure, accuracy, and resource proof for the trace-free loop. -/

namespace NumStability.CertifiedTridiagonalEigenpairs

theorem indexedRefinementExecution : SourceTargets.indexedRefinementExecution := by
  unfold SourceTargets.indexedRefinementExecution
  intro n r q hq j a b
  dsimp only
  intro hr hprec hH hb
  exact runIndexedRefinement j a b hr hprec hH hb

end NumStability.CertifiedTridiagonalEigenpairs
