import ComputationalMathematics.Source.CertifiedTridiagonalEigenpairs.TrivialBranches
import ComputationalMathematics.Source.CertifiedTridiagonalEigenpairs.TrivialBranchesExecutionTarget

/-!
# Correctness of the measured exact tridiagonal execution
-/

namespace NumStability.CertifiedTridiagonalEigenpairs

open FloatingPointFormat.UnboundedBinary
open scoped Matrix

theorem exactBranchWordInterpretation : SourceTargets.exactBranchWordInterpretation := by
  intro p hp
  refine ⟨rfl, fun negative m e hm => ⟨hm.1, hm.2, ?_⟩⟩
  rfl

private theorem mulVec_column_of_mul_diagonal {n k : ℕ}
    (T : Matrix (Fin n) (Fin n) ℝ) (Q : Matrix (Fin n) (Fin k) ℝ) (d : Fin k → ℝ)
    (h : T * Q = Q * Matrix.diagonal d) (j : Fin k) :
    T *ᵥ Q.col j = d j • Q.col j := by
  funext i
  have hij := congrArg (fun A : Matrix (Fin n) (Fin k) ℝ => A i j) h
  change (T * Q) i j = (Q * Matrix.diagonal d) i j at hij
  rw [Matrix.mul_diagonal] at hij
  simpa [Matrix.mulVec, Matrix.mul_apply, Matrix.col, dotProduct,
    smul_eq_mul, mul_comm] using hij

theorem tridiagonalExactBranchesExecution : SourceTargets.tridiagonalExactBranchesExecution := by
  refine ⟨exactBranchWordInterpretation, ?_⟩
  intro p n k hp a b J hk hguard
  dsimp only
  obtain ⟨hout, hwords⟩ := runExactBranch_output a b J
  obtain ⟨hwork, htrace⟩ := runExactBranch_work a b J hk
  obtain ⟨hdispatch, hexact⟩ := tridiagonalExactBranches hp a b J hk hguard
  refine ⟨htrace, runExactBranch_space a b J, hout ▸ hdispatch, ?_⟩
  intro hbranch
  obtain ⟨out, hbranch, hzero, hscalar, hcoordinates, hlabels, hresidual, hgram,
    htrials, hsize, hsize_le, _hbudget⟩ := hexact hbranch
  have hw : (runExactBranch a b J).words = exactBranchOutputWords out := by
    simpa [hbranch] using hwords
  refine ⟨out, hout.trans hbranch, hzero, hscalar, hcoordinates, hlabels, ?_,
    hresidual, hgram, htrials, hw, hw ▸ hsize, hw ▸ hsize_le, ?_⟩
  · exact mulVec_column_of_mul_diagonal _ _ _ hresidual
  · rw [htrials, zero_add, mul_one]
    exact hwork.trans (Nat.le_mul_of_pos_right _ (by omega))

end NumStability.CertifiedTridiagonalEigenpairs
