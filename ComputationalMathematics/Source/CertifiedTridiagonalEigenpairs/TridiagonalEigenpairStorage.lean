import ComputationalMathematics.Source.CertifiedTridiagonalEigenpairs.AcceptedOutput.WholeRunStorage
import ComputationalMathematics.Source.CertifiedTridiagonalEigenpairs.ExactBranchExecution
import ComputationalMathematics.Source.CertifiedTridiagonalEigenpairs.TridiagonalEigenpairRun

/-! Complete peak space for the exact and normalized tridiagonal branches. -/

namespace NumStability.CertifiedTridiagonalEigenpairs

open FloatingPointFormat.UnboundedBinary ScalarWork

variable {n p : ℕ} {J : Finset ℕ} {hp : 2 ≤ p}

/-- Observe the phases used by `runTridiagonalEigenpairs`. The exact-branch
observation accounts for its packed scan and explicit outputs. On a nontrivial
input that scan is followed by normalization, fresh trials and accepted output. -/
noncomputable def tridiagonalEigenpairWorkspace
    (a : Fin (n + 1) → Word p hp) (b : Fin n → Word p hp)
    (bits : ℕ → GateBits n J) (hguard : precisionGuard (n + 1) p)
    (hJ : J.Nonempty) (hJvalid : J ⊆ Finset.Icc 1 (n + 1)) : ℕ :=
  let dispatch := storage (runExactBranch a b (requestedRankOrder hJvalid)).liveWords
  match h : exactBranch a b (requestedRankOrder hJvalid) with
  | some _ => dispatch
  | none => max dispatch <| normalizedEigenpairWorkspace a b bits
      ((exactBranch_eq_none_iff ..).mp h).2 hguard hJ hJvalid

/-- The exact observation reads the same labels and explicitly stored words
as the unified numerical interface. -/
theorem tridiagonalEigenpairWorkspace_exact_output
    (a : Fin (n + 1) → Word p hp) (b : Fin n → Word p hp)
    (bits : ℕ → GateBits n J) (hguard : precisionGuard (n + 1) p)
    (hJ : J.Nonempty) (hJvalid : J ⊆ Finset.Icc 1 (n + 1))
    (out : ExactBranchOutput p hp n J.card)
    (h : exactBranch a b (requestedRankOrder hJvalid) = some out) :
    runTridiagonalEigenpairs a b bits hguard hJ hJvalid =
      some (.exact out (runExactBranch a b (requestedRankOrder hJvalid)).words) := by
  have hwords := (runExactBranch_output a b (requestedRankOrder hJvalid)).2
  rw [h] at hwords
  unfold runTridiagonalEigenpairs
  split
  · rename_i branch hbranch
    rw [h] at hbranch
    cases Option.some.inj hbranch
    rw [hwords]
    rfl
  · rename_i hnone
    rw [h] at hnone
    contradiction

/-- Bound the full run pathwise, including every rejected-trial prefix and
the explicit output. The retry phases contribute their maximum, independent
of the number of rejected trials. -/
theorem tridiagonalEigenpairWorkspace_le
    (a : Fin (n + 1) → Word p hp) (b : Fin n → Word p hp)
    (bits : ℕ → GateBits n J) (hguard : precisionGuard (n + 1) p)
    (hJ : J.Nonempty) (hJvalid : J ⊆ Finset.Icc 1 (n + 1)) :
    tridiagonalEigenpairWorkspace a b bits hguard hJ hJvalid ≤
      64 * ((n + 1) + (n + 1) * J.card) := by
  have hdispatch := runExactBranch_space a b (requestedRankOrder hJvalid)
  unfold tridiagonalEigenpairWorkspace
  split
  · exact hdispatch.trans (by omega)
  · apply max_le (hdispatch.trans (by omega))
    exact normalizedEigenpairWorkspace_le _ _ _ _ _ _ _

end NumStability.CertifiedTridiagonalEigenpairs
