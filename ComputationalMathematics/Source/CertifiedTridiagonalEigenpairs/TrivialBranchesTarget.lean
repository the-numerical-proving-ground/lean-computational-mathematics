import ComputationalMathematics.Source.CertifiedTridiagonalEigenpairs.ExactBranches
import ComputationalMathematics.Source.CertifiedTridiagonalEigenpairs.Parameters

/-!
# Exact branches of the selected tridiagonal eigensolver

The target binds the executable dispatch and native-word output to the
ordered requested ranks and the deterministic resource bounds used on
the exact paths.
-/

namespace NumStability.CertifiedTridiagonalEigenpairs

open FloatingPointFormat.UnboundedBinary
open NoisyRankCertificate (ascendingEigenvalue)
open scoped Matrix

/-- The written labels followed by the explicit dense coordinate columns.
Each position in the list occupies one native scalar word. -/
def exactBranchOutputWords {p n k : ℕ} {hp : 2 ≤ p} (out : ExactBranchOutput p hp n k) :
    List (Word p hp) :=
  List.ofFn out.labels ++
    List.ofFn (fun i : Fin (k * (n + 1)) =>
      let ji := (finProdFinEquiv (m := k) (n := n + 1)).symm i
      out.columns ji.2 ji.1)

namespace SourceTargets

/-- The zero-matrix and scalar branches of §3, with the input convention of
the main theorem and the exact-path work and explicit-output size bounds. -/
def tridiagonalExactBranches : Prop :=
  ∀ {p n k : ℕ} (hp : 2 ≤ p) (a : Fin (n + 1) → Word p hp) (b : Fin n → Word p hp)
    (J : Fin k ↪o Fin (n + 1)), 0 < k → precisionGuard (n + 1) p →
    let T := storedTridiagonal a b
    let hT : T.IsHermitian := sturmTridiagonal_isHermitian _ _
    (exactBranch a b J = none ↔ T ≠ 0 ∧ 2 ≤ n + 1) ∧
    (T = 0 ∨ n = 0 → ∃ out, exactBranch a b J = some out ∧
      let Q : Matrix (Fin (n + 1)) (Fin k) ℝ := fun i j => (out.columns i j).value
      let D := Matrix.diagonal (fun j => (out.labels j).value)
      (T = 0 → ∀ j, out.labels j = .zero) ∧
      (n = 0 → k = 1 ∧ ∀ j, out.labels j = a 0 ∧ ∀ i, Q i j = 1) ∧
      (∀ i j, Q i j = if i = J j then 1 else 0) ∧
      (∀ j, (out.labels j).value = ascendingEigenvalue hT (J j)) ∧
      T * Q = Q * D ∧ Qᵀ * Q = 1 ∧ out.trials = 0 ∧
      (exactBranchOutputWords out).length = k + (n + 1) * k ∧
      (exactBranchOutputWords out).length ≤ 2 * ((n + 1) * k) ∧
      exactBranchWorkBound n k ≤ 23 * ((n + 1) * k) * p * (out.trials + 1))

end SourceTargets

end NumStability.CertifiedTridiagonalEigenpairs
