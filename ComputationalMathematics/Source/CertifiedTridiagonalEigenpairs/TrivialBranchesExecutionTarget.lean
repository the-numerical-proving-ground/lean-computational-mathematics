import ComputationalMathematics.Source.CertifiedTridiagonalEigenpairs.ExactBranchExecution

/-!
# Exact tridiagonal branches with measured resources

This successor retains the zero and scalar output guarantees and uses the
work and storage observations of the scan and dense output execution.
-/

namespace NumStability.CertifiedTridiagonalEigenpairs.SourceTargets

open FloatingPointFormat.UnboundedBinary
open NoisyRankCertificate (ascendingEigenvalue)
open ScalarWork
open scoped Matrix

/-- The input and output word interpretation used by the exact branches. -/
def exactBranchWordInterpretation : Prop :=
  ∀ (p : ℕ) (hp : 2 ≤ p),
    (Word.zero : Word p hp).value = 0 ∧
    ∀ (negative : Bool) (m : ℕ) (e : ℤ) (hm : (format p hp).normalizedMantissa m),
      2 ^ (p - 1) ≤ m ∧ m < 2 ^ p ∧
      (Word.normal negative m e hm).value =
        (if negative then -1 else 1) * (m : ℝ) * (2 : ℝ) ^ (e - (p : ℤ))

/-- The complete exact-branch statement, using the actual dispatched result,
packed native output and observed work and live-word counts. -/
def tridiagonalExactBranchesExecution : Prop :=
  exactBranchWordInterpretation ∧
  (∀ {p n k : ℕ} (hp : 2 ≤ p) (a : Fin (n + 1) → Word p hp) (b : Fin n → Word p hp)
    (J : Fin k ↪o Fin (n + 1)), 0 < k → precisionGuard (n + 1) p →
    let T := storedTridiagonal a b
    let hT : T.IsHermitian := sturmTridiagonal_isHermitian _ _
    let run := runExactBranch a b J
    TraceAllowed p run.trace ∧ storage run.liveWords ≤ 24 * (n + 1 + (n + 1) * k) ∧
    (run.output = none ↔ T ≠ 0 ∧ 2 ≤ n + 1) ∧
    (T = 0 ∨ n = 0 → ∃ out, run.output = some out ∧
      let Q : Matrix (Fin (n + 1)) (Fin k) ℝ := fun i j => (out.columns i j).value
      let D := Matrix.diagonal (fun j => (out.labels j).value)
      (T = 0 → ∀ j, out.labels j = .zero) ∧
      (n = 0 → k = 1 ∧ ∀ j, out.labels j = a 0 ∧ ∀ i, Q i j = 1) ∧
      (∀ i j, Q i j = if i = J j then 1 else 0) ∧
      (∀ j, (out.labels j).value = ascendingEigenvalue hT (J j)) ∧
      (∀ j, T *ᵥ Q.col j = (out.labels j).value • Q.col j) ∧
      T * Q = Q * D ∧ Qᵀ * Q = 1 ∧ out.trials = 0 ∧
      run.words = exactBranchOutputWords out ∧
      run.words.length = k + (n + 1) * k ∧
      run.words.length ≤ 2 * ((n + 1) * k) ∧
      work run.trace ≤ 56 * ((n + 1) * k) * p * (out.trials + 1)))

end NumStability.CertifiedTridiagonalEigenpairs.SourceTargets
