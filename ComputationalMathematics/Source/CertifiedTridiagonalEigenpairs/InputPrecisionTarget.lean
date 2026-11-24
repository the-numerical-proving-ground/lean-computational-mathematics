import ComputationalMathematics.Analysis.Eigenvalues.AscendingEigenvalueRoots
import ComputationalMathematics.Source.CertifiedTridiagonalEigenpairs.TridiagonalEigenpairRun
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-! The input, rank convention, and precision of the tridiagonal routine (§2). -/

namespace NumStability.CertifiedTridiagonalEigenpairs.SourceTargets

open FloatingPointFormat.UnboundedBinary NoisyRankCertificate

/-- The packed tridiagonal data and its increasing requested ranks determine the
working precision. Native output slots carry the same precision as the input. -/
def tridiagonalInputPrecision : Prop :=
  ∀ {n p : ℕ} (hp : 2 ≤ p) (a : Fin (n + 1) → Word p hp) (b : Fin n → Word p hp)
    (J : Finset ℕ) (hJ : J ⊆ Finset.Icc 1 (n + 1)),
    J.Nonempty → precisionGuard (n + 1) p →
    let T := storedTridiagonal a b
    let hT : T.IsHermitian := sturmTridiagonal_isHermitian _ _
    let lambda := ascendingEigenvalue hT
    let k := J.card
    let order := requestedRankOrder hJ
    let L := ⌈Real.logb 2 (n + 1 : ℕ)⌉₊
    let Lk := ⌈Real.logb 2 (k : ℕ)⌉₊
    let N := nextPowerOfTwo (n + 1)
    let Nk := nextPowerOfTwo k
    let Nquarter := quarterPowerOfTwo (n + 1)
    let q := workingPrecision (n + 1) k p
    let beta := rejectionBound (n + 1)
    1 ≤ k ∧ k ≤ n + 1 ∧
    Monotone lambda ∧
    T.charpoly.roots = Multiset.map lambda (Finset.univ : Finset (Fin (n + 1))).val ∧
    StrictMono order ∧ (∀ j, (∃ i, order i = j) ↔ j.val + 1 ∈ J) ∧
    N = 2 ^ L ∧ Nk = 2 ^ Lk ∧ Nquarter = 2 ^ ⌈(L : ℝ) / 4⌉₊ ∧
    q = 2 * p + 3 * L + Lk + 32 ∧ beta = 3 / (2048 * (N : ℝ) ^ 2) ∧
    L ≤ p - 7 ∧ Lk ≤ L ∧ q ≤ 2 * p + 4 * L + 32 ∧ 2 * p + 4 * L + 32 ≤ 6 * p + 4 ∧
    ∀ out : NativeTridiagonalOutput n p J hp,
      (∀ i, Native p hp (out.labels i)) ∧ (∀ j i, Native p hp (out.columns j i))

end NumStability.CertifiedTridiagonalEigenpairs.SourceTargets
