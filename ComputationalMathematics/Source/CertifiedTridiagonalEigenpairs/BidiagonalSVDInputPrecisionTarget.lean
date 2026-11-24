import ComputationalMathematics.Analysis.SingularValues.FullRealSVD.Basic
import ComputationalMathematics.Source.CertifiedTridiagonalEigenpairs.BidiagonalSVDOracleOutput
import ComputationalMathematics.Source.CertifiedTridiagonalEigenpairs.BidiagonalSVDScaling
import ComputationalMathematics.Source.CertifiedTridiagonalEigenpairs.AcceptedOutput.RequestedRanks
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-! The bidiagonal input, selected triplets, and working precision (§1). -/

namespace NumStability.CertifiedTridiagonalEigenpairs.SourceTargets

open BidiagonalSVDRequest FloatingPointFormat.UnboundedBinary
open scoped Matrix

/-- Either packed bidiagonal orientation is admitted. The exact objects being
requested are the indicated columns of a full SVD in ascending rank order.
The returned label and vector arrays have the input's native precision. -/
def bidiagonalSVDInputPrecision : Prop :=
  ∀ {n p : ℕ} (hp : 2 ≤ p) (upper : Bool)
    (a : Fin (n + 1) → Word p hp) (b : Fin n → Word p hp)
    (I : Finset ℕ) (hI : I ⊆ Finset.Icc 1 (n + 1)),
    I.Nonempty → precisionGuard (n + 1) p →
    let B := storedBidiagonal upper a b
    let k := I.card
    let order := requestedRankOrder hI
    let σ := ascendingRealSpectrum B
    let L := ⌈Real.logb 2 (n + 1 : ℕ)⌉₊
    let Lk := ⌈Real.logb 2 (k : ℕ)⌉₊
    1 ≤ k ∧ k ≤ n + 1 ∧ StrictMono order ∧ (∀ j, (∃ i, order i = j) ↔ j.val + 1 ∈ I) ∧
    Monotone σ ∧ (∀ i, 0 ≤ σ i) ∧
    (∃ U V : OrthonormalBasis (Fin (n + 1)) ℝ (EuclideanSpace ℝ (Fin (n + 1))),
      B = orthonormalBasisMatrix U * Matrix.diagonal σ * (orthonormalBasisMatrix V).transpose ∧
      let Usel := (orthonormalBasisMatrix U).submatrix id order
      let Vsel := (orthonormalBasisMatrix V).submatrix id order
      let Dsel := Matrix.diagonal (σ ∘ order)
      B * Vsel = Usel * Dsel ∧ B.transpose * Usel = Vsel * Dsel) ∧
    svdWorkingPrecision (n + 1) k p = 4 * p + 3 * L + 3 * Lk + 56 ∧
    ∀ out : NativeSVDTriplets (n + 1) k p hp,
      (∀ i, Native p hp (out.labels i).value) ∧
      (∀ j i, Native p hp (out.leftMatrix j i)) ∧ (∀ j i, Native p hp (out.rightMatrix j i))

end NumStability.CertifiedTridiagonalEigenpairs.SourceTargets
