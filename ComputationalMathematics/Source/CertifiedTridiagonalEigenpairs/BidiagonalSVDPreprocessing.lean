import ComputationalMathematics.Source.CertifiedTridiagonalEigenpairs.BidiagonalSVDLabelCache
import ComputationalMathematics.Source.CertifiedTridiagonalEigenpairs.BidiagonalSVDScaling

/-!
# Deterministic preprocessing of stored bidiagonal input

A nonzero stored input determines the exact normalization exponent. The scalar
phase reads its exactly scaled bands and produces the label cache used by the
single first-empty-bin scan.
-/

namespace NumStability.CertifiedTridiagonalEigenpairs

open FloatingPointFormat.UnboundedBinary

/-- The physical scale, native label cache, and cut from the nonzero branch. -/
structure BidiagonalPreprocessing (k p : ℕ) where
  scaleExponent : ℤ
  cache : BidiagonalLabelCache (svdLabelPrecision k p) (svdLabelPrecision_ge_two k p)
  cutExecution : EmptyBinScan.SourceWork.Execution (svdLabelPrecision k p)
    (svdLabelPrecision_ge_two k p)

/-- Execute the source normalization, native refinements, and first-empty-bin
scan. The absent exponent leaves the exact zero branch to the caller. -/
noncomputable def preprocessBidiagonal {n k p : ℕ} {hp : 2 ≤ p} (upper : Bool)
    (a : Fin (n + 1) → Word p hp) (b : Fin n → Word p hp) (I : Fin k → Fin (n + 1))
    (cmp : EmptyBinScan.Comparison (svdLabelPrecision k p) (svdLabelPrecision_ge_two k p)) :
    Option (BidiagonalPreprocessing k p) :=
  (normalizationExponent a b).map fun e =>
    let C := storedBidiagonalWord upper (fun i => (a i).scale (-e)) (fun i => (b i).scale (-e))
    let cache := bidiagonalCachedRefinement (by omega) upper C I
    let cut := EmptyBinScan.SourceWork.runStored cmp (svdBinWidthWord k p) cache.labels
    ⟨e, cache, cut⟩

/-- Connect the executed preprocessing, including the same preserved label
stream, to the exact scaled bidiagonal matrix at its original requested indices. -/
theorem preprocessBidiagonal_spec {n k p : ℕ} {hp : 2 ≤ p} (upper : Bool)
    (a : Fin (n + 1) → Word p hp) (b : Fin n → Word p hp) (I : Fin k → Fin (n + 1))
    (cmp : EmptyBinScan.Comparison (svdLabelPrecision k p) (svdLabelPrecision_ge_two k p))
    (hn : 2 ≤ n + 1) (hk : 1 ≤ k) (hkn : k ≤ n + 1) (hguard : precisionGuard (n + 1) p)
    (hI : StrictMono I) {e : ℤ} (he : normalizationExponent a b = some e) :
    ∃ out : BidiagonalPreprocessing k p,
      preprocessBidiagonal upper a b I cmp = some out ∧ out.scaleExponent = e ∧
      let C := scaledBidiagonal upper a b e
      let labels := out.cache.labels
      let cut := out.cutExecution.result.state
      let s := fun i : Fin labels.length => (labels.get i).val
      let α := svdAlpha k p
      ∃ hlength : labels.length = k,
        (∀ i : Fin labels.length, |s i - ascendingRealSpectrum C (I (Fin.cast hlength i))| ≤
          unitRoundoff (svdAuxiliaryPrecision k p) / 64) ∧
        1 ≤ cut.j ∧ cut.j ≤ k + 1 ∧ EmptyCutBin α s cut.j ∧
        (∀ m : ℕ, 1 ≤ m → m < cut.j → ∃ i, InCutBin α m (s i)) ∧
        cut.lower.val = (cut.j : ℝ) * α ∧ cut.upper.val = ((cut.j + 1 : ℕ) : ℝ) * α ∧
        (∀ i : Fin labels.length, (s i < cut.lower.val ∧ s i ≤ 2 * unitRoundoff p) ∨
          (cut.upper.val ≤ s i ∧ 2 * α ≤ s i)) ∧ out.cutExecution.trace.length ≤ 71 * k := by
  let C := storedBidiagonalWord upper (fun i => (a i).scale (-e)) (fun i => (b i).scale (-e))
  let cache := bidiagonalCachedRefinement (by omega : 0 < n + 1) upper C I
  let cut := EmptyBinScan.SourceWork.runStored cmp (svdBinWidthWord k p) cache.labels
  refine ⟨⟨e, cache, cut⟩, ?_, rfl, ?_⟩
  · simp only [preprocessBidiagonal, he, Option.map_some]
    rfl
  · exact bidiagonalCachedCut_spec hn hk hkn hguard upper C I hI
      (scaledBidiagonal_support upper a b e) (scaledBidiagonal_bounds upper a b he).1 cmp

end NumStability.CertifiedTridiagonalEigenpairs
