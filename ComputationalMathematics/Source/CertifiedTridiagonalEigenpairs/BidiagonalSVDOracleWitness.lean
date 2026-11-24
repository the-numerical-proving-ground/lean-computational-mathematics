import ComputationalMathematics.Source.CertifiedTridiagonalEigenpairs.BidiagonalSVDOracleOutput
import ComputationalMathematics.Source.CertifiedTridiagonalEigenpairs.SVDCommonIndexedWitness

/-!
# The common SVD witness for the native bidiagonal output

The returned labels and both returned arrays are read from the final p-bit
words, after column normalization and exact rescaling of the rounded labels.
-/

namespace NumStability.CertifiedTridiagonalEigenpairs.BidiagonalSVDRequest

open FloatingPointFormat.UnboundedBinary

variable {n k p : ℕ} {hp : 2 ≤ p}

/-- The common nearby matrix uses the actual rounded labels, at their original
requested ranks, with distances measured to the same returned columns. -/
theorem ReturnedTripletAccuracy.hasIndexedSVDWitness
    {B : Matrix (Fin n) (Fin n) ℝ} {I : Fin k → Fin n} {out : NativeSVDTriplets n k p hp}
    (h : ReturnedTripletAccuracy B I out) (hn : 2 ≤ n) (hk : 1 ≤ k) (hI : StrictMono I) :
    HasIndexedSVDWitness B I out.leftMatrix out.rightMatrix
      (fun j => (out.labels j).value) (unitRoundoff p) := by
  apply hasIndexedSVDWitness_of_output_bounds hn hk B I hI out.leftMatrix out.rightMatrix
    (fun j => (out.labels j).value) h.labels_monotone h.labels_nonnegative
  · nlinarith only [h.dimension_budget]
  · simpa only [mul_assoc] using h.left_gram.le
  · simpa only [mul_assoc] using h.right_gram.le
  · intro j
    exact max_le (h.left_residual j) (h.right_residual j)
  · intro j
    exact (h.value_error j).le

/-- Every successful prepared nonzero bidiagonal solve gives one common
indexed SVD witness for the result of final p-bit normalization and rounding. -/
theorem TridiagonalCall.prepared_solve_finish_indexedWitness (hp : 2 ≤ p) (upper : Bool)
    (a : Fin (n + 1) → Word p hp) (b : Fin n → Word p hp) (I : Fin k → Fin (n + 1))
    (cmp : EmptyBinScan.Comparison (svdLabelPrecision k p) (svdLabelPrecision_ge_two k p))
    (hn : 2 ≤ n + 1) (hk : 1 ≤ k) (hguard : precisionGuard (n + 1) p)
    (hI : StrictMono I) {r : ℤ} (hr : normalizationExponent a b = some r)
    (call : TridiagonalCall n k p)
    (hprep : prepareTridiagonalCall upper a b I cmp hn hk hguard hI = some call)
    (bits : ℕ → GateBits (edgeCount n) call.oneBasedRanks) (out : call.NativeParities)
    (hrun : call.solveParities upper hk hguard bits = some out) :
    ∃ (hL : ∀ j, Word.euclidean (out.left.get j).get ≠ 0)
      (hR : ∀ j, Word.euclidean (out.right.get j).get ≠ 0),
      let B := storedBidiagonal upper a b
      let result := call.finish (hp := hp) out hL hR
      ReturnedTripletAccuracy B I result ∧
        HasIndexedSVDWitness B I result.leftMatrix result.rightMatrix
          (fun j => (result.labels j).value) (unitRoundoff p) := by
  obtain ⟨hL, hR, hAccuracy⟩ :=
    prepared_solve_finish_accuracy hp upper a b I cmp hn hk hguard hI hr call hprep bits out hrun
  exact ⟨hL, hR, hAccuracy, hAccuracy.hasIndexedSVDWitness hn hk hI⟩

end NumStability.CertifiedTridiagonalEigenpairs.BidiagonalSVDRequest
