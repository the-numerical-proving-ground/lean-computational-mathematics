import ComputationalMathematics.Source.CertifiedTridiagonalEigenpairs.BidiagonalSVDTridiagonalCall
import ComputationalMathematics.Source.CertifiedTridiagonalEigenpairs.AcceptedOutput.NormalizedExecution

/-! The prepared bidiagonal request drives one tridiagonal eigensolver call. -/

namespace NumStability.CertifiedTridiagonalEigenpairs.BidiagonalSVDRequest

open FloatingPointFormat.UnboundedBinary MeasureTheory

/-- Every diagonal entry in the packed request has nonzero signed mass. -/
theorem shiftedDiagonal_nonzero (n k p : ℕ) (upper : Bool) (i : Fin (edgeCount n + 1)) :
    ((shiftedDiagonal n k p upper).get i).value ≠ 0 := by
  have hα : 0 < svdAlpha k p := by
    rw [svdAlpha_eq_unitRoundoff]
    exact unitRoundoff_pos _
  have hget (f : Fin (edgeCount n + 1) → AuxWord k p) :
      (Vector.ofFn f).get i = f i := Vector.getElem_ofFn i.isLt
  simp only [shiftedDiagonal, hget]
  cases bidiagonalParityCoord upper (n + 1) (bidiagonalRefinementCoord (by omega) i) <;>
    simp [value_massWord, ne_of_gt hα]

/-- A call made from the selected cut is nonzero, including when some original
singular values vanish. This follows from the positive mass on its diagonal. -/
theorem prepareTridiagonalCall_nonzero {n k p : ℕ} {hp : 2 ≤ p}
    (upper : Bool) (a : Fin (n + 1) → Word p hp) (b : Fin n → Word p hp)
    (I : Fin k → Fin (n + 1))
    (cmp : EmptyBinScan.Comparison (svdLabelPrecision k p) (svdLabelPrecision_ge_two k p))
    (hn : 2 ≤ n + 1) (hk : 1 ≤ k) (hguard : precisionGuard (n + 1) p)
    (hI : StrictMono I) {call : TridiagonalCall n k p}
    (hcall : prepareTridiagonalCall upper a b I cmp hn hk hguard hI = some call) :
    call.matrix ≠ 0 := by
  simp only [prepareTridiagonalCall] at hcall
  obtain ⟨pre, hlen, hpre, rfl⟩ := Option.pmap_eq_some_iff.mp hcall
  intro hz
  have h00 := congrArg
    (fun A : Matrix (Fin (edgeCount n + 1)) (Fin (edgeCount n + 1)) ℝ => A 0 0) hz
  exact shiftedDiagonal_nonzero n k p upper 0 (by
    simpa only [TridiagonalCall.matrix, assembleTridiagonalCall, storedTridiagonal,
      sturmTridiagonal_diagonal, Matrix.zero_apply] using h00)

/-- Invoke the actual tridiagonal eigensolver once, at the auxiliary
precision and with precisely the prepared rank set. -/
noncomputable def TridiagonalCall.solve {n k p : ℕ} (call : TridiagonalCall n k p)
    (hk : 1 ≤ k) (hguard : precisionGuard (n + 1) p)
    (bits : ℕ → GateBits (edgeCount n) call.oneBasedRanks) :
    Option (NativeAcceptedEigenpairs (edgeCount n) (svdAuxiliaryPrecision k p)
      call.oneBasedRanks (auxiliaryPrecision_ge_two k p)) :=
  let legal := call.admissible hk hguard
  normalizedEigenpairRun call.diagonal.get call.edges.get bits
    legal.1 legal.2.2.2.2.2.1 legal.2.1 call.oneBasedRanks_subset

theorem TridiagonalCall.ae_solve_returns {n k p : ℕ} (call : TridiagonalCall n k p)
    (hk : 1 ≤ k) (hguard : precisionGuard (n + 1) p) (hnonzero : call.matrix ≠ 0) :
    ∀ᵐ bits ∂retryBitMeasure (edgeCount n) call.oneBasedRanks,
      ∃ out, call.solve hk hguard bits = some out := by
  let legal := call.admissible hk hguard
  exact normalizedEigenpairRun_returns call.diagonal.get call.edges.get
    legal.1 legal.2.2.2.2.2.1 legal.2.1 call.oneBasedRanks_subset hnonzero

theorem TridiagonalCall.solve_accuracy {n k p : ℕ} (call : TridiagonalCall n k p)
    (hk : 1 ≤ k) (hguard : precisionGuard (n + 1) p)
    (bits : ℕ → GateBits (edgeCount n) call.oneBasedRanks)
    (out : NativeAcceptedEigenpairs (edgeCount n) (svdAuxiliaryPrecision k p)
      call.oneBasedRanks (auxiliaryPrecision_ge_two k p))
    (hrun : call.solve hk hguard bits = some out) :
    ReturnedAccuracy (requestedRankOrder call.oneBasedRanks_subset) call.matrix
      call.matrix_isHermitian out.columns out.labels (unitRoundoff (svdAuxiliaryPrecision k p)) := by
  let legal := call.admissible hk hguard
  exact normalizedEigenpairRun_accuracy call.diagonal.get call.edges.get bits
    legal.1 legal.2.2.2.2.2.1 legal.2.1 call.oneBasedRanks_subset out hrun

end NumStability.CertifiedTridiagonalEigenpairs.BidiagonalSVDRequest
