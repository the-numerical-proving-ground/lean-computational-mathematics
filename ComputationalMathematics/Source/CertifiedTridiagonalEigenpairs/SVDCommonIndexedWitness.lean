import ComputationalMathematics.Source.CertifiedTridiagonalEigenpairs.SVDCommonIndexedWitness.Defs
import ComputationalMathematics.Source.CertifiedTridiagonalEigenpairs.SVDFirstWitnessProof
import ComputationalMathematics.Source.CertifiedTridiagonalEigenpairs.SVDIndexedCompletionProof

/-!
# A full common SVD at the reported ranks

The thin polar factors give a first block replacement. Ordered complementary
clipping then keeps those factors at the requested ranks in one full SVD.
-/

namespace NumStability.CertifiedTridiagonalEigenpairs

open ClaimTargets FloatingPointFormat.UnboundedBinary OrderStatistics

/-- The rounded Gram, residual, and ordered value bounds imply the source's
common indexed SVD witness, using the same reported arrays and labels throughout. -/
theorem hasIndexedSVDWitness_of_output_bounds {n k p : ℕ} (hn : 2 ≤ n) (hk : 1 ≤ k)
    (B : Matrix (Fin n) (Fin n) ℝ) (I : Fin k → Fin n) (hI : StrictMono I)
    (Uhat Vhat : Matrix (Fin n) (Fin k) ℝ) (s : Fin k → ℝ)
    (hs : Monotone s) (hs₀ : ∀ j, 0 ≤ s j)
    (hsmall : Real.sqrt (k : ℝ) * unitRoundoff p ≤ 1 / 128)
    (hGramU : realMatrixOperatorNorm (Uhat.transpose * Uhat - 1) ≤
      7 * (Real.sqrt (k : ℝ) * unitRoundoff p))
    (hGramV : realMatrixOperatorNorm (Vhat.transpose * Vhat - 1) ≤
      7 * (Real.sqrt (k : ℝ) * unitRoundoff p))
    (hResidual : ∀ j,
      max (vecNorm2 (fun i => (B * Vhat - Uhat * Matrix.diagonal s) i j))
        (vecNorm2 (fun i => (B.transpose * Uhat - Vhat * Matrix.diagonal s) i j)) ≤
      160 * unitRoundoff p * realMatrixOperatorNorm B)
    (hLabels : ∀ j, |s j - ascendingRealSpectrum B (I j)| ≤
      16 * unitRoundoff p * realMatrixOperatorNorm B) :
    HasIndexedSVDWitness B I Uhat Vhat s (unitRoundoff p) := by
  have hkn : k ≤ n := by
    simpa only [Fintype.card_fin] using Fintype.card_le_of_injective I hI.injective
  obtain ⟨_, _, Q, P, Qperp, Pperp, _, _, _, _, hQ, hP, _, hDist, hSharp,
    _, _, _, _, _, _, _, hBudget, hEstimate⟩ :=
    svdFirstWitness_proof n k p hk hkn B Uhat Vhat s hsmall hGramU hGramV hResidual
  have hDistance : max (realMatrixOperatorNorm (Uhat - Q))
      (realMatrixOperatorNorm (Vhat - P)) ≤ 4 * Real.sqrt (k : ℝ) * unitRoundoff p := by
    simpa only [mul_assoc] using (hDist.trans (le_of_lt hSharp))
  have hc := svdIndexedCompletion_proof.2.2.2 n k p hn hk I hI B Uhat Vhat Q P Qperp Pperp s
    hs hs₀ hQ hP hLabels (hBudget.trans hEstimate) hDistance
  dsimp only at hc
  obtain ⟨_, _, _, _, hd, hd₀, hdI, A, D, _, _, _, hU, hV, _, _, _, _, hFactor,
    _, _, _, hError, hBound, hFinalDistance⟩ := hc
  let slots : Fin k ↪ Fin n := ⟨I, hI.injective⟩
  let U := (Matrix.fromCols Q (Qperp * A)).submatrix id (CommonWitnessBlocks.slotEquiv slots).symm
  let V := (Matrix.fromCols P (Pperp * D)).submatrix id (CommonWitnessBlocks.slotEquiv slots).symm
  let d := completeSelectedValues I (ascendingRealSpectrum B) s
  let E := U * Matrix.diagonal d * V.transpose - B
  exact ⟨U, V, E, d, hU, mul_eq_one_comm.mp hU, hV, mul_eq_one_comm.mp hV,
    hd, hd₀, hdI, hFactor, hError.trans hBound, hFinalDistance⟩

end NumStability.CertifiedTridiagonalEigenpairs
