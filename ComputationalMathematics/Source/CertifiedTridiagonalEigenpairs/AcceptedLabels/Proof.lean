import ComputationalMathematics.Source.CertifiedTridiagonalEigenpairs.AcceptedLabels.Target
import ComputationalMathematics.Source.CertifiedTridiagonalEigenpairs.FiniteTrial.Proof

/-! The certified finite gate supplies the hypotheses of the tighter refinement. -/

namespace NumStability.CertifiedTridiagonalEigenpairs

open FloatingPointFormat.UnboundedBinary NoisyRankCertificate
open scoped Matrix.Norms.L2Operator

noncomputable section

private theorem vectorTolerance_le_unitRoundoff (n k p : ℕ) :
    vectorTolerance n k p ≤ unitRoundoff p / 16 := by
  rw [vectorTolerance_eq_roundoff]
  unfold vectorToleranceExponent unitRoundoff
  calc
    (2 : ℝ) ^ (-((p + (p + 1) / 2 + 3 * Nat.clog 2 n + Nat.clog 2 k +
        (Nat.clog 2 n + 3) / 4 + 23 : ℕ) : ℤ)) ≤
      (2 : ℝ) ^ (-(p : ℤ) + (-4)) := by
        apply zpow_le_zpow_right₀ (by norm_num)
        push_cast
        omega
    _ = (2 : ℝ) ^ (-(p : ℤ)) / 16 := by
      rw [zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
      norm_num [div_eq_mul_inv]

private theorem abs_ascendingEigenvalue_le {N : ℕ} {M : Matrix (Fin N) (Fin N) ℝ}
    (hM : M.IsHermitian) (j : Fin N) :
    |ascendingEigenvalue hM j| ≤ realMatrixOperatorNorm M := by
  change |hermitianOrderedEigenvalue hM j.rev| ≤ ‖M‖
  have h := M.l2_opNorm_mulVec (hermitianOrderedEigenbasis hM j.rev)
  change ‖M.toEuclideanLin (hermitianOrderedEigenbasis hM j.rev)‖ ≤
    ‖M‖ * ‖hermitianOrderedEigenbasis hM j.rev‖ at h
  simpa [hermitianOrderedEigenbasis_apply, norm_smul, norm_hermitianOrderedEigenbasis,
    Real.norm_eq_abs] using h

set_option maxHeartbeats 1200000 in
/-- On the accepted matrix, the tighter native refinement gives the working
label and its rounded output with the bounds used in §7. -/
theorem acceptedIndexedLabels : SourceTargets.acceptedIndexedLabels := by
  intro n p J hp a b hn guard hJ hJvalid ha hb words haccepted j r trial av dv bv
    S M spectrumS spectrumM q h eta Δ omega u theta mu R result output
  obtain ⟨_, hclose, hcloseBudget, hM, hsame, hgap, _, _, _⟩ :=
    finiteTrialCertificate n p J a b hn guard hJ hJvalid ha hb words
  have hmatrix : M = trialMatrix a b words := trialRun_matrix_eq a b words
  rw [← hmatrix] at hclose hM hsame
  have hcloseFinal : realMatrixOperatorNorm (M - S) ≤ u / 128 :=
    hclose.trans hcloseBudget
  have hgapFinal (i : Fin (n + 1)) (hi : i ≠ j.val) :
      Δ < |spectrumM i - spectrumM j.val| :=
    hgap haccepted j.val j.property i hi
  have ⟨hmargin, hmarginBound⟩ := vectorTolerance_precision_margin (k := J.card) hn guard
  have hprec : h + 9 ≤ q := vectorToleranceExponent_add_nine_le (k := J.card) hn guard
  have hetaHalf : eta / 2 = unitRoundoff (h + 1) := vectorTolerance_half_eq_roundoff (n + 1) J.card p
  have hetaPositive : 0 < eta := by
    dsimp [eta]
    rw [vectorTolerance_eq_roundoff]
    exact unitRoundoff_pos _
  have hrefineExp : 2 ≤ h + 1 := by
    dsimp [h, vectorToleranceExponent]
    omega
  have hrefinePrec : h + 1 + 8 ≤ q := by simpa only [Nat.add_assoc] using hprec
  have hMrefine : realMatrixOperatorNorm M ≤ 3 / 2 := hM.le.trans (by norm_num)
  have hbRefine (i : Fin n) : |bv i| ≤ 1 := (hb i).trans (by norm_num)
  have hrefinement := indexedRefinement n (h + 1) q
    (workingPrecision_ge_two (n + 1) J.card p) j.val (fun i => trial.val.diagonal[i.val]) b
  obtain ⟨_, hlabelFine, hstrictFine, hwork, hallowed, hspace⟩ :=
    hrefinement hrefineExp hrefinePrec hMrefine hbRefine
  have htheta : |theta - spectrumM j.val| ≤ (423 / 256) * (eta / 2) := by
    rw [hetaHalf]
    exact hlabelFine
  have hthetaStrict : |theta - spectrumM j.val| < eta := by
    apply htheta.trans_lt
    rw [hetaHalf]
    calc
      _ < 2 * unitRoundoff (h + 1) := hstrictFine
      _ = eta := by rw [← hetaHalf]; ring
  have hu : 0 < u := unitRoundoff_pos p
  have huSmall : u ≤ 1 / 128 := by
    have hnReal : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast (show 1 ≤ n + 1 by omega)
    have h := mul_le_mul_of_nonneg_right hnReal hu.le
    simp only [one_mul] at h
    exact h.trans guard
  have hetaSmall : eta ≤ u / 16 := vectorTolerance_le_unitRoundoff (n + 1) J.card p
  have hlabelBudget : eta + u * (1 + eta) + u / 128 < 2 * u := by
    have hetaCompare : eta ≤ 1 / 16 := by linarith only [hetaSmall, huSmall]
    have hprod := mul_le_mul_of_nonneg_left hetaCompare hu.le
    linarith only [hetaSmall, hprod, hu]
  have heigenMag : |spectrumM j.val| < 1 :=
    (abs_ascendingEigenvalue_le (sturmTridiagonal_isHermitian dv bv) j.val).trans_lt hM
  have hthetaMag : |theta| ≤ 1 + eta := by
    have hsplit := abs_sub_le theta (spectrumM j.val) 0
    simp only [sub_zero] at hsplit
    linarith only [hsplit, hthetaStrict, heigenMag]
  have hmuM : |mu - spectrumM j.val| ≤ eta + u * (1 + eta) := by
    have hround : |mu - theta| ≤ u * (1 + eta) :=
      (abs_roundToEven_sub_le p hp theta).trans (mul_le_mul_of_nonneg_left hthetaMag hu.le)
    exact (abs_sub_le mu theta (spectrumM j.val)).trans
      (by linarith only [hround, hthetaStrict])
  have hmuMStrict : |mu - spectrumM j.val| < 2 * u := by linarith only [hmuM, hlabelBudget, hu]
  have hmuAbs : |mu| < 2 := by
    have hsplit := abs_sub_le mu (spectrumM j.val) 0
    simp only [sub_zero] at hsplit
    linarith only [hsplit, hmuMStrict, heigenMag, huSmall]
  have hweyl : |spectrumM j.val - spectrumS j.val| ≤ u / 128 :=
    (HDP.Matrix.abs_hermitianOrderedEigenvalue_sub_le_operatorNorm M S
      (sturmTridiagonal_isHermitian dv bv) (sturmTridiagonal_isHermitian av bv)
      j.val.rev).trans hcloseFinal
  have hmuS : |mu - spectrumS j.val| ≤ eta + u * (1 + eta) + u / 128 :=
    (abs_sub_le _ (spectrumM j.val) _).trans (add_le_add hmuM hweyl)
  have hmuSStrict : |mu - spectrumS j.val| < 2 * u := hmuS.trans_lt hlabelBudget
  have hout : output.value = R * mu := rescaledLabel_value p hp r theta
  have houtError : |output.value - R * spectrumS j.val| < R * (2 * u) := by
    have hR : 0 < R := by dsimp [R]; positivity
    rw [hout, ← mul_sub, abs_mul, abs_of_pos hR]
    exact mul_lt_mul_of_pos_left hmuSStrict hR
  have ⟨homegaEta, homegaEq, homegaDim⟩ := acceptedPrecisionBudget (k := J.card) hn guard
  exact ⟨hmatrix, hcloseFinal, hM, hsame, hgapFinal,
    (trialPrecisionBudget (k := J.card) hn guard).2.2.2.2,
    hmargin, hmarginBound, hprec, hetaHalf, hetaPositive, vectorTolerance_lt_half _ _ _,
    vectorTolerance_le_root_scale (by omega : 0 < n + 1) J.card p,
    dimension_mul_certifiedGap_lt (k := J.card) guard, homegaEta, homegaEq, homegaDim,
    htheta, hthetaStrict, hwork, hallowed, hspace, hmuM, hmuMStrict, hmuAbs, hmuS,
    hmuSStrict, hout, houtError⟩

end

end NumStability.CertifiedTridiagonalEigenpairs
