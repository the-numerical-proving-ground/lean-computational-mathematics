import ComputationalMathematics.Analysis.MatrixInequalities.CommonWitnessBlockPerturbation
import ComputationalMathematics.Analysis.SingularValues.CommonWitnessBlocks
import ComputationalMathematics.Source.CertifiedTridiagonalEigenpairs.SVDFirstWitnessTarget

namespace NumStability.CertifiedTridiagonalEigenpairs.ClaimTargets

open CommonWitnessBlockPerturbation CommonWitnessBlocks FloatingPointFormat.UnboundedBinary
  MatrixPolar
open scoped BigOperators

private theorem exists_orthogonal_complement {n k : ℕ} (hkn : k ≤ n)
    (Q : Matrix (Fin n) (Fin k) ℝ) (hQ : Q.transpose * Q = 1) :
    ∃ Qperp : Matrix (Fin n) (Fin (n - k)) ℝ,
      (Matrix.fromCols Q Qperp).transpose * Matrix.fromCols Q Qperp = 1 ∧
      complementProjector Q = Qperp * Qperp.transpose := by
  let I : Fin k ↪ Fin n := Fin.castLEEmb hkn
  obtain ⟨U, hU⟩ :=
    exists_orthonormalBasis_extending_fin_embedding I _ (columns_orthonormal Q hQ)
  have hUQ : (orthonormalBasisMatrix U).submatrix id I = Q := by
    ext i j
    change U (I j) i = Q i j
    rw [hU j]
  let Qperp := complementColumns I U
  have ⟨hLeft, hRight⟩ :
      (Matrix.fromCols Q Qperp).transpose * Matrix.fromCols Q Qperp = 1 ∧
      Matrix.fromCols Q Qperp * (Matrix.fromCols Q Qperp).transpose = 1 := by
    simpa only [hUQ] using split_basis_orthogonal I U
  refine ⟨Qperp, hLeft, ?_⟩
  rw [Matrix.transpose_fromCols, Matrix.fromCols_mul_fromRows] at hRight
  rw [complementProjector, ← hRight, add_sub_cancel_left]

/-- The source's Sylvester relation and its first common nuclear-norm witness. -/
theorem svdFirstWitness_proof : svdFirstWitness := by
  intro n k p hk hkn B Uhat Vhat s u z S HU HV R₁ R₂ hz hGramU hGramV hResidual
  have hu : 0 < u := unitRoundoff_pos p
  have hzPos : 0 < z := mul_pos (Real.sqrt_pos.2 (by exact_mod_cast (show 0 < k by omega))) hu
  have hθ : 0 ≤ 7 * z := by positivity
  have hHalf : 7 * z ≤ 1 / 2 := by linarith
  have hS : S.transpose = S := Matrix.diagonal_transpose s
  let r := 160 * (k : ℝ) * u * realMatrixOperatorNorm B
  have hcolumn (A : Matrix (Fin n) (Fin k) ℝ)
      (hA : ∀ j, vecNorm2 (fun i => A i j) ≤ 160 * u * realMatrixOperatorNorm B) :
      realMatrixNuclearNorm A ≤ r := by
    apply (realMatrixNuclearNorm_le_sum_column_budgets A _ hA).trans
    simp [r]
    ring_nf
    rfl
  have hR₁ := hcolumn R₁ (fun j => (le_max_left _ _).trans (hResidual j))
  have hR₂ := hcolumn R₂ (fun j => (le_max_right _ _).trans (hResidual j))
  obtain ⟨Q, hU, hQ, hHU, hHUpos, _, _, _⟩ :=
    exists_polarCompletion_of_gram_bound Uhat hkn hθ hGramU
  obtain ⟨P, hV, hP, hHV, hHVpos, _, _, _⟩ :=
    exists_polarCompletion_of_gram_bound Vhat hkn hθ hGramV
  obtain ⟨hFloorU, hInvNormU⟩ := polarH_lower_and_inverse_of_gram_bound Uhat hθ hHalf hGramU
  obtain ⟨hFloorV, hInvNormV⟩ := polarH_lower_and_inverse_of_gram_bound Vhat hθ hHalf hGramV
  obtain ⟨Qc, hQc, hProjQ⟩ := exists_orthogonal_complement hkn Q hQ
  obtain ⟨Pc, hPc, hProjP⟩ := exists_orthogonal_complement hkn P hP
  let C₀ := Qc.transpose * B * Pc
  let B₀ := Q * S * P.transpose + Qc * C₀ * Pc.transpose
  have hB₀ : blockReplacement B Q P S = B₀ := by
    simp only [blockReplacement, hProjQ, hProjP, B₀, C₀, Matrix.mul_assoc]
  have hSqrt : Real.sqrt (1 - 7 / 128 : ℝ) ≤ Real.sqrt (1 - 7 * z) :=
    Real.sqrt_le_sqrt (by linarith)
  have hDenom : (7 * z) / (1 + Real.sqrt (1 - 7 * z)) ≤
      (7 * z) / (1 + Real.sqrt (1 - 7 / 128)) :=
    div_le_div_of_nonneg_left hθ (by positivity) (add_le_add_right hSqrt 1)
  have hSharp : (7 * z) / (1 + Real.sqrt (1 - 7 / 128)) < 4 * z := by
    have hs : (3 / 4 : ℝ) < Real.sqrt (1 - 7 / 128) := by
      rw [Real.lt_sqrt (by norm_num : (0 : ℝ) ≤ 3 / 4)]
      norm_num
    apply (div_lt_iff₀ (by positivity : (0 : ℝ) < 1 + Real.sqrt (1 - 7 / 128))).2
    nlinarith [mul_pos hzPos (sub_pos.mpr hs)]
  have hC : 0 < (Real.sqrt 2)⁻¹ := by positivity
  have hInvU := inverse_identities_of_quadratic_lower HU hHU _ hC hFloorU
  have hInvV := inverse_identities_of_quadratic_lower HV hHV _ hC hFloorV
  have hSylvester := residual_sylvester_identity B Q P Uhat Vhat HU HV S hQ hP hU hV
    hHU hHV hS
  have hLeading := leading_block_nuclear_le B Q P Uhat Vhat HU HV S hQ hP hU hV
    hHU hHV hS _ _ hC hC hFloorU hFloorV
  have hCoeff : ((Real.sqrt 2)⁻¹ + (Real.sqrt 2)⁻¹)⁻¹ = (Real.sqrt 2)⁻¹ := by
    have hsq := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
    have hs : Real.sqrt 2 ≠ 0 := by positivity
    field_simp
    nlinarith
  simp only [div_eq_mul_inv, hCoeff, mul_comm _ ((Real.sqrt 2)⁻¹)] at hLeading
  have hLeftProject : Qc.transpose * complementProjector Q = Qc.transpose := by
    rw [hProjQ, ← Matrix.mul_assoc, (split_gram_blocks _ _ hQc).2.2.2, Matrix.one_mul]
  have hRightProject : complementProjector P * Pc = Pc := by
    rw [hProjP, Matrix.mul_assoc, (split_gram_blocks _ _ hPc).2.2.2, Matrix.mul_one]
  have hCross₁ : Qc.transpose * B * P = Qc.transpose * R₁ * HV⁻¹ := by
    have h := congrArg (Qc.transpose * ·)
      (left_cross_residual B Q P Uhat Vhat HU HV S hQ hU hV hInvV.2)
    simpa only [← Matrix.mul_assoc, hLeftProject] using h
  have hCross₂ : Q.transpose * B * Pc = HU⁻¹ * R₂.transpose * Pc := by
    have h := congrArg (· * Pc)
      (right_cross_residual B Q P Uhat Vhat HU HV S hP hU hV hHU hInvU.1)
    simpa only [Matrix.mul_assoc, hRightProject] using h
  have hPaired := blockReplacement_paired B Q P S hQ hP hS
  rw [hB₀] at hPaired
  have hBudget := blockReplacement_polar_nuclear_le B Q P Uhat Vhat HU HV S hQ hP
    hU hV hHU hHV hS hFloorU hFloorV hInvNormU hInvNormV
  rw [hB₀] at hBudget
  refine ⟨hR₁, hR₂, Q, P, Qc, Pc, ⟨hU, hQ, hHU, hHUpos⟩, ⟨hV, hP, hHV, hHVpos⟩,
    hFloorU, hFloorV, hQc, hPc, max_le ?_ ?_, max_le ?_ ?_, hSharp,
    hSylvester, hLeading, hCross₁, hCross₂, ?_, hPaired.1, hPaired.2, hBudget, ?_⟩
  · exact (polarH_sub_one_operatorNorm_le Uhat hθ hGramU).trans hDenom
  · exact (polarH_sub_one_operatorNorm_le Vhat hθ hGramV).trans hDenom
  · exact (sub_polar_operatorNorm_le Uhat Q hθ hGramU hU hQ).trans hDenom
  · exact (sub_polar_operatorNorm_le Vhat P hθ hGramV hV hP).trans hDenom
  · abel
  · dsimp [r] at hR₁ hR₂
    linarith

/-- Combining the first nuclear perturbation with the errors in the reported
labels gives the budget for the ordered complementary matching. -/
theorem svdComplementMatchingBudget_le {n k : ℕ} (p : ℕ)
    (B E₀ : Matrix (Fin n) (Fin n) ℝ) (I : Fin k → Fin n) (s : Fin k → ℝ)
    (hE₀ : realMatrixNuclearNorm E₀ ≤
      960 * (k : ℝ) * unitRoundoff p * realMatrixOperatorNorm B)
    (hLabels : ∀ j, |s j - ascendingRealSpectrum B (I j)| ≤
      16 * unitRoundoff p * realMatrixOperatorNorm B) :
    realMatrixNuclearNorm E₀ + (∑ j, |s j - ascendingRealSpectrum B (I j)|) ≤
      976 * (k : ℝ) * unitRoundoff p * realMatrixOperatorNorm B := by
  refine (add_le_add hE₀ (Finset.sum_le_sum fun j _ => hLabels j)).trans_eq ?_
  simp
  ring

end NumStability.CertifiedTridiagonalEigenpairs.ClaimTargets
