import ComputationalMathematics.Algorithms.LinearSystems.QR.GramSchmidt
import ComputationalMathematics.Analysis.Eigenvalues.ComplexHermitianL1.Basic
import ComputationalMathematics.Source.CertifiedTridiagonalEigenpairs.SVDIndexedCompletionTarget

namespace NumStability.CertifiedTridiagonalEigenpairs.ClaimTargets

open CommonWitnessBlocks FloatingPointFormat.UnboundedBinary Matrix.Bipartite OrderStatistics
open scoped BigOperators Matrix.Norms.L2Operator

private theorem nuclear_eq_sum_abs_eigenvalues {n : ℕ}
    {H : Matrix (Fin n) (Fin n) ℝ} (hH : H.IsHermitian) :
    realMatrixNuclearNorm H = ∑ i, |hermitianOrderedEigenvalue hH i| := by
  let e := hermitianOrderedEigenvalue hH
  let U := orthonormalBasisMatrix (hermitianOrderedEigenbasis hH)
  let sign (i : Fin n) : ℝ := if 0 ≤ e i then 1 else -1
  let S := Matrix.diagonal sign
  have hU : U.transpose * U = 1 :=
    orthonormalBasisMatrix_transpose_mul_self (hermitianOrderedEigenbasis hH)
  have hsign (i : Fin n) : sign i * sign i = 1 := by
    by_cases hi : 0 ≤ e i <;> simp [sign, hi]
  have hS : S.transpose * S = 1 := by
    simp [S, Matrix.diagonal_mul_diagonal, hsign]
  have hUS : (U * S).transpose * (U * S) = 1 := by
    rw [Matrix.transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc U.transpose,
      hU, Matrix.one_mul, hS]
  have hsabs (i : Fin n) : sign i * |e i| = e i := by
    by_cases hi : 0 ≤ e i
    · simp [sign, hi, abs_of_nonneg hi]
    · simp [sign, hi, abs_of_neg (lt_of_not_ge hi)]
  have hrec : H = (U * S) * Matrix.diagonal (fun i => |e i|) * U.transpose := by
    rw [Matrix.mul_assoc U S, Matrix.diagonal_mul_diagonal]
    simp only [hsabs]
    exact (hermitianSpectralMatrix_eigenvalues hH).symm
  have hs := ascendingRealSpectrum_eq_sorted_of_orthogonal_factorization H (U * S) U
    (fun i => |e i|) hUS hU (fun i => abs_nonneg (e i)) hrec
  calc
    realMatrixNuclearNorm H = ∑ i, ascendingRealSpectrum H i := by
      unfold realMatrixNuclearNorm
      exact (Equiv.sum_comp Fin.revPerm (rectSingularValue H)).symm
    _ = ∑ i, |e i| := by
      rw [hs]
      exact Equiv.sum_comp (Tuple.sort (fun i => |e i|)) (fun i => |e i|)

private theorem dilation_nuclear_eq {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    realMatrixNuclearNorm (finEmbedding A) = 2 * realMatrixNuclearNorm A := by
  obtain ⟨_, _, _, hnonneg, _⟩ := exists_orthonormalBases_ascendingRealSpectrum A
  have hrev : (∑ i, |hermitianOrderedEigenvalue (finEmbedding_isHermitian A) i|) =
      ∑ i, |ascendingZeroMassValues (ascendingRealSpectrum A) i| := by
    rw [← Equiv.sum_comp Fin.revPerm (fun i => |hermitianOrderedEigenvalue (finEmbedding_isHermitian A) i|)]
    simp only [Fin.revPerm_apply, finEmbedding_orderedEigenvalue]
  rw [nuclear_eq_sum_abs_eigenvalues (finEmbedding_isHermitian A), hrev, Fin.sum_univ_add]
  simp only [ascendingZeroMassValues_castAdd, ascendingZeroMassValues_natAdd, abs_neg]
  have hsum : (∑ i, |ascendingRealSpectrum A i|) = realMatrixNuclearNorm A := by
    simp_rw [abs_of_nonneg (hnonneg _)]
    exact Equiv.sum_comp Fin.revPerm (fun i => rectSingularValue A i)
  have hsum_rev : (∑ i : Fin n, |ascendingRealSpectrum A i.rev|) =
      ∑ i : Fin n, |ascendingRealSpectrum A i| := by
    simpa only [Fin.revPerm_apply] using Equiv.sum_comp Fin.revPerm (fun i => |ascendingRealSpectrum A i|)
  rw [hsum_rev, hsum]
  ring

private theorem countLE_slots {n k : ℕ} (I : Fin k ↪ Fin n)
    (a : Fin n → ℝ) (x : ℝ) :
    countLE a x = countLE (a ∘ I) x + countLE (a ∘ orderedComplement I) x := by
  unfold countLE
  rw [← (slotEquiv I).sum_comp (fun i => if a i ≤ x then (1 : ℝ) else 0),
    Fintype.sum_sum_type]
  rfl

private theorem orthonormal_columns_contraction {n k : ℕ} (Q : Matrix (Fin n) (Fin k) ℝ)
    (hQ : Q.transpose * Q = 1) : realMatrixOperatorNorm Q ≤ 1 := by
  apply realMatrixOperatorNorm_le_of_rectOpNorm2Le _ (by norm_num)
  apply GramSchmidtOrthonormalColumns.rectOpNorm2Le_one
  intro i j
  simpa only [rectangularGram, matMulRect, finiteTranspose, Matrix.mul_apply,
    Matrix.transpose_apply, idMatrix, Matrix.one_apply] using congrFun (congrFun hQ i) j

private theorem orthonormal_columns_mul_transpose_le {n k : ℕ}
    (Q P : Matrix (Fin n) (Fin k) ℝ) (A : Matrix (Fin k) (Fin k) ℝ)
    (hQ : Q.transpose * Q = 1) (hP : P.transpose * P = 1) :
    realMatrixOperatorNorm (Q * A * P.transpose) ≤ realMatrixOperatorNorm A := by
  have hPn : realMatrixOperatorNorm P.transpose ≤ 1 :=
    (realMatrixOperatorNorm_finiteTranspose P).le.trans
      (orthonormal_columns_contraction P hP)
  calc
    _ ≤ realMatrixOperatorNorm (Q * A) * realMatrixOperatorNorm P.transpose :=
      realMatrixOperatorNorm_rectMatMul_le _ _
    _ ≤ realMatrixOperatorNorm (Q * A) := mul_le_of_le_one_right (norm_nonneg _) hPn
    _ ≤ realMatrixOperatorNorm Q * realMatrixOperatorNorm A :=
      realMatrixOperatorNorm_rectMatMul_le _ _
    _ ≤ realMatrixOperatorNorm A :=
      mul_le_of_le_one_left (norm_nonneg _) (orthonormal_columns_contraction Q hQ)

theorem svdIndexedCompletion_proof : svdIndexedCompletion := by
  have singularBound (n : ℕ) (B E₀ : Matrix (Fin n) (Fin n) ℝ) :
      (∑ i, |ascendingRealSpectrum (B + E₀) i - ascendingRealSpectrum B i|) ≤
        realMatrixNuclearNorm E₀ := by
    simpa only [add_sub_cancel_left] using
      sum_abs_sub_ascendingRealSpectrum_le_nuclearNorm (B + E₀) B
  refine ⟨(fun _ => ComplexHermitianL1.ordered_perturbation_trace), ?_, ?_, ?_⟩
  · intro n B E₀
    refine ⟨?_, sum_abs_sub_finEmbedding_eigenvalues (B + E₀) B, singularBound n B E₀⟩
    rw [← finEmbedding_sub, add_sub_cancel_left, dilation_nuclear_eq]
  · intro n a b ha hb
    exact (sum_abs_sub_eq_integral_countLE a b ha hb).symm
  · intro n k p _hn hk I hI B Uhat Vhat Q P Qperp Pperp s hs hs0 hL hR
      u delta distance C₀ B₀ E₀ lambda hlabels hE₀ hdistance slots J t w d
    have hu : 0 ≤ u := (unitRoundoff_pos p).le
    have hdelta : 0 ≤ delta := mul_nonneg (mul_nonneg (by norm_num) hu) (norm_nonneg _)
    obtain ⟨_, _, hlambda, hlambda0, _⟩ := exists_orthonormalBases_ascendingRealSpectrum B
    obtain ⟨_, _, hw, _, _⟩ := exists_orthonormalBases_ascendingRealSpectrum (B + E₀)
    obtain ⟨Uc, Vc, ht, ht0, hC₀⟩ := exists_orthonormalBases_ascendingRealSpectrum C₀
    let A := orthonormalBasisMatrix Uc
    let D := orthonormalBasisMatrix Vc
    let L := Matrix.fromCols Q (Qperp * A)
    let R := Matrix.fromCols P (Pperp * D)
    let U := L.submatrix id (slotEquiv slots).symm
    let V := R.submatrix id (slotEquiv slots).symm
    have hA : A.transpose * A = 1 := orthonormalBasisMatrix_transpose_mul_self Uc
    have hD : D.transpose * D = 1 := orthonormalBasisMatrix_transpose_mul_self Vc
    have hU : U.transpose * U = 1 :=
      gram_reindex L _ (rotate_complement_gram Q Qperp A hL hA)
    have hV : V.transpose * V = 1 :=
      gram_reindex R _ (rotate_complement_gram P Pperp D hR hD)
    have hfactor (a : Fin k → ℝ) (b : Fin (n - k) → ℝ) :
        U * Matrix.diagonal (combinedValues slots a b) * V.transpose =
          Q * Matrix.diagonal a * P.transpose +
            Qperp * (A * Matrix.diagonal b * D.transpose) * Pperp.transpose := by
      change L.submatrix id (slotEquiv slots).symm *
        Matrix.diagonal (fun i => Sum.elim a b ((slotEquiv slots).symm i)) *
        (R.submatrix id (slotEquiv slots).symm).transpose = _
      rw [reindex_factorization]
      dsimp only [L, R]
      rw [fromCols_diagonal]
      simp only [Matrix.transpose_mul, Matrix.mul_assoc]
    have hB : B + E₀ = B₀ := by
      change B + (B₀ - B) = B₀
      abel
    have hrec : B + E₀ = U * Matrix.diagonal (combinedValues slots s t) * V.transpose := by
      rw [hB, hfactor, ← hC₀]
    have hsorted : w = combinedValues slots s t ∘ Tuple.sort (combinedValues slots s t) :=
      ascendingRealSpectrum_eq_sorted_of_orthogonal_factorization
        (B + E₀) U V _ hU hV (combinedValues_nonneg slots s t hs0 ht0) hrec
    have hsplit (x : ℝ) : countLE w x = countLE s x + countLE t x := by
      rw [countLE_ascendingRealSpectrum_eq_of_orthogonal_factorization
        (B + E₀) U V _ hU hV (combinedValues_nonneg slots s t hs0 ht0) hrec,
        countLE_slots slots]
      simp only [Function.comp_def, combinedValues_selected, combinedValues_complement]
    have href (x : ℝ) :
        countLE lambda x = countLE (lambda ∘ I) x + countLE (lambda ∘ J) x :=
      countLE_slots slots lambda x
    have hcancel (x : ℝ) : countLE t x - countLE (lambda ∘ J) x =
        countLE w x - countLE lambda x - (countLE s x - countLE (lambda ∘ I) x) := by
      rw [hsplit x, href x]
      ring
    have hmatch : matchingL1 t (lambda ∘ J) ≤
        realMatrixNuclearNorm E₀ + matchingL1 s (lambda ∘ I) :=
      (matchingL1_cancel_splits w lambda s (lambda ∘ I) t (lambda ∘ J)
        hw hlambda hs (hlambda.comp hI.monotone) ht (hlambda.comp J.monotone) hsplit href).trans
        (add_le_add (singularBound n B E₀) le_rfl)
    have hclip (l : Fin (n - k)) : |d (J l) - lambda (J l)| ≤ delta :=
      completeSelectedValues_abs_sub_le I lambda s delta hlambda hlambda0 hdelta hlabels (J l)
    have hdsel (j : Fin k) : d (I j) = s j :=
      completeSelectedValues_apply_selected I lambda s hI hs j
    refine ⟨hsorted, hcancel, hmatch, hclip, completeSelectedValues_monotone I lambda s hlambda,
      completeSelectedValues_nonneg I lambda s hs0, hdsel, A, D, hA, hD, hC₀, ?_⟩
    dsimp only
    let C := A * Matrix.diagonal (d ∘ J) * D.transpose
    let W := U * Matrix.diagonal d * V.transpose
    let E := W - B
    change U.transpose * U = 1 ∧ V.transpose * V = 1 ∧
      U.submatrix id I = Q ∧ V.submatrix id I = P ∧
      U.submatrix id J = Qperp * A ∧ V.submatrix id J = Pperp * D ∧
      B + E = W ∧ W = Q * Matrix.diagonal s * P.transpose + Qperp * C * Pperp.transpose ∧
      realMatrixOperatorNorm (C - C₀) ≤ realMatrixNuclearNorm E₀ + ((k : ℝ) + 1) * delta ∧
      (k = n → C = C₀ ∧ W = B₀) ∧
      realMatrixOperatorNorm E ≤ 2 * realMatrixNuclearNorm E₀ + ((k : ℝ) + 1) * delta ∧
      2 * realMatrixNuclearNorm E₀ + ((k : ℝ) + 1) * delta ≤
        1952 * (k : ℝ) * u * realMatrixOperatorNorm B ∧
      max (realMatrixOperatorNorm (Uhat - U.submatrix id I))
        (realMatrixOperatorNorm (Vhat - V.submatrix id I)) ≤ distance
    have hUI : U.submatrix id I = Q := by
      ext i j
      change L i ((slotEquiv slots).symm (slotEquiv slots (Sum.inl j))) = Q i j
      rw [Equiv.symm_apply_apply]
      rfl
    have hVI : V.submatrix id I = P := by
      ext i j
      change R i ((slotEquiv slots).symm (slotEquiv slots (Sum.inl j))) = P i j
      rw [Equiv.symm_apply_apply]
      rfl
    have hUJ : U.submatrix id J = Qperp * A := by
      ext i j
      change L i ((slotEquiv slots).symm (slotEquiv slots (Sum.inr j))) = (Qperp * A) i j
      rw [Equiv.symm_apply_apply]
      rfl
    have hVJ : V.submatrix id J = Pperp * D := by
      ext i j
      change R i ((slotEquiv slots).symm (slotEquiv slots (Sum.inr j))) = (Pperp * D) i j
      rw [Equiv.symm_apply_apply]
      rfl
    have hd : d = combinedValues slots s (d ∘ J) := by
      funext i
      obtain ⟨j, rfl⟩ := (slotEquiv slots).surjective i
      cases j with
      | inl j => exact (hdsel j).trans (combinedValues_selected slots s _ j).symm
      | inr l => exact (combinedValues_complement slots s (d ∘ J) l).symm
    have hW : W = Q * Matrix.diagonal s * P.transpose + Qperp * C * Pperp.transpose := by
      calc
        W = U * Matrix.diagonal (combinedValues slots s (d ∘ J)) * V.transpose :=
          congrArg (fun e => U * Matrix.diagonal e * V.transpose) hd
        _ = _ := hfactor s (d ∘ J)
    have hsel : (∑ j, |s j - lambda (I j)|) ≤ (k : ℝ) * delta := by
      calc
        _ ≤ ∑ _j : Fin k, delta := Finset.sum_le_sum (fun j _ => hlabels j)
        _ = _ := by simp
    have hdiag :
        realMatrixOperatorNorm (Matrix.diagonal (fun l => d (J l) - t l)) ≤
          realMatrixNuclearNorm E₀ + ((k : ℝ) + 1) * delta := by
      have hcap0 : 0 ≤ realMatrixNuclearNorm E₀ + ((k : ℝ) + 1) * delta :=
        add_nonneg (realMatrixNuclearNorm_nonneg _) (mul_nonneg (by positivity) hdelta)
      change ‖Matrix.diagonal (fun l : Fin (n - k) => d (J l) - t l)‖ ≤ _
      rw [Matrix.l2_opNorm_diagonal]
      apply (pi_norm_le_iff_of_nonneg hcap0).mpr
      intro l
      rw [Real.norm_eq_abs]
      calc
        _ ≤ |d (J l) - lambda (J l)| + |lambda (J l) - t l| := abs_sub_le _ _ _
        _ ≤ delta + matchingL1 t (lambda ∘ J) := by
          apply add_le_add (hclip l)
          rw [abs_sub_comm]
          exact Finset.single_le_sum (fun l _ => abs_nonneg (t l - lambda (J l)))
            (Finset.mem_univ l)
        _ ≤ delta + (realMatrixNuclearNorm E₀ + (k : ℝ) * delta) :=
          add_le_add le_rfl (hmatch.trans (add_le_add le_rfl hsel))
        _ = _ := by ring
    have hCdiff : C - C₀ = A * Matrix.diagonal (fun l => d (J l) - t l) * D.transpose := by
      change A * Matrix.diagonal (d ∘ J) * D.transpose - C₀ = _
      rw [hC₀]
      have he : Matrix.diagonal (fun l => d (J l) - t l) =
          Matrix.diagonal (d ∘ J) - Matrix.diagonal t :=
        (Matrix.diagonal_sub (d ∘ J) t).symm
      rw [he, Matrix.mul_sub, Matrix.sub_mul]
    have hCbound : realMatrixOperatorNorm (C - C₀) ≤
        realMatrixNuclearNorm E₀ + ((k : ℝ) + 1) * delta := by
      rw [hCdiff]
      exact (orthonormal_columns_mul_transpose_le A D _ hA hD).trans hdiag
    have hWdiff : W - B₀ = Qperp * (C - C₀) * Pperp.transpose := by
      unfold B₀
      rw [hW, Matrix.mul_sub, Matrix.sub_mul]
      abel
    have hWbound : realMatrixOperatorNorm (W - B₀) ≤
        realMatrixNuclearNorm E₀ + ((k : ℝ) + 1) * delta := by
      rw [hWdiff]
      exact (orthonormal_columns_mul_transpose_le Qperp Pperp _ (split_gram_blocks Q Qperp hL).2.2.2
        (split_gram_blocks P Pperp hR).2.2.2).trans hCbound
    have hEbound : realMatrixOperatorNorm E ≤
        2 * realMatrixNuclearNorm E₀ + ((k : ℝ) + 1) * delta := by
      have he : E = (W - B₀) + E₀ := by dsimp only [E, E₀]; abel
      have htriangle : realMatrixOperatorNorm E ≤
          realMatrixOperatorNorm (W - B₀) + realMatrixOperatorNorm E₀ := by
        rw [he]
        exact norm_add_le (W - B₀) E₀
      linarith only [htriangle, hWbound, realMatrixOperatorNorm_le_nuclearNorm E₀]
    have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
    have hkdelta : delta ≤ (k : ℝ) * delta := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hkR hdelta
    have hnum : 2 * realMatrixNuclearNorm E₀ + ((k : ℝ) + 1) * delta ≤
        1952 * (k : ℝ) * u * realMatrixOperatorNorm B := by
      dsimp only [delta] at hkdelta ⊢
      nlinarith only [hE₀, hkdelta]
    refine ⟨hU, hV, hUI, hVI, hUJ, hVJ, ?_, hW, hCbound, ?_, hEbound, hnum, ?_⟩
    · change B + (W - B) = W
      abel
    · intro hfull
      have hempty : n - k = 0 := Nat.sub_eq_zero_of_le (by rw [hfull])
      letI : IsEmpty (Fin (n - k)) := by rw [hempty]; infer_instance
      have hzero : C = C₀ := by
        ext l
        exact isEmptyElim l
      refine ⟨hzero, ?_⟩
      rw [hW, hzero]
    · simpa only [hUI, hVI] using hdistance

end NumStability.CertifiedTridiagonalEigenpairs.ClaimTargets
