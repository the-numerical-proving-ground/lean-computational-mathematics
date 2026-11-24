import ComputationalMathematics.Analysis.MatrixInequalities.ThinPolar.Defs
import ComputationalMathematics.Algorithms.LinearSystems.QR.GramSchmidtPolar
import ComputationalMathematics.Analysis.SingularValues.EckartYoung
import Mathlib.Tactic

/-!
# Exact thin-polar perturbation bounds

Gram control gives exact tall polar completions, sharp coercivity and inverse
bounds, and operator-norm estimates from column controls. The construction
reuses the existing right-Gram polar factor and completion.
-/

namespace NumStability.MatrixPolar

open scoped BigOperators Matrix.Norms.L2Operator

noncomputable section

private theorem rectBound_of_operatorNorm_le {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) {c : ℝ}
    (h : realMatrixOperatorNorm A ≤ c) : rectOpNorm2Le A c := by
  apply rectOpNorm2Le_of_complexMatrixOp2_realRectToCMatrix_le A
  rwa [← realMatrixOperatorNorm_eq_complexMatrixOp2_realRectToCMatrix]

private theorem polarH_posSemidef {n k : ℕ}
    (X : Matrix (Fin n) (Fin k) ℝ) :
    Matrix.PosSemidef (show Matrix (Fin k) (Fin k) ℝ from rectRightGramPolarH X) := by
  let V : Matrix (Fin k) (Fin k) ℝ := rectRightGramEigenbasis X
  have hd : (Matrix.diagonal (rectRightGramBasisSingularValue X)).PosSemidef :=
    Matrix.posSemidef_diagonal_iff.mpr (rectRightGramBasisSingularValue_nonneg X)
  have hform : (show Matrix (Fin k) (Fin k) ℝ from rectRightGramPolarH X) =
      V * Matrix.diagonal (rectRightGramBasisSingularValue X) * V.transpose := by
    change V * (Matrix.diagonal _ * V.transpose) =
      V * Matrix.diagonal _ * V.transpose
    exact (Matrix.mul_assoc _ _ _).symm
  rw [hform]
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
    hd.mul_mul_conjTranspose_same V

private theorem one_sub_polarH_opBound {n k : ℕ}
    (X : Matrix (Fin n) (Fin k) ℝ) {θ : ℝ}
    (hGram : realMatrixOperatorNorm (X.transpose * X - 1) ≤ θ) :
    opNorm2Le (fun i j => idMatrix k i j - rectRightGramPolarH X i j) θ := by
  have hD := opNorm2Le_of_rectOpNorm2Le_square _
    (rectBound_of_operatorNorm_le (X.transpose * X - 1) hGram)
  have hnegD : opNorm2Le
      (fun i j => idMatrix k i j - rectangularGram X i j) θ := by
    have heq : (fun i j => idMatrix k i j - rectangularGram X i j) =
        (fun i j => -((X.transpose * X - 1 : Matrix (Fin k) (Fin k) ℝ) i j)) := by
      ext i j
      simp only [Matrix.sub_apply, Matrix.mul_apply, Matrix.transpose_apply,
        rectangularGram, matMulRect, finiteTranspose, idMatrix, Matrix.one_apply]
      ring
    rw [heq]
    exact opNorm2Le_neg hD
  have hinput : opNorm2Le
      (fun i j => idMatrix k i j -
        matMul k (rectRightGramPolarH X) (rectRightGramPolarH X) i j) θ := by
    rw [rectRightGramPolarH_sq_eq_rectangularGram]
    exact hnegD
  have hprod := opNorm2Le_matMul_square_of_bounds
    (rectRightGramPolarResolvent X)
    (fun i j => idMatrix k i j -
      matMul k (rectRightGramPolarH X) (rectRightGramPolarH X) i j)
    (by norm_num : (0 : ℝ) ≤ 1)
    (rectRightGramPolarResolvent_opNorm2Le_one X) hinput
  rw [rectRightGramPolarResolvent_mul_id_sub_polarH_sq] at hprod
  simpa only [one_mul] using hprod

/-- A tall real matrix has an exact polar completion within its Gram-error radius. -/
theorem exists_polarCompletion_of_gram_bound {n k : ℕ}
    (X : Matrix (Fin n) (Fin k) ℝ) (hkn : k ≤ n) {θ : ℝ}
    (hθ : 0 ≤ θ)
    (hGram : realMatrixOperatorNorm (X.transpose * X - 1) ≤ θ) :
    ∃ Q : Matrix (Fin n) (Fin k) ℝ,
      let H : Matrix (Fin k) (Fin k) ℝ := rectRightGramPolarH X
      X = Q * H ∧ Q.transpose * Q = 1 ∧
      H.transpose = H ∧ H.PosSemidef ∧ H * H = X.transpose * X ∧
      realMatrixOperatorNorm (X - Q) ≤ θ ∧
      realMatrixOperatorNorm (H - 1) ≤ θ := by
  obtain ⟨Qf, hfactor, hQ⟩ := exists_rectRightGramPolarCompletion_of_tall X hkn
  let Q : Matrix (Fin n) (Fin k) ℝ := Qf
  let H : Matrix (Fin k) (Fin k) ℝ := rectRightGramPolarH X
  have hfactor' : X = (Q : Matrix (Fin n) (Fin k) ℝ) * H := by
    simpa only [Q, H, matMulRect, Matrix.mul_apply] using hfactor
  have hQgram : (Q : Matrix (Fin n) (Fin k) ℝ).transpose * Q = 1 := by
    ext i j
    simpa only [Matrix.mul_apply, Matrix.transpose_apply, rectangularGram,
      Q, idMatrix, Matrix.one_apply] using hQ i j
  have hHsym : H.transpose = H := rectRightGramPolarH_symmetric X
  have hHpsd : H.PosSemidef := polarH_posSemidef X
  have hHsq : H * H = X.transpose * X := by
    simpa only [H, matMul, rectangularGram, Matrix.mul_apply,
      Matrix.transpose_apply] using rectRightGramPolarH_sq_eq_rectangularGram X
  have hIH : opNorm2Le (fun i j => idMatrix k i j - H i j) θ :=
    one_sub_polarH_opBound X hGram
  have hHI : opNorm2Le (fun i j => H i j - idMatrix k i j) θ := by
    have heq : (fun i j => H i j - idMatrix k i j) =
        (fun i j => -(idMatrix k i j - H i j)) := by
      ext i j
      ring
    rw [heq]
    exact opNorm2Le_neg hIH
  have hHnorm : realMatrixOperatorNorm (H - 1) ≤ θ := by
    apply realMatrixOperatorNorm_le_of_rectOpNorm2Le _ hθ
    simpa only [Matrix.sub_apply, Matrix.one_apply, idMatrix] using
      rectOpNorm2Le_of_opNorm2Le_square _ hHI
  have hXQpoint : rectOpNorm2Le
      (matMulRect n k k Q (fun i j => H i j - idMatrix k i j)) θ :=
    hQ.rectOpNorm2Le_matMulRect_square_right hHI
  have hXQeq : (X - Q : Matrix (Fin n) (Fin k) ℝ) =
      matMulRect n k k Q (fun i j => H i j - idMatrix k i j) := by
    change X - Q = Q * (H - 1)
    rw [Matrix.mul_sub, Matrix.mul_one, ← hfactor']
  have hXQnorm : realMatrixOperatorNorm (X - Q) ≤ θ := by
    rw [hXQeq]
    exact realMatrixOperatorNorm_le_of_rectOpNorm2Le _ hθ hXQpoint
  exact ⟨Q, hfactor', hQgram, hHsym, hHpsd, hHsq, hXQnorm, hHnorm⟩

private theorem gram_vector_bound {n k : ℕ}
    (X : Matrix (Fin n) (Fin k) ℝ) {θ : ℝ}
    (hGram : realMatrixOperatorNorm (X.transpose * X - 1) ≤ θ) :
    opNorm2Le (X.transpose * X - 1) θ := by
  apply opNorm2Le_of_rectOpNorm2Le_square
  apply rectOpNorm2Le_of_complexMatrixOp2_realRectToCMatrix_le
  rwa [← realMatrixOperatorNorm_eq_complexMatrixOp2_realRectToCMatrix]

private theorem singular_sq_deviation_of_gram_bound {n k : ℕ}
    (X : Matrix (Fin n) (Fin k) ℝ) {θ : ℝ}
    (hGram : realMatrixOperatorNorm (X.transpose * X - 1) ≤ θ) (a : Fin k) :
    |(rectRightGramBasisSingularValue X a) ^ 2 - 1| ≤ θ := by
  let v : Fin k → ℝ := fun j => rectRightGramEigenbasis X j a
  let D : Matrix (Fin k) (Fin k) ℝ := X.transpose * X - 1
  let σ : ℝ := rectRightGramBasisSingularValue X a
  have hv : vecNorm2Sq v = 1 := by
    simpa only [v, vecNorm2Sq, pow_two, idMatrix, if_pos rfl] using
      rectRightGramEigenbasis_col_orthonormal X a a
  have hG (j : Fin k) :
      (∑ l : Fin k, (X.transpose * X) j l * v l) = σ ^ 2 * v j := by
    simpa only [v, σ, Matrix.mul_apply, Matrix.transpose_apply, rectRightGram,
      rectRightGramBasisSingularValue_sq_eq] using
      rectRightGramEigenbasis_eigenvector X a j
  have hDv (j : Fin k) : matMulVec k D v j = (σ ^ 2 - 1) * v j := by
    change (∑ l : Fin k, ((X.transpose * X) j l - (1 : Matrix (Fin k) (Fin k) ℝ) j l) * v l) = _
    simp only [sub_mul, Finset.sum_sub_distrib, Matrix.one_apply]
    rw [hG]
    simp
  have hquad : (∑ j : Fin k, v j * matMulVec k D v j) = σ ^ 2 - 1 := by
    simp_rw [hDv]
    calc
      (∑ j : Fin k, v j * ((σ ^ 2 - 1) * v j)) =
          (σ ^ 2 - 1) * vecNorm2Sq v := by
        rw [vecNorm2Sq, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ = σ ^ 2 - 1 := by rw [hv, mul_one]
  have h := abs_vecInnerProduct_matMulVec_le_of_opNorm2Le D
    (gram_vector_bound X hGram) v
  rw [hquad, hv, mul_one] at h
  exact h

/-- The square-root denominator in the thin polar perturbation bound. -/
theorem polarH_sub_one_operatorNorm_le {n k : ℕ}
    (X : Matrix (Fin n) (Fin k) ℝ) {θ : ℝ} (hθ : 0 ≤ θ)
    (hGram : realMatrixOperatorNorm (X.transpose * X - 1) ≤ θ) :
    let H : Matrix (Fin k) (Fin k) ℝ := rectRightGramPolarH X
    realMatrixOperatorNorm (H - 1) ≤ θ / (1 + Real.sqrt (1 - θ)) := by
  let H : Matrix (Fin k) (Fin k) ℝ := rectRightGramPolarH X
  let V : Matrix (Fin k) (Fin k) ℝ := rectRightGramEigenbasis X
  let s := rectRightGramBasisSingularValue X
  have hV := rectRightGramEigenbasis_isOrthogonal X
  have hVV : V * V.transpose = 1 := by
    ext i j
    simpa only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply,
      finiteMatMul, matTranspose, finiteIdMatrix] using hV.2 i j
  have hHd : H = V * (Matrix.diagonal s * V.transpose) := rfl
  have hdiag : H - 1 =
      V * (Matrix.diagonal (fun i => s i - 1) * V.transpose) := by
    rw [← Matrix.diagonal_sub s (fun _ => (1 : ℝ)), Matrix.diagonal_one, Matrix.sub_mul, Matrix.mul_sub,
      Matrix.one_mul, hVV, hHd]
  have hbound : ∀ i, |s i - 1| ≤ θ / (1 + Real.sqrt (1 - θ)) := by
    intro i
    have hsq := singular_sq_deviation_of_gram_bound X hGram i
    change |s i ^ 2 - 1| ≤ θ at hsq
    have hs := rectRightGramBasisSingularValue_nonneg X i
    change 0 ≤ s i at hs
    have hlo : 1 - θ ≤ s i ^ 2 := by linarith [(abs_le.mp hsq).1]
    have hsqrt : Real.sqrt (1 - θ) ≤ s i := (Real.sqrt_le_iff).2 ⟨hs, hlo⟩
    rw [show s i ^ 2 - 1 = (s i - 1) * (s i + 1) by ring, abs_mul,
      abs_of_nonneg (by positivity : 0 ≤ s i + 1)] at hsq
    apply (le_div_iff₀ (by positivity : 0 < 1 + Real.sqrt (1 - θ))).2
    exact (mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg (s i - 1))).trans hsq
  have hc : 0 ≤ θ / (1 + Real.sqrt (1 - θ)) := by positivity
  apply realMatrixOperatorNorm_le_of_rectOpNorm2Le _ hc
  apply rectOpNorm2Le_of_opNorm2Le_square
  apply opNorm2Le_of_finiteOpNorm2Le
  exact finiteOpNorm2Le_of_isOrthogonal_diagonalization hdiag hV hc hbound

/-- An orthonormal family is nonexpansive as a map from its coefficient space. -/
theorem operatorNorm_thin_le_one {n k : ℕ} (Q : Matrix (Fin n) (Fin k) ℝ)
    (hQ : Q.transpose * Q = 1) : realMatrixOperatorNorm Q ≤ 1 := by
  apply realMatrixOperatorNorm_le_of_rectOpNorm2Le _ (by norm_num)
  apply GramSchmidtOrthonormalColumns.rectOpNorm2Le_one
  intro i j
  simpa only [rectangularGram, matMulRect, finiteTranspose, Matrix.mul_apply,
    Matrix.transpose_apply, idMatrix, Matrix.one_apply] using congrFun (congrFun hQ i) j

/-- The same scalar square-root bound controls the distance to any orthonormal
thin factor in the exact right Gram polar factorization. -/
theorem sub_polar_operatorNorm_le {n k : ℕ}
    (X Q : Matrix (Fin n) (Fin k) ℝ) {θ : ℝ} (hθ : 0 ≤ θ)
    (hGram : realMatrixOperatorNorm (X.transpose * X - 1) ≤ θ)
    (hX : X = Q * (show Matrix (Fin k) (Fin k) ℝ from rectRightGramPolarH X))
    (hQ : Q.transpose * Q = 1) :
    realMatrixOperatorNorm (X - Q) ≤ θ / (1 + Real.sqrt (1 - θ)) := by
  let H : Matrix (Fin k) (Fin k) ℝ := rectRightGramPolarH X
  have he : X - Q = Q * (H - 1) := by
    rw [Matrix.mul_sub, Matrix.mul_one, ← hX]
  have hnorm := polarH_sub_one_operatorNorm_le X hθ hGram
  rw [he]
  change ‖Q * (H - 1)‖ ≤ _
  exact (Matrix.l2_opNorm_mul _ _).trans
    ((mul_le_of_le_one_left (norm_nonneg _) (operatorNorm_thin_le_one Q hQ)).trans hnorm)

private theorem scalar_floor_and_inverse {s θ : ℝ}
    (hs : 0 ≤ s) (hθ : θ ≤ 1 / 2) (h : |s ^ 2 - 1| ≤ θ) :
    (Real.sqrt 2)⁻¹ ≤ s ∧ 0 < s ∧ |s⁻¹| ≤ Real.sqrt 2 := by
  have hsqrt : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hsqrt2 : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hc : 0 < (Real.sqrt 2)⁻¹ := inv_pos.mpr hsqrt
  have hc2 : ((Real.sqrt 2)⁻¹) ^ 2 = 1 / 2 := by
    rw [inv_pow, hsqrt2]
    norm_num
  have hs2 : 1 / 2 ≤ s ^ 2 := by
    have hh := (abs_le.mp h).1
    linarith
  have hfloor : (Real.sqrt 2)⁻¹ ≤ s := by
    nlinarith [hc.le]
  have hspos : 0 < s := hc.trans_le hfloor
  have hprod : 1 ≤ s * Real.sqrt 2 := by
    have hh := mul_le_mul_of_nonneg_right hfloor hsqrt.le
    simpa only [inv_mul_cancel₀ hsqrt.ne'] using hh
  have hinv : s⁻¹ ≤ Real.sqrt 2 := (inv_le_iff_one_le_mul₀' hspos).mpr hprod
  exact ⟨hfloor, hspos, by rwa [abs_of_pos (inv_pos.mpr hspos)]⟩

/-- Gram defect at most one half gives the sharp polar floor and inverse norm bound. -/
theorem polarH_lower_and_inverse_of_gram_bound {n k : ℕ}
    (X : Matrix (Fin n) (Fin k) ℝ) {θ : ℝ}
    (_hθ0 : 0 ≤ θ) (hθhalf : θ ≤ 1 / 2)
    (hGram : realMatrixOperatorNorm (X.transpose * X - 1) ≤ θ) :
    let H : Matrix (Fin k) (Fin k) ℝ := rectRightGramPolarH X
    (∀ x : Fin k → ℝ,
      (Real.sqrt 2)⁻¹ * vecNorm2Sq x ≤ finiteQuadraticForm H x) ∧
      realMatrixOperatorNorm H⁻¹ ≤ Real.sqrt 2 := by
  let H : Matrix (Fin k) (Fin k) ℝ := rectRightGramPolarH X
  let V := rectRightGramEigenbasis X
  let s := rectRightGramBasisSingularValue X
  let Hinv : Matrix (Fin k) (Fin k) ℝ :=
    finiteMatMul V (finiteMatMul (finiteDiagonal (fun i => (s i)⁻¹)) (matTranspose V))
  have hs (i : Fin k) : (Real.sqrt 2)⁻¹ ≤ s i ∧ 0 < s i ∧ |(s i)⁻¹| ≤ Real.sqrt 2 :=
    scalar_floor_and_inverse (rectRightGramBasisSingularValue_nonneg X i)
      hθhalf (singular_sq_deviation_of_gram_bound X hGram i)
  have hV : IsOrthogonal k V := rectRightGramEigenbasis_isOrthogonal X
  have hHdiag : H = finiteMatMul V (finiteMatMul (finiteDiagonal s) (matTranspose V)) := rfl
  have hInv : IsInverse k H Hinv :=
    isInverse_of_isOrthogonal_diagonalization hHdiag hV (fun i => (hs i).2.1.ne')
  have hInvBound : opNorm2Le Hinv (Real.sqrt 2) := by
    apply opNorm2Le_of_finiteOpNorm2Le
    exact finiteOpNorm2Le_of_isOrthogonal_diagonalization rfl hV
      (Real.sqrt_nonneg 2) (fun i => (hs i).2.2)
  have hInvNorm : realMatrixOperatorNorm Hinv ≤ Real.sqrt 2 :=
    realMatrixOperatorNorm_le_of_rectOpNorm2Le Hinv (Real.sqrt_nonneg 2)
      (rectOpNorm2Le_of_opNorm2Le_square Hinv hInvBound)
  have hRight : H * Hinv = 1 := by
    ext i j
    simpa only [Matrix.mul_apply, Matrix.one_apply] using hInv.2 i j
  have hActualInverse : H⁻¹ = Hinv := Matrix.inv_eq_right_inv hRight
  have hPSD : finitePSD H := Matrix_posSemidef.to_finitePSD H (polarH_posSemidef X)
  have hSym : IsSymmetricFiniteMatrix H := by
    intro i j
    have hh := congrFun (congrFun (rectRightGramPolarH_symmetric X) i) j
    exact hh.symm
  have hLower := finiteLoewnerLe_smul_id_le_of_right_inverse_opNorm2Le
    H Hinv (Real.sqrt_pos.mpr (by norm_num)) hPSD hSym hInv.2 hInvBound
  refine ⟨?_, ?_⟩
  · intro x
    have hx := hLower x
    simpa only [finiteQuadraticForm_smul_finiteIdMatrix, finiteVecNorm2Sq,
      vecNorm2Sq] using hx
  · rw [hActualInverse]
    exact hInvNorm

private theorem gram_diagonal_eq_column_norm_sq {n k : ℕ}
    (X : Matrix (Fin n) (Fin k) ℝ) (j : Fin k) :
    (X.transpose * X) j j = vecNorm2 (fun i => X i j) ^ 2 := by
  rw [vecNorm2_sq]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, vecNorm2Sq, pow_two]

private theorem gram_defect_entry_bound {n k : ℕ}
    (X : Matrix (Fin n) (Fin k) ℝ) (cO cN rho : ℝ)
    (_hcO : 0 ≤ cO) (hcN : 0 ≤ cN) (hrho : 0 ≤ rho) (hrho1 : rho ≤ 1)
    (hO : PairwiseGramBound X cO rho)
    (hN : ColumnNormDeviationBound X cN rho) :
    ∀ i j, |gramDefect X i j| ≤ gramControlConstant cO cN * rho := by
  intro i j
  have hKO : cO ≤ gramControlConstant cO cN :=
    (le_max_left cO (2 * cN + cN ^ 2)).trans
      (le_max_right 1 (max cO (2 * cN + cN ^ 2)))
  have hKN : 2 * cN + cN ^ 2 ≤ gramControlConstant cO cN :=
    (le_max_right cO (2 * cN + cN ^ 2)).trans
      (le_max_right 1 (max cO (2 * cN + cN ^ 2)))
  by_cases hij : i = j
  · subst j
    have hcol0 := vecNorm2_nonneg (fun h => X h i)
    have hupper : vecNorm2 (fun h => X h i) ≤ 1 + cN * rho := by
      have h := (abs_le.mp (hN i)).2
      linarith
    have hfactor : |vecNorm2 (fun h => X h i) ^ 2 - 1| =
        |vecNorm2 (fun h => X h i) - 1| * (vecNorm2 (fun h => X h i) + 1) := by
      rw [show vecNorm2 (fun h => X h i) ^ 2 - 1 =
        (vecNorm2 (fun h => X h i) - 1) * (vecNorm2 (fun h => X h i) + 1) by ring,
        abs_mul, abs_of_nonneg (show 0 ≤ vecNorm2 (fun h => X h i) + 1 by linarith)]
    have hsmall : |vecNorm2 (fun h => X h i) ^ 2 - 1| ≤
        (2 * cN + cN ^ 2) * rho := by
      rw [hfactor]
      calc
        _ ≤ (cN * rho) * (vecNorm2 (fun h => X h i) + 1) :=
          mul_le_mul_of_nonneg_right (hN i) (by linarith)
        _ ≤ (cN * rho) * (2 + cN * rho) :=
          mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg hcN hrho)
        _ ≤ _ := by
          have hrhosq : rho ^ 2 ≤ rho := by nlinarith
          have hprod := mul_nonneg (sq_nonneg cN) (sub_nonneg.mpr hrhosq)
          nlinarith
    have hentry : gramDefect X i i = vecNorm2 (fun h => X h i) ^ 2 - 1 := by
      simp only [gramDefect, Matrix.sub_apply, Matrix.one_apply,
        gram_diagonal_eq_column_norm_sq, ite_true]
    rw [hentry]
    exact hsmall.trans (mul_le_mul_of_nonneg_right hKN hrho)
  · have hentry : gramDefect X i j = (X.transpose * X) i j := by
      simp only [gramDefect, Matrix.sub_apply, Matrix.one_apply, if_neg hij, sub_zero]
    rw [hentry]
    exact (hO i j hij).trans (mul_le_mul_of_nonneg_right hKO hrho)

/-- Column controls imply the operator Gram bound with coefficient `k*K*rho`. -/
theorem gramDefect_operatorNorm_le_of_column_bounds {n k : ℕ}
    (X : Matrix (Fin n) (Fin k) ℝ) (cO cN rho : ℝ)
    (hcO : 0 ≤ cO) (hcN : 0 ≤ cN) (hrho : 0 ≤ rho) (hrho1 : rho ≤ 1)
    (hO : PairwiseGramBound X cO rho)
    (hN : ColumnNormDeviationBound X cN rho) :
    realMatrixOperatorNorm (gramDefect X) ≤
      (k : ℝ) * (gramControlConstant cO cN * rho) := by
  have hK0 : 0 ≤ gramControlConstant cO cN :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (le_max_left 1 _)
  have hentry := gram_defect_entry_bound X cO cN rho hcO hcN hrho hrho1 hO hN
  have hF := frobNormRect_le_sqrt_mul_nat_of_entry_abs_le (gramDefect X)
    (mul_nonneg hK0 hrho) hentry
  rw [Real.sqrt_mul_self (by positivity : (0 : ℝ) ≤ (k : ℝ))] at hF
  exact realMatrixOperatorNorm_le_of_rectOpNorm2Le (gramDefect X)
    (by positivity) (rectOpNorm2Le_of_frobNormRect_le _ hF)

end

end NumStability.MatrixPolar
