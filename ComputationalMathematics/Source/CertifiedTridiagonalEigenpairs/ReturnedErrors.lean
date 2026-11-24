import ComputationalMathematics.Analysis.FloatingPointArithmetic.UnboundedBinary.Basic
import ComputationalMathematics.Analysis.OperatorNorms.RealComplexification
import ComputationalMathematics.HDP.Matrix.Weyl
import Mathlib.Analysis.CStarAlgebra.Matrix

/-!
# Deterministic error bounds for the returned tridiagonal eigenpairs

This section assembles the accuracy guarantees in §7.2 from the accepted
matrix, the refined labels and the errors of the returned columns relative to
the signed exact eigenvectors of that same matrix.
-/

namespace NumStability.CertifiedTridiagonalEigenpairs

open Matrix WithLp
open scoped Matrix.Norms.L2Operator RealInnerProductSpace
open FloatingPointFormat.UnboundedBinary

noncomputable section

/-- The label refinement tolerance from §7.1, with the ceiling logarithms of
the matrix order and the number of requested indices. -/
def finalLabelTolerance (n k p : ℕ) : ℝ :=
  unitRoundoff (p + (p + 1) / 2 + 3 * Nat.clog 2 n + Nat.clog 2 k +
    (Nat.clog 2 n + 3) / 4 + 23)

/-- The deterministic assembly for the nonspecial branch of §7.2.
The library indexes eigenvalues in decreasing order, so `Fin.rev` converts
the requested increasing ranks. The columns of `U` are the signed exact
eigenvectors of the accepted matrix. -/
def returnedEigenpairErrorsClaim : Prop :=
  ∀ {n k p : ℕ} (hp : 2 ≤ p) (_hn : 2 ≤ n) (_hk : 0 < k) (_hkn : k ≤ n)
    (J : Fin k ↪o Fin n) (T S M : Matrix (Fin n) (Fin n) ℝ)
    (hT : T.IsHermitian) (hS : S.IsHermitian) (hM : M.IsHermitian)
    (R : ℝ) (_hR : 0 < R) (_hTscale : T = R • S) (_hRnorm : R < 8 * ‖T‖)
    (U Q : Matrix (Fin n) (Fin k) ℝ) (theta : Fin k → ℝ)
    (_hguard : (n : ℝ) * unitRoundoff p ≤ 1 / 128)
    (_hMS : ‖M - S‖ ≤ unitRoundoff p / 128) (_hMnorm : ‖M‖ < 1)
    (_hUorth : Uᵀ * U = 1)
    (_hUEig : M * U = U * diagonal (fun j => hermitianOrderedEigenvalue hM (J j).rev))
    (_htheta : ∀ j, |theta j - hermitianOrderedEigenvalue hM (J j).rev| ≤
      finalLabelTolerance n k p)
    (_hcolumn : ∀ j, ‖toLp 2 (Q.col j) - toLp 2 (U.col j)‖ ≤ 4 * unitRoundoff p),
    let u := unitRoundoff p
    let eta := finalLabelTolerance n k p
    let mu := fun j => roundToEven p hp (theta j)
    let D := diagonal mu
    let E := Q - U
    let rootk := Real.sqrt (k : ℝ)
    (‖E‖ ≤ frobNormRect E ∧ frobNormRect E ≤ 4 * rootk * u) ∧
    ‖Qᵀ * Q - 1‖ ≤ 9 * rootk * u ∧
    (∀ i j : Fin k, i ≠ j → |(Qᵀ * Q) i j| ≤ 9 * u) ∧
    (∀ j, |mu j - hermitianOrderedEigenvalue hM (J j).rev| ≤ eta + u * (1 + eta) ∧
      |mu j - hermitianOrderedEigenvalue hM (J j).rev| < 2 * u ∧ |mu j| < 2) ∧
    ‖M * Q - Q * D‖ ≤ 12 * rootk * u + 2 * u ∧
    ‖S * Q - Q * D‖ < 15 * rootk * u ∧
    ‖T * Q - Q * (R • D)‖ ≤ 128 * rootk * u * ‖T‖ ∧
    (∀ j, ‖toLp 2 (T *ᵥ Q.col j) - (R * mu j) • toLp 2 (Q.col j)‖ ≤
      128 * u * ‖T‖) ∧
    (∀ j, |mu j - hermitianOrderedEigenvalue hS (J j).rev| ≤
        eta + u * (1 + eta) + u / 128 ∧
      |mu j - hermitianOrderedEigenvalue hS (J j).rev| < 2 * u ∧
      |R * mu j - hermitianOrderedEigenvalue hT (J j).rev| ≤ 16 * u * ‖T‖)

private theorem finalLabelTolerance_le (n k p : ℕ) :
    finalLabelTolerance n k p ≤ unitRoundoff p / 16 := by
  unfold finalLabelTolerance unitRoundoff
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

private theorem gram_norm_le {n k : ℕ} (U E : Matrix (Fin n) (Fin k) ℝ)
    (hU : Uᵀ * U = 1) (hUnorm : ‖U‖ ≤ 1) :
    ‖(U + E)ᵀ * (U + E) - 1‖ ≤ 2 * ‖E‖ + ‖E‖ ^ 2 := by
  have norm_transpose (A : Matrix (Fin n) (Fin k) ℝ) : ‖Aᵀ‖ = ‖A‖ := by
    rw [← conjTranspose_eq_transpose_of_trivial, l2_opNorm_conjTranspose]
  have hexpand :
      (U + E)ᵀ * (U + E) - 1 = (Uᵀ * E + Eᵀ * U) + Eᵀ * E := by
    rw [Matrix.transpose_add, Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, hU]
    abel
  have h₁ := l2_opNorm_mul Uᵀ E
  have h₂ := l2_opNorm_mul Eᵀ U
  have h₃ := l2_opNorm_mul Eᵀ E
  rw [norm_transpose] at h₁ h₂ h₃
  calc
    _ = ‖(Uᵀ * E + Eᵀ * U) + Eᵀ * E‖ := congrArg norm hexpand
    _ ≤ ‖Uᵀ * E‖ + ‖Eᵀ * U‖ + ‖Eᵀ * E‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ ‖U‖ * ‖E‖ + ‖E‖ * ‖U‖ + ‖E‖ * ‖E‖ := by gcongr
    _ ≤ 2 * ‖E‖ + ‖E‖ ^ 2 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hUnorm) (norm_nonneg E)]

private theorem norm_of_orthonormal_columns {n k : ℕ} (U : Matrix (Fin n) (Fin k) ℝ)
    (hU : Uᵀ * U = 1) : ‖U‖ ≤ 1 := by
  have h := l2_opNorm_conjTranspose_mul_self U
  rw [conjTranspose_eq_transpose_of_trivial, hU] at h
  have hone : ‖(1 : Matrix (Fin k) (Fin k) ℝ)‖ ≤ 1 := by
    rw [← diagonal_one, l2_opNorm_diagonal]
    exact (pi_norm_le_iff_of_nonneg (by norm_num)).2 fun _ => by simp
  nlinarith [norm_nonneg U]

private theorem gram_entry_eq_inner {n k : ℕ} (A : Matrix (Fin n) (Fin k) ℝ)
    (i j : Fin k) :
    (Aᵀ * A) i j = ⟪toLp 2 (A.col i), toLp 2 (A.col j)⟫ := by
  calc
    _ = (toLp 2 (A.col j)).ofLp ⬝ᵥ star (toLp 2 (A.col i)).ofLp := by
      rw [star_trivial, dotProduct_comm]
      rfl
    _ = _ := (EuclideanSpace.inner_eq_star_dotProduct (𝕜 := ℝ)
      (toLp 2 (A.col i)) (toLp 2 (A.col j))).symm

private theorem frobenius_le_of_column_errors {n k : ℕ}
    (E : Matrix (Fin n) (Fin k) ℝ) {c : ℝ} (hc : 0 ≤ c)
    (hcol : ∀ j, ‖toLp 2 (E.col j)‖ ≤ c) :
    frobNormRect E ≤ c * Real.sqrt (k : ℝ) := by
  apply (sq_le_sq₀ (frobNormRect_nonneg E) (by positivity)).1
  rw [frobNormRect_sq, frobNormSqRect_eq_sum_vecNorm2Sq_cols, mul_pow,
    Real.sq_sqrt (by positivity)]
  calc
    _ ≤ ∑ _ : Fin k, c ^ 2 := by
      gcongr with j hj
      have h := (sq_le_sq₀ (norm_nonneg (toLp 2 (E.col j))) hc).2 (hcol j)
      rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)] at h
      simpa [vecNorm2Sq, Matrix.col, Real.norm_eq_abs, sq_abs] using h
    _ = _ := by simp [mul_comm]

private theorem eigenvalue_abs_le_norm {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ)
    (hM : M.IsHermitian) (i : Fin n) :
    |hermitianOrderedEigenvalue hM i| ≤ ‖M‖ := by
  have h := M.l2_opNorm_mulVec (hermitianOrderedEigenbasis hM i)
  change ‖M.toEuclideanLin (hermitianOrderedEigenbasis hM i)‖ ≤
    ‖M‖ * ‖hermitianOrderedEigenbasis hM i‖ at h
  simpa [hermitianOrderedEigenbasis_apply, norm_smul, norm_hermitianOrderedEigenbasis,
    Real.norm_eq_abs] using h

private theorem orderedEigenvalue_pos_smul {n : ℕ} {T S : Matrix (Fin n) (Fin n) ℝ}
    (hT : T.IsHermitian) (hS : S.IsHermitian)
    {R : ℝ} (hR : 0 < R) (hTscale : T = R • S) (i : Fin n) :
    hermitianOrderedEigenvalue hT i = R * hermitianOrderedEigenvalue hS i := by
  have hscale (x : EuclideanSpace ℝ (Fin n)) :
      matrixRayleighForm T x = R * matrixRayleighForm S x := by
    simp [matrixRayleighForm, hTscale, inner_smul_right]
  obtain ⟨F, hFdim, hFmin, _, hFall⟩ := hermitian_courantFischer_maxMin T hT i
  obtain ⟨G, hGdim, hGmin, _, hGall⟩ := hermitian_courantFischer_maxMin S hS i
  apply le_antisymm
  · obtain ⟨x, hxF, hxunit, hxle⟩ := hGall F hFdim
    have hxge := hFmin x hxF hxunit
    rw [hscale] at hxge
    exact hxge.trans (mul_le_mul_of_nonneg_left hxle hR.le)
  · obtain ⟨x, hxG, hxunit, hxle⟩ := hFall G hGdim
    have hxge := hGmin x hxG hxunit
    rw [hscale] at hxle
    exact (mul_le_mul_of_nonneg_left hxge hR.le).trans hxle

private theorem diagonals_diff_norm_le {k : ℕ} {a b : Fin k → ℝ} {c : ℝ}
    (hc : 0 ≤ c) (h : ∀ j, |a j - b j| ≤ c) :
    ‖diagonal a - diagonal b‖ ≤ c := by
  rw [diagonal_sub, l2_opNorm_diagonal]
  exact (pi_norm_le_iff_of_nonneg hc).2 fun j => by simpa [Real.norm_eq_abs] using h j

private theorem block_residual_le {n k : ℕ}
    (M : Matrix (Fin n) (Fin n) ℝ) (U E : Matrix (Fin n) (Fin k) ℝ)
    (A D : Matrix (Fin k) (Fin k) ℝ) (hEig : M * U = U * A) :
    ‖M * (U + E) - (U + E) * D‖ ≤
      (‖M‖ + ‖D‖) * ‖E‖ + ‖U‖ * ‖A - D‖ := by
  have hexpand : M * (U + E) - (U + E) * D = (M * E - E * D) + U * (A - D) := by
    rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub, hEig]
    abel
  rw [hexpand]
  calc
    _ ≤ (‖M * E‖ + ‖E * D‖) + ‖U * (A - D)‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
    _ ≤ (‖M‖ * ‖E‖ + ‖E‖ * ‖D‖) + ‖U‖ * ‖A - D‖ :=
      add_le_add (add_le_add (l2_opNorm_mul _ _) (l2_opNorm_mul _ _)) (l2_opNorm_mul _ _)
    _ = _ := by ring

private theorem transfer_residual_le {n k : ℕ}
    (M S : Matrix (Fin n) (Fin n) ℝ) (Q : Matrix (Fin n) (Fin k) ℝ)
    (D : Matrix (Fin k) (Fin k) ℝ) :
    ‖S * Q - Q * D‖ ≤ ‖M * Q - Q * D‖ + ‖M - S‖ * ‖Q‖ := by
  have hexpand : S * Q - Q * D = (M * Q - Q * D) - (M - S) * Q := by
    rw [Matrix.sub_mul]
    abel
  rw [hexpand]
  exact (norm_sub_le _ _).trans (add_le_add le_rfl (l2_opNorm_mul (M - S) Q))

private theorem residual_budget {u x : ℝ}
    (hu : 0 < u) (hux : u ≤ x) (hx : x ≤ 1 / 128) :
    12 * x + 2 * u + u / 128 * (1 + 4 * x) < 15 * x := by
  have hterm : u / 128 * (1 + 4 * x) ≤ u / 128 * 2 :=
    mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  linarith

private theorem column_residual_le {n : ℕ} (M S : Matrix (Fin n) (Fin n) ℝ)
    (q v : EuclideanSpace ℝ (Fin n)) (a d : ℝ)
    (hEig : M.toEuclideanLin v = a • v) :
    ‖S.toEuclideanLin q - d • q‖ ≤
      (‖M‖ + |d|) * ‖q - v‖ + |a - d| * ‖v‖ + ‖M - S‖ * ‖q‖ := by
  have hexpand : S.toEuclideanLin q - d • q =
      (M.toEuclideanLin (q - v) - d • (q - v)) + (a - d) • v -
        (M - S).toEuclideanLin q := by
    simp only [map_sub, LinearMap.sub_apply, smul_sub, sub_smul, hEig]
    abel
  rw [hexpand]
  have hop (A : Matrix (Fin n) (Fin n) ℝ) (x : EuclideanSpace ℝ (Fin n)) :
      ‖A.toEuclideanLin x‖ ≤ ‖A‖ * ‖x‖ := A.l2_opNorm_mulVec x
  calc
    _ ≤ (‖M.toEuclideanLin (q - v)‖ + ‖d • (q - v)‖) + ‖(a - d) • v‖ +
        ‖(M - S).toEuclideanLin q‖ :=
      (norm_sub_le _ _).trans (add_le_add ((norm_add_le _ _).trans
        (add_le_add (norm_sub_le _ _) le_rfl)) le_rfl)
    _ ≤ _ := by
      simp only [norm_smul, Real.norm_eq_abs, add_mul]
      gcongr <;> apply hop

private theorem pair_inner_error_le {n : ℕ}
    (qi qj vi vj : EuclideanSpace ℝ (Fin n)) {u : ℝ}
    (hu : 0 ≤ u) (hui : ‖vi‖ = 1) (huj : ‖vj‖ = 1)
    (horth : inner ℝ vi vj = 0) (hi : ‖qi - vi‖ ≤ 4 * u) (hj : ‖qj - vj‖ ≤ 4 * u) :
    |inner ℝ qi qj| ≤ 8 * u + 16 * u ^ 2 := by
  have hexpand : inner ℝ qi qj =
      (inner ℝ vi (qj - vj) + inner ℝ (qi - vi) vj) + inner ℝ (qi - vi) (qj - vj) := by
    simp only [inner_sub_left, inner_sub_right, horth]
    abel
  calc
    _ ≤ |inner ℝ vi (qj - vj)| + |inner ℝ (qi - vi) vj| + |inner ℝ (qi - vi) (qj - vj)| := by
      rw [hexpand]
      exact (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ ‖vi‖ * ‖qj - vj‖ + ‖qi - vi‖ * ‖vj‖ + ‖qi - vi‖ * ‖qj - vj‖ := by
      gcongr <;> exact abs_real_inner_le_norm _ _
    _ ≤ 1 * (4 * u) + (4 * u) * 1 + (4 * u) * (4 * u) := by
      rw [hui, huj]
      gcongr
    _ = _ := by ring

set_option maxHeartbeats 1800000 in
/-- The returned eigenvalue, residual and orthogonality bounds of §7.2. -/
theorem returnedEigenpairErrors : returnedEigenpairErrorsClaim := by
  intro n k p hp hn hk hkn J T S M hT hS hM R hR hTscale hRnorm U Q theta
    hguard hMS hMnorm hUorth hUEig htheta hcolumn u eta mu D E rootk
  let a := fun j => hermitianOrderedEigenvalue hM (J j).rev
  have hu : 0 < u := unitRoundoff_pos p
  have heta : eta ≤ u / 16 := finalLabelTolerance_le n k p
  have hroot_pos : 0 ≤ rootk := Real.sqrt_nonneg _
  have hroot_ge : 1 ≤ rootk := by
    apply (Real.le_sqrt (by norm_num) (by positivity)).2
    norm_num
    exact_mod_cast hk
  have hroot_le : rootk ≤ n := by
    have hk' : (k : ℝ) ≤ n := by exact_mod_cast hkn
    have hn' : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
    apply (Real.sqrt_le_left (by positivity)).2
    nlinarith
  have hu_le_x : u ≤ rootk * u := by
    simpa using mul_le_mul_of_nonneg_right hroot_ge hu.le
  have hx : rootk * u ≤ 1 / 128 :=
    (mul_le_mul_of_nonneg_right hroot_le hu.le).trans hguard
  have hu_small : u ≤ 1 / 128 := hu_le_x.trans hx
  have hsum_small : eta + u * (1 + eta) + u / 128 < 2 * u := by
    have heta_lt_one : eta ≤ 1 / 16 := by linarith
    have hprod := mul_le_mul_of_nonneg_left heta_lt_one hu.le
    linarith
  have hcolE (j : Fin k) : ‖toLp 2 (E.col j)‖ ≤ 4 * u := by
    have heq : toLp 2 (E.col j) = toLp 2 (Q.col j) - toLp 2 (U.col j) := by
      rfl
    rw [heq]
    exact hcolumn j
  have hEop : ‖E‖ ≤ frobNormRect E := realMatrixOperatorNorm_le_frobNormRect E
  have hEfrob : frobNormRect E ≤ 4 * rootk * u := by
    convert frobenius_le_of_column_errors E (show 0 ≤ 4 * u by positivity) hcolE using 1
    ring
  have hE : ‖E‖ ≤ 4 * rootk * u := hEop.trans hEfrob
  have hQ : U + E = Q := by
    dsimp [E]
    abel
  have hU : ‖U‖ ≤ 1 := norm_of_orthonormal_columns U hUorth
  have hQnorm : ‖Q‖ ≤ 1 + 4 * rootk * u := by
    rw [← hQ]
    exact (norm_add_le _ _).trans (add_le_add hU hE)
  have hgram : ‖Qᵀ * Q - 1‖ ≤ 9 * rootk * u := by
    rw [← hQ]
    calc
      _ ≤ 2 * ‖E‖ + ‖E‖ ^ 2 := gram_norm_le U E hUorth hU
      _ ≤ 2 * (4 * rootk * u) + (4 * rootk * u) ^ 2 := by gcongr
      _ ≤ _ := by
        have hnonneg : 0 ≤ rootk * u := by positivity
        have hmul := mul_nonneg hnonneg (sub_nonneg.mpr hx)
        nlinarith
  have hunit (j : Fin k) : ‖toLp 2 (U.col j)‖ = 1 := by
    have h := (gram_entry_eq_inner U j j).symm
    rw [hUorth, Matrix.one_apply_eq] at h
    change inner ℝ (toLp 2 (U.col j)) (toLp 2 (U.col j)) = 1 at h
    rw [real_inner_self_eq_norm_sq] at h
    nlinarith [norm_nonneg (toLp 2 (U.col j))]
  have hpairs (i j : Fin k) (hij : i ≠ j) : |(Qᵀ * Q) i j| ≤ 9 * u := by
    have horth : inner ℝ (toLp 2 (U.col i)) (toLp 2 (U.col j)) = 0 := by
      calc
        _ = (Uᵀ * U) i j := (gram_entry_eq_inner U i j).symm
        _ = 0 := by rw [hUorth, Matrix.one_apply_ne hij]
    calc
      _ ≤ 8 * u + 16 * u ^ 2 := by
        rw [gram_entry_eq_inner]
        exact pair_inner_error_le _ _ _ _ hu.le (hunit i) (hunit j) horth
          (hcolumn i) (hcolumn j)
      _ ≤ _ := by nlinarith [mul_nonneg hu.le (sub_nonneg.mpr hu_small)]
  have ha (j : Fin k) : |a j| < 1 :=
    (eigenvalue_abs_le_norm M hM (J j).rev).trans_lt hMnorm
  have hlabel (j : Fin k) :
      |mu j - a j| ≤ eta + u * (1 + eta) := by
    have htheta_abs := (abs_sub_le (theta j) (a j) 0)
    simp only [sub_zero] at htheta_abs
    have ht : |theta j| ≤ 1 + eta := by linarith [htheta j, ha j]
    calc
      _ ≤ |mu j - theta j| + |theta j - a j| := abs_sub_le _ _ _
      _ ≤ u * |theta j| + eta :=
        add_le_add (abs_roundToEven_sub_le p hp (theta j)) (htheta j)
      _ ≤ _ := by
        have h := mul_le_mul_of_nonneg_left ht hu.le
        linarith
  have hlabel_strict (j : Fin k) : |mu j - a j| < 2 * u := by
    linarith [hlabel j]
  have hmu (j : Fin k) : |mu j| < 2 := by
    have h := abs_sub_le (mu j) (a j) 0
    simp only [sub_zero] at h
    linarith [hlabel_strict j, ha j]
  have hD : ‖D‖ ≤ 2 := by
    dsimp [D]
    rw [l2_opNorm_diagonal]
    exact (pi_norm_le_iff_of_nonneg (by norm_num)).2 fun j => by
      simpa only [Real.norm_eq_abs] using (hmu j).le
  have hDiagDiff : ‖diagonal a - D‖ ≤ 2 * u := by
    exact diagonals_diff_norm_le (by positivity) fun j => by
      rw [abs_sub_comm]
      exact (hlabel_strict j).le
  have hStored : ‖M * Q - Q * D‖ ≤ 12 * rootk * u + 2 * u := by
    rw [← hQ]
    calc
      _ ≤ (‖M‖ + ‖D‖) * ‖E‖ + ‖U‖ * ‖diagonal a - D‖ :=
        block_residual_le M U E (diagonal a) D hUEig
      _ ≤ (1 + 2) * (4 * rootk * u) + 1 * (2 * u) := by gcongr
      _ = _ := by ring
  have hScaled : ‖S * Q - Q * D‖ < 15 * rootk * u := by
    calc
      _ ≤ ‖M * Q - Q * D‖ + ‖M - S‖ * ‖Q‖ := transfer_residual_le M S Q D
      _ ≤ 12 * rootk * u + 2 * u + u / 128 * (1 + 4 * rootk * u) := by gcongr
      _ < _ := by
        convert residual_budget hu hu_le_x hx using 1 <;> ring
  have hNormT : 0 ≤ ‖T‖ := norm_nonneg T
  have hBlock : ‖T * Q - Q * (R • D)‖ ≤ 128 * rootk * u * ‖T‖ := by
    calc
      _ = R * ‖S * Q - Q * D‖ := by
        rw [hTscale, Matrix.smul_mul, Matrix.mul_smul, ← smul_sub, norm_smul,
          Real.norm_eq_abs, abs_of_pos hR]
      _ ≤ R * (15 * rootk * u) := mul_le_mul_of_nonneg_left hScaled.le hR.le
      _ ≤ (8 * ‖T‖) * (15 * rootk * u) :=
        mul_le_mul_of_nonneg_right hRnorm.le (by positivity)
      _ ≤ _ := by nlinarith [mul_nonneg hNormT (mul_nonneg hroot_pos hu.le)]
  refine ⟨⟨hEop, hEfrob⟩, hgram, hpairs,
    fun j => ⟨hlabel j, hlabel_strict j, hmu j⟩, hStored, hScaled, hBlock, ?_, ?_⟩
  · intro j
    let q := toLp 2 (Q.col j)
    let v := toLp 2 (U.col j)
    have hEigen : M.toEuclideanLin v = a j • v := by
      apply WithLp.ofLp_injective
      funext i
      have hc := congrArg (fun A : Matrix (Fin n) (Fin k) ℝ => A i j) hUEig
      change (M * U) i j = (U * diagonal a) i j at hc
      rw [Matrix.mul_diagonal] at hc
      simpa [Matrix.toLpLin_apply, v, Matrix.mul_apply, Matrix.mulVec, dotProduct,
        Matrix.col, mul_comm] using hc
    have hqnorm : ‖q‖ ≤ 1 + 4 * u := by
      calc
        _ ≤ ‖q - v‖ + ‖v‖ := norm_le_norm_sub_add _ _
        _ ≤ _ := by rw [hunit j]; linarith [hcolumn j]
    have hqScaled : ‖S.toEuclideanLin q - mu j • q‖ < 15 * u := by
      calc
        _ ≤ (‖M‖ + |mu j|) * ‖q - v‖ + |a j - mu j| * ‖v‖ + ‖M - S‖ * ‖q‖ :=
          column_residual_le M S q v (a j) (mu j) hEigen
        _ ≤ (1 + 2) * (4 * u) + (2 * u) * 1 + u / 128 * (1 + 4 * u) := by
          have hd : |a j - mu j| ≤ 2 * u := by rw [abs_sub_comm]; exact (hlabel_strict j).le
          have hqv : ‖q - v‖ ≤ 4 * u := hcolumn j
          have hv : ‖v‖ = 1 := hunit j
          gcongr
          · exact (hmu j).le
          · exact hv.le
        _ < _ := by
          convert residual_budget hu le_rfl hu_small using 1; ring
    change ‖T.toEuclideanLin q - (R * mu j) • q‖ ≤ _
    calc
      _ = R * ‖S.toEuclideanLin q - mu j • q‖ := by
        rw [hTscale, map_smul, LinearMap.smul_apply, SemigroupAction.mul_smul, ← smul_sub, norm_smul,
          Real.norm_eq_abs, abs_of_pos hR]
      _ ≤ R * (15 * u) := mul_le_mul_of_nonneg_left hqScaled.le hR.le
      _ ≤ (8 * ‖T‖) * (15 * u) := mul_le_mul_of_nonneg_right hRnorm.le (by positivity)
      _ ≤ _ := by nlinarith [mul_nonneg hNormT hu.le]
  · intro j
    have hWeyl := HDP.Matrix.abs_hermitianOrderedEigenvalue_sub_le_operatorNorm
      M S hM hS (J j).rev
    have hInput : |mu j - hermitianOrderedEigenvalue hS (J j).rev| ≤
        eta + u * (1 + eta) + u / 128 := by
      calc
        _ ≤ |mu j - a j| + |a j - hermitianOrderedEigenvalue hS (J j).rev| :=
          abs_sub_le _ _ _
        _ ≤ _ := add_le_add (hlabel j) (hWeyl.trans hMS)
    have hInput_strict := hInput.trans_lt hsum_small
    refine ⟨hInput, hInput_strict, ?_⟩
    calc
      _ = R * |mu j - hermitianOrderedEigenvalue hS (J j).rev| := by
        rw [orderedEigenvalue_pos_smul hT hS hR hTscale, ← mul_sub, abs_mul, abs_of_pos hR]
      _ ≤ R * (2 * u) := mul_le_mul_of_nonneg_left hInput_strict.le hR.le
      _ ≤ (8 * ‖T‖) * (2 * u) := mul_le_mul_of_nonneg_right hRnorm.le (by positivity)
      _ = _ := by ring

end

end NumStability.CertifiedTridiagonalEigenpairs
