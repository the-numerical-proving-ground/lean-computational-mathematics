import ComputationalMathematics.Analysis.Eigenvalues.LoewnerOrder
import ComputationalMathematics.Analysis.SingularValues.InverseSVD
import ComputationalMathematics.Analysis.MatrixNorms.Nuclear.Basic
import Mathlib.Data.Real.Sign

/-!
# Hermitian l1 eigenvalue perturbation

Positive and negative parts are constructed in the actual ordered orthonormal
spectral basis. Their trace sum is the sum of absolute eigenvalues. The common
upper bound and a concrete spectral-sign dual witness give the Hermitian l1
perturbation bound in the actual nuclear norm, without gaps or rank assumptions.
-/

namespace NumStability

open scoped BigOperators RealInnerProductSpace

noncomputable section

/-- A diagonal multiplier in the actual ordered Hermitian spectral basis. -/
def hermitianSpectralMatrix {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.IsHermitian) (d : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  orthonormalBasisMatrix (hermitianOrderedEigenbasis hA) * Matrix.diagonal d *
    (orthonormalBasisMatrix (hermitianOrderedEigenbasis hA)).transpose

/-- Reconstruction using the actual ordered eigenvalues. -/
theorem hermitianSpectralMatrix_eigenvalues {n : ℕ}
    {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsHermitian) :
    hermitianSpectralMatrix hA (hermitianOrderedEigenvalue hA) = A := by
  let U := orthonormalBasisMatrix (hermitianOrderedEigenbasis hA)
  have heig : A * U = U * Matrix.diagonal (hermitianOrderedEigenvalue hA) := by
    ext i j
    have hj := congrArg (fun x : EuclideanSpace ℝ (Fin n) => x i)
      (hermitianOrderedEigenbasis_apply hA j)
    rw [Matrix.mul_diagonal]
    simpa [Matrix.toLpLin_apply, Matrix.mulVec, dotProduct, U,
      orthonormalBasisMatrix, Matrix.mul_apply, mul_comm] using hj
  change U * Matrix.diagonal (hermitianOrderedEigenvalue hA) * U.transpose = A
  rw [← heig, Matrix.mul_assoc, orthonormalBasisMatrix_mul_transpose,
    Matrix.mul_one]

theorem hermitianSpectralMatrix_sub {n : ℕ}
    {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsHermitian) (d e : Fin n → ℝ) :
    hermitianSpectralMatrix hA (d - e) =
      hermitianSpectralMatrix hA d - hermitianSpectralMatrix hA e := by
  have hdiag : Matrix.diagonal (d - e) = Matrix.diagonal d - Matrix.diagonal e := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp
    · simp [hij]
  unfold hermitianSpectralMatrix
  rw [hdiag, Matrix.mul_sub, Matrix.sub_mul]

/-- Every real diagonal multiplier in this basis is Hermitian. -/
theorem hermitianSpectralMatrix_isHermitian {n : ℕ}
    {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsHermitian) (d : Fin n → ℝ) :
    (hermitianSpectralMatrix hA d).IsHermitian := by
  simpa only [hermitianSpectralMatrix, Matrix.conjTranspose_eq_transpose_of_trivial]
    using Matrix.isHermitian_mul_mul_conjTranspose
      (orthonormalBasisMatrix (hermitianOrderedEigenbasis hA)) (Matrix.isHermitian_diagonal d)

/-- Nonnegative spectral multipliers give positive-semidefinite matrices. -/
theorem hermitianSpectralMatrix_posSemidef {n : ℕ}
    {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsHermitian) (d : Fin n → ℝ)
    (hd : ∀ i, 0 ≤ d i) : (hermitianSpectralMatrix hA d).PosSemidef := by
  have hp : (Matrix.diagonal d).PosSemidef := Matrix.PosSemidef.diagonal hd
  simpa only [hermitianSpectralMatrix, Matrix.conjTranspose_eq_transpose_of_trivial]
    using hp.mul_mul_conjTranspose_same
      (orthonormalBasisMatrix (hermitianOrderedEigenbasis hA))

/-- Orthogonal spectral conjugation preserves the diagonal trace. -/
theorem trace_hermitianSpectralMatrix {n : ℕ}
    {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsHermitian) (d : Fin n → ℝ) :
    (hermitianSpectralMatrix hA d).trace = ∑ i, d i := by
  rw [hermitianSpectralMatrix, Matrix.trace_mul_cycle,
    orthonormalBasisMatrix_transpose_mul_self, Matrix.one_mul, Matrix.trace_diagonal]

/-- Spectral multipliers multiply coordinatewise in their common actual basis. -/
theorem hermitianSpectralMatrix_mul {n : ℕ}
    {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsHermitian) (d e : Fin n → ℝ) :
    hermitianSpectralMatrix hA d * hermitianSpectralMatrix hA e =
      hermitianSpectralMatrix hA (fun i => d i * e i) := by
  unfold hermitianSpectralMatrix
  simp only [Matrix.mul_assoc, ← Matrix.mul_assoc
    (orthonormalBasisMatrix (hermitianOrderedEigenbasis hA)).transpose,
    orthonormalBasisMatrix_transpose_mul_self, Matrix.one_mul]
  rw [← Matrix.mul_assoc (Matrix.diagonal d), Matrix.diagonal_mul_diagonal]

/-- A uniform bound on the actual spectral multiplier is an operator bound. -/
theorem operatorNorm_hermitianSpectralMatrix_le {n : ℕ}
    {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsHermitian) (d : Fin n → ℝ)
    {L : ℝ} (hL : 0 ≤ L) (hd : ∀ i, |d i| ≤ L) :
    realMatrixOperatorNorm (hermitianSpectralMatrix hA d) ≤ L := by
  let U := orthonormalBasisMatrix (hermitianOrderedEigenbasis hA)
  have hU : IsOrthogonal n U := by
    constructor
    · intro i j
      have h := congrFun (congrFun
        (orthonormalBasisMatrix_transpose_mul_self (hermitianOrderedEigenbasis hA)) i) j
      simpa [U, IsLeftInverse, matTranspose, Matrix.mul_apply, Matrix.one_apply] using h
    · intro i j
      have h := congrFun (congrFun
        (orthonormalBasisMatrix_mul_transpose (hermitianOrderedEigenbasis hA)) i) j
      simpa [U, IsRightInverse, matTranspose, Matrix.mul_apply, Matrix.one_apply] using h
  have hdiag : hermitianSpectralMatrix hA d =
      finiteMatMul U (finiteMatMul (finiteDiagonal d) (matTranspose U)) := by
    change U * Matrix.diagonal d * U.transpose = U * (Matrix.diagonal d * U.transpose)
    exact Matrix.mul_assoc _ _ _
  have hf := finiteOpNorm2Le_of_isOrthogonal_diagonalization hdiag hU hL hd
  apply realMatrixOperatorNorm_le_of_rectOpNorm2Le _ hL
  intro x
  exact hf x

/-- Positive part defined from the actual ordered eigenbasis. -/
def hermitianPositivePart {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.IsHermitian) : Matrix (Fin n) (Fin n) ℝ :=
  hermitianSpectralMatrix hA (fun i => max (hermitianOrderedEigenvalue hA i) 0)

/-- Negative part defined from the same ordered eigenbasis. -/
def hermitianNegativePart {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.IsHermitian) : Matrix (Fin n) (Fin n) ℝ :=
  hermitianSpectralMatrix hA (fun i => max (-hermitianOrderedEigenvalue hA i) 0)

/-- The spectral sign vanishes on the zero eigenspace. -/
def hermitianSpectralSign {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.IsHermitian) : Matrix (Fin n) (Fin n) ℝ :=
  hermitianSpectralMatrix hA (fun i => Real.sign (hermitianOrderedEigenvalue hA i))

theorem hermitianPositivePart_posSemidef {n : ℕ}
    {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsHermitian) :
    (hermitianPositivePart hA).PosSemidef :=
  hermitianSpectralMatrix_posSemidef hA _ (fun _ => le_max_right _ _)

theorem hermitianNegativePart_posSemidef {n : ℕ}
    {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsHermitian) :
    (hermitianNegativePart hA).PosSemidef :=
  hermitianSpectralMatrix_posSemidef hA _ (fun _ => le_max_right _ _)

/-- The actual positive and negative parts reconstruct the matrix. -/
theorem hermitianPositivePart_sub_negativePart {n : ℕ}
    {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsHermitian) :
    hermitianPositivePart hA - hermitianNegativePart hA = A := by
  rw [hermitianPositivePart, hermitianNegativePart, ← hermitianSpectralMatrix_sub]
  have heq : (fun i => max (hermitianOrderedEigenvalue hA i) 0) -
      (fun i => max (-hermitianOrderedEigenvalue hA i) 0) =
      hermitianOrderedEigenvalue hA := by
    funext i
    change max (hermitianOrderedEigenvalue hA i) 0 -
      max (-hermitianOrderedEigenvalue hA i) 0 = hermitianOrderedEigenvalue hA i
    rcases le_total 0 (hermitianOrderedEigenvalue hA i) with hi | hi
    · rw [max_eq_left hi, max_eq_right (neg_nonpos.mpr hi), sub_zero]
    · rw [max_eq_right hi, max_eq_left (neg_nonneg.mpr hi)]
      ring
  rw [heq, hermitianSpectralMatrix_eigenvalues]

/-- The traces of the actual parts sum to the absolute ordered spectrum. -/
theorem trace_hermitianParts_eq_sum_abs {n : ℕ}
    {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsHermitian) :
    (hermitianPositivePart hA).trace + (hermitianNegativePart hA).trace =
      ∑ i, |hermitianOrderedEigenvalue hA i| := by
  rw [hermitianPositivePart, hermitianNegativePart, trace_hermitianSpectralMatrix,
    trace_hermitianSpectralMatrix, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rcases le_total 0 (hermitianOrderedEigenvalue hA i) with hi | hi
  · rw [max_eq_left hi, max_eq_right (neg_nonpos.mpr hi), abs_of_nonneg hi, add_zero]
  · rw [max_eq_right hi, max_eq_left (neg_nonneg.mpr hi), abs_of_nonpos hi, zero_add]

/-- Hermitian eigenvalue l1 perturbation, before nuclear norm identification. -/
theorem sum_abs_sub_hermitianOrderedEigenvalue_le_sum_abs_difference {n : ℕ}
    {A C : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsHermitian) (hC : C.IsHermitian) :
    (∑ i, |hermitianOrderedEigenvalue hA i - hermitianOrderedEigenvalue hC i|) ≤
      ∑ i, |hermitianOrderedEigenvalue (hA.sub hC) i| := by
  let hp := hermitianPositivePart (hA.sub hC)
  let hm := hermitianNegativePart (hA.sub hC)
  have hparts : hp - hm = A - C := hermitianPositivePart_sub_negativePart (hA.sub hC)
  have hpPSD : hp.PosSemidef := hermitianPositivePart_posSemidef (hA.sub hC)
  have hmPSD : hm.PosSemidef := hermitianNegativePart_posSemidef (hA.sub hC)
  have heq : C + hp = A + hm := by
    ext i j
    have h := congrFun (congrFun hparts i) j
    simp only [Matrix.sub_apply] at h
    simp only [Matrix.add_apply]
    linarith
  have hAH : (C + hp - A).PosSemidef := by
    rw [heq]
    simpa only [add_sub_cancel_left] using hmPSD
  have hCH : (C + hp - C).PosSemidef := by
    simpa only [add_sub_cancel_left] using hpPSD
  have hbound := sum_abs_sub_hermitianOrderedEigenvalue_le_trace_of_posSemidef_upper
    hA hC (hC.add hpPSD.isHermitian) hAH hCH
  have htrace : 2 * (C + hp).trace - A.trace - C.trace = hp.trace + hm.trace := by
    have heqt := congrArg Matrix.trace heq
    simp only [Matrix.trace_add] at heqt ⊢
    linarith
  rw [htrace] at hbound
  exact hbound.trans_eq (trace_hermitianParts_eq_sum_abs (hA.sub hC))


/-- The rectangular coordinate pairing is the trace of the transpose product. -/
theorem realMatrixTracePairing_eq_trace_transpose_mul {m n : ℕ}
    (W A : Matrix (Fin m) (Fin n) ℝ) :
    realMatrixTracePairing W A = (W.transpose * A).trace := by
  simp only [realMatrixTracePairing, Matrix.trace, Matrix.diag,
    Matrix.mul_apply, Matrix.transpose_apply]
  exact Finset.sum_comm

/-- Pairing two real spectral multipliers reduces to their coordinate pairing. -/
theorem realMatrixTracePairing_hermitianSpectralMatrix {n : ℕ}
    {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsHermitian) (d e : Fin n → ℝ) :
    realMatrixTracePairing (hermitianSpectralMatrix hA d) (hermitianSpectralMatrix hA e) =
      ∑ i, d i * e i := by
  have ht : (hermitianSpectralMatrix hA d).transpose = hermitianSpectralMatrix hA d := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      (hermitianSpectralMatrix_isHermitian hA d).eq
  rw [realMatrixTracePairing_eq_trace_transpose_mul, ht,
    hermitianSpectralMatrix_mul, trace_hermitianSpectralMatrix]

/-- The actual spectral sign is an operator contraction, including its zero eigenspace. -/
theorem operatorNorm_hermitianSpectralSign_le_one {n : ℕ}
    {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsHermitian) :
    realMatrixOperatorNorm (hermitianSpectralSign hA) ≤ 1 := by
  apply operatorNorm_hermitianSpectralMatrix_le hA _ (by norm_num)
  intro i
  rcases Real.sign_apply_eq (hermitianOrderedEigenvalue hA i) with hn | hz | hp
  · rw [hn]; norm_num
  · rw [hz]; norm_num
  · rw [hp]; norm_num

/-- The concrete spectral sign attains the sum of absolute ordered eigenvalues
in the trace pairing with the original matrix. -/
theorem realMatrixTracePairing_hermitianSpectralSign {n : ℕ}
    {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsHermitian) :
    realMatrixTracePairing (hermitianSpectralSign hA) A =
      ∑ i, |hermitianOrderedEigenvalue hA i| := by
  calc
    _ = realMatrixTracePairing (hermitianSpectralMatrix hA
        (fun i => Real.sign (hermitianOrderedEigenvalue hA i)))
        (hermitianSpectralMatrix hA (hermitianOrderedEigenvalue hA)) := by
      rw [hermitianSpectralMatrix_eigenvalues]
      rfl
    _ = ∑ i, Real.sign (hermitianOrderedEigenvalue hA i) *
        hermitianOrderedEigenvalue hA i :=
      realMatrixTracePairing_hermitianSpectralMatrix hA _ _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      rcases lt_trichotomy (hermitianOrderedEigenvalue hA i) 0 with hn | hz | hp
      · rw [Real.sign_of_neg hn, abs_of_neg hn, neg_one_mul]
      · rw [hz, Real.sign_zero, mul_zero, abs_zero]
      · rw [Real.sign_of_pos hp, one_mul, abs_of_pos hp]

/-- Actual rectangular trace duality bounds the absolute Hermitian spectrum by
its concrete nuclear norm, with no dimension factor. -/
theorem sum_abs_hermitianOrderedEigenvalue_le_nuclearNorm {n : ℕ}
    {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsHermitian) :
    (∑ i, |hermitianOrderedEigenvalue hA i|) ≤ realMatrixNuclearNorm A := by
  calc
    _ ≤ |realMatrixTracePairing (hermitianSpectralSign hA) A| := by
      rw [realMatrixTracePairing_hermitianSpectralSign]
      exact le_abs_self _
    _ ≤ realMatrixOperatorNorm (hermitianSpectralSign hA) * realMatrixNuclearNorm A :=
      abs_realMatrixTracePairing_le_operatorNorm_mul_nuclearNorm _ _
    _ ≤ 1 * realMatrixNuclearNorm A :=
      mul_le_mul_of_nonneg_right (operatorNorm_hermitianSpectralSign_le_one hA)
        (realMatrixNuclearNorm_nonneg A)
    _ = _ := one_mul _

/-- Hermitian l1 eigenvalue perturbation in the actual concrete nuclear norm.
All dimensions, zero eigenvalues and multiplicities are retained. -/
theorem sum_abs_sub_hermitianOrderedEigenvalue_le_nuclearNorm {n : ℕ}
    {A C : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsHermitian) (hC : C.IsHermitian) :
    (∑ i, |hermitianOrderedEigenvalue hA i - hermitianOrderedEigenvalue hC i|) ≤
      realMatrixNuclearNorm (A - C) :=
  (sum_abs_sub_hermitianOrderedEigenvalue_le_sum_abs_difference hA hC).trans
    (sum_abs_hermitianOrderedEigenvalue_le_nuclearNorm (hA.sub hC))

end
end NumStability
