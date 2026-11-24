import ComputationalMathematics.Analysis.Eigenvalues.HermitianL1
import ComputationalMathematics.Analysis.MatrixStructure.Bipartite.ZeroMassSpectrum

/-!
# Singular-value l1 perturbation in the concrete nuclear norm

The frozen complete signed spectrum of the symmetric bipartite embedding
reduces the canonical singular-value estimate to the Hermitian l1 theorem.
The dilation nuclear bound uses two rectangular coordinate inclusions and the
shape-changing operator-ideal inequalities. No dimension factor, gap, rank,
or nonempty-dimension assumption is introduced.
-/

namespace NumStability

open scoped BigOperators
open Matrix.Bipartite

/-- Inclusion into the first contiguous coordinate block. -/
def finLeftInclusion (n : ℕ) : Matrix (Fin (n + n)) (Fin n) ℝ :=
  fun i j => Sum.elim (fun k => if k = j then 1 else 0) (fun _ => 0)
    (finSumFinEquiv.symm i)

/-- Inclusion into the second contiguous coordinate block. -/
def finRightInclusion (n : ℕ) : Matrix (Fin (n + n)) (Fin n) ℝ :=
  fun i j => Sum.elim (fun _ => 0) (fun k => if k = j then 1 else 0)
    (finSumFinEquiv.symm i)

@[simp] theorem finLeftInclusion_castAdd {n : ℕ} (i j : Fin n) :
    finLeftInclusion n (Fin.castAdd n i) j = if i = j then 1 else 0 := by
  simp [-Fin.natAdd_eq_addNat, finLeftInclusion, finSumFinEquiv_symm_apply_castAdd]

@[simp] theorem finLeftInclusion_natAdd {n : ℕ} (i j : Fin n) :
    finLeftInclusion n (Fin.natAdd n i) j = 0 := by
  simp [-Fin.natAdd_eq_addNat, finLeftInclusion, finSumFinEquiv_symm_apply_natAdd]

@[simp] theorem finRightInclusion_castAdd {n : ℕ} (i j : Fin n) :
    finRightInclusion n (Fin.castAdd n i) j = 0 := by
  simp [-Fin.natAdd_eq_addNat, finRightInclusion, finSumFinEquiv_symm_apply_castAdd]

@[simp] theorem finRightInclusion_natAdd {n : ℕ} (i j : Fin n) :
    finRightInclusion n (Fin.natAdd n i) j = if i = j then 1 else 0 := by
  simp [-Fin.natAdd_eq_addNat, finRightInclusion, finSumFinEquiv_symm_apply_natAdd]

/-- The first coordinate inclusion preserves the actual Euclidean norm. -/
theorem vecNorm2_finLeftInclusion {n : ℕ} (x : Fin n → ℝ) :
    vecNorm2 (rectMatMulVec (finLeftInclusion n) x) = vecNorm2 x := by
  unfold vecNorm2 vecNorm2Sq
  rw [Fin.sum_univ_add]
  simp [-Fin.natAdd_eq_addNat, rectMatMulVec]

/-- The second coordinate inclusion preserves the actual Euclidean norm. -/
theorem vecNorm2_finRightInclusion {n : ℕ} (x : Fin n → ℝ) :
    vecNorm2 (rectMatMulVec (finRightInclusion n) x) = vecNorm2 x := by
  unfold vecNorm2 vecNorm2Sq
  rw [Fin.sum_univ_add]
  simp [-Fin.natAdd_eq_addNat, rectMatMulVec]

/-- The first inclusion is an operator contraction, also for n=0. -/
theorem operatorNorm_finLeftInclusion_le_one (n : ℕ) :
    realMatrixOperatorNorm (finLeftInclusion n) ≤ 1 := by
  apply realMatrixOperatorNorm_le_of_rectOpNorm2Le _ (by norm_num)
  intro x
  rw [vecNorm2_finLeftInclusion, one_mul]

/-- The second inclusion is an operator contraction, also for n=0. -/
theorem operatorNorm_finRightInclusion_le_one (n : ℕ) :
    realMatrixOperatorNorm (finRightInclusion n) ≤ 1 := by
  apply realMatrixOperatorNorm_le_of_rectOpNorm2Le _ (by norm_num)
  intro x
  rw [vecNorm2_finRightInclusion, one_mul]

/-- The actual contiguous-block symmetric embedding is the sum of its two
rectangular off-diagonal embeddings. -/
theorem finEmbedding_eq_inclusions {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    finEmbedding A = finLeftInclusion n * A * (finRightInclusion n).transpose +
      finRightInclusion n * A.transpose * (finLeftInclusion n).transpose := by
  ext i j
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;>
    refine Fin.addCases (fun j => ?_) (fun j => ?_) j <;>
    simp [-Fin.natAdd_eq_addNat, finEmbedding, embedding, finSumFinEquiv_symm_apply_castAdd,
      finSumFinEquiv_symm_apply_natAdd, Matrix.mul_apply]

/-- A coordinate inclusion on each side cannot increase the nuclear norm. -/
private theorem nuclearNorm_inclusions_le {n : ℕ}
    (L R : Matrix (Fin (n + n)) (Fin n) ℝ)
    (hL : realMatrixOperatorNorm L ≤ 1) (hR : realMatrixOperatorNorm R ≤ 1)
    (A : Matrix (Fin n) (Fin n) ℝ) :
    realMatrixNuclearNorm (L * A * R.transpose) ≤ realMatrixNuclearNorm A := by
  have hi := realMatrixNuclearNorm_rectMatMul_both_le L A (finiteTranspose R)
  change realMatrixNuclearNorm (L * A * R.transpose) ≤
    realMatrixOperatorNorm L * realMatrixNuclearNorm A * realMatrixOperatorNorm (finiteTranspose R) at hi
  rw [realMatrixOperatorNorm_finiteTranspose] at hi
  calc
    _ ≤ realMatrixOperatorNorm L * realMatrixNuclearNorm A * realMatrixOperatorNorm R := hi
    _ ≤ 1 * realMatrixNuclearNorm A * 1 := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_right hL (realMatrixNuclearNorm_nonneg A)
      · exact hR
      · exact norm_nonneg _
      · exact mul_nonneg (by norm_num) (realMatrixNuclearNorm_nonneg A)
    _ = _ := by ring

/-- The symmetric embedding has nuclear norm at most twice the actual nuclear
norm, derived from rectangular ideals and transpose invariance. -/
theorem nuclearNorm_finEmbedding_le_two {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    realMatrixNuclearNorm (finEmbedding A) ≤ 2 * realMatrixNuclearNorm A := by
  rw [finEmbedding_eq_inclusions]
  have hleft := nuclearNorm_inclusions_le (finLeftInclusion n) (finRightInclusion n)
    (operatorNorm_finLeftInclusion_le_one n) (operatorNorm_finRightInclusion_le_one n) A
  have hright := nuclearNorm_inclusions_le (finRightInclusion n) (finLeftInclusion n)
    (operatorNorm_finRightInclusion_le_one n) (operatorNorm_finLeftInclusion_le_one n) A.transpose
  have ht : realMatrixNuclearNorm A.transpose = realMatrixNuclearNorm A :=
    realMatrixNuclearNorm_finiteTranspose A
  have hsum := realMatrixNuclearNorm_add_le
    (finLeftInclusion n * A * (finRightInclusion n).transpose)
    (finRightInclusion n * A.transpose * (finLeftInclusion n).transpose)
  rw [ht] at hright
  linarith

/-- Symmetric embedding respects subtraction exactly. -/
theorem finEmbedding_sub {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℝ) :
    finEmbedding (A - B) = finEmbedding A - finEmbedding B := by
  ext i j
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;>
    refine Fin.addCases (fun j => ?_) (fun j => ?_) j <;>
    simp [-Fin.natAdd_eq_addNat, finEmbedding, embedding, finSumFinEquiv_symm_apply_castAdd,
      finSumFinEquiv_symm_apply_natAdd]

/-- The full signed ascending lists have exactly twice the singular-value l1
separation. This finite identity includes repeated and zero values. -/
theorem sum_abs_sub_ascendingZeroMassValues {n : ℕ} (s t : Fin n → ℝ) :
    (∑ i, |ascendingZeroMassValues s i - ascendingZeroMassValues t i|) =
      2 * ∑ i, |s i - t i| := by
  rw [Fin.sum_univ_add]
  simp only [ascendingZeroMassValues_castAdd, ascendingZeroMassValues_natAdd, neg_sub_neg]
  have hrev : (∑ i : Fin n, |t i.rev - s i.rev|) = ∑ i : Fin n, |s i - t i| := by
    calc
      _ = ∑ i : Fin n, |s i.rev - t i.rev| := by
        apply Finset.sum_congr rfl
        intro i _
        exact abs_sub_comm _ _
      _ = _ := Equiv.sum_comp Fin.revPerm (fun i : Fin n => |s i - t i|)
  rw [hrev]
  ring

/-- The actual ordered Hermitian eigenvalue lists of the two symmetric
embeddings have exactly twice the canonical ascending singular discrepancy. -/
theorem sum_abs_sub_finEmbedding_eigenvalues {n : ℕ}
    (A B : Matrix (Fin n) (Fin n) ℝ) :
    (∑ i, |hermitianOrderedEigenvalue (finEmbedding_isHermitian A) i -
      hermitianOrderedEigenvalue (finEmbedding_isHermitian B) i|) =
      2 * ∑ i, |ascendingRealSpectrum A i - ascendingRealSpectrum B i| := by
  rw [← Equiv.sum_comp Fin.revPerm
    (fun i => |hermitianOrderedEigenvalue (finEmbedding_isHermitian A) i -
      hermitianOrderedEigenvalue (finEmbedding_isHermitian B) i|)]
  simp only [Fin.revPerm_apply, finEmbedding_orderedEigenvalue]
  exact sum_abs_sub_ascendingZeroMassValues _ _

/-- Mirsky's l1 perturbation bound for the actual complete canonical ascending
singular spectra of arbitrary real square matrices. -/
theorem sum_abs_sub_ascendingRealSpectrum_le_nuclearNorm {n : ℕ}
    (A B : Matrix (Fin n) (Fin n) ℝ) :
    (∑ i, |ascendingRealSpectrum A i - ascendingRealSpectrum B i|) ≤
      realMatrixNuclearNorm (A - B) := by
  have hherm := sum_abs_sub_hermitianOrderedEigenvalue_le_nuclearNorm
    (finEmbedding_isHermitian A) (finEmbedding_isHermitian B)
  rw [sum_abs_sub_finEmbedding_eigenvalues, ← finEmbedding_sub] at hherm
  have hdil := nuclearNorm_finEmbedding_le_two (A - B)
  linarith

end NumStability
