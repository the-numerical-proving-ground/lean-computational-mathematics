import ComputationalMathematics.Analysis.MatrixStructure.Bipartite.MassShiftSpectrum
import ComputationalMathematics.Analysis.MatrixStructure.Bipartite.GolubKahanSpectrum

/-!
# Actual ordered eigenvalues of a positive mass shift

The existing complete orthogonal diagonalization supplies the characteristic
polynomial with all multiplicities. Sorting its roots identifies actual ordered
eigenvalues, including zero or repeated singular labels. Physical upper/lower
interleaving keeps the corresponding alternating mass signs explicit.
-/

open Matrix

namespace NumStability.Matrix.Bipartite

/-- The mass shift in two contiguous coordinate blocks, on `Fin (n+n)`.
This owns the positive-mass adapter; `finEmbedding` remains in ZeroMassSpectrum. -/
def finMassShift {n : ℕ} (C : Matrix (Fin n) (Fin n) ℝ) (α : ℝ) :
    Matrix (Fin (n + n)) (Fin (n + n)) ℝ :=
  (massShift C α).submatrix finSumFinEquiv.symm finSumFinEquiv.symm

theorem finMassShift_isHermitian {n : ℕ} (C : Matrix (Fin n) (Fin n) ℝ) (α : ℝ) :
    (finMassShift C α).IsHermitian := by
  rw [Matrix.IsHermitian, conjTranspose_eq_transpose_of_trivial]
  simp [finMassShift, transpose_submatrix]

/-- Complete characteristic-polynomial identity from the frozen full diagonalization. -/
theorem finMassShift_charpoly {n : ℕ} (C : Matrix (Fin n) (Fin n) ℝ)
    (α : ℝ) (hα : 0 < α) :
    (finMassShift C α).charpoly =
      (diagonal (ascendingMassValues α (ascendingRealSpectrum C))).charpoly := by
  obtain ⟨W, hcol, hrow, hd⟩ := exists_orthogonal_massShift_fin_ascending_diagonalization C α hα
  change finMassShift C α * W = W * diagonal (ascendingMassValues α (ascendingRealSpectrum C)) at hd
  have hA : finMassShift C α = (W * diagonal (ascendingMassValues α (ascendingRealSpectrum C))) * Wᵀ := by
    rw [← hd, Matrix.mul_assoc, hrow, Matrix.mul_one]
  rw [hA, Matrix.charpoly_mul_comm]
  simp only [← Matrix.mul_assoc, hcol, Matrix.one_mul]

/-- Actual complete ascending ordered spectrum of the positive mass shift. -/
theorem finMassShift_orderedEigenvalue {n : ℕ} (C : Matrix (Fin n) (Fin n) ℝ)
    (α : ℝ) (hα : 0 < α) (i : Fin (n + n)) :
    hermitianOrderedEigenvalue (finMassShift_isHermitian C α) i.rev =
      ascendingMassValues α (ascendingRealSpectrum C) i := by
  exact orderedEigenvalue_eq_of_charpoly_diagonal (finMassShift_isHermitian C α) _
    (ascendingMassValues_ascendingRealSpectrum_monotone C α) (finMassShift_charpoly C α hα) i

/-- Positive source rank `n+j` for one-based `j=i+1`, with zeros and repetitions retained. -/
theorem finMassShift_orderedEigenvalue_positive_index {n : ℕ}
    (C : Matrix (Fin n) (Fin n) ℝ) (α : ℝ) (hα : 0 < α) (i : Fin n) :
    hermitianOrderedEigenvalue (finMassShift_isHermitian C α) (Fin.natAdd n i).rev =
      Real.sqrt (ascendingRealSpectrum C i ^ 2 + α ^ 2) := by
  rw [finMassShift_orderedEigenvalue C α hα, ascendingMassValues_natAdd]
  simp only [massMagnitude, add_comm]

/-- Negative source rank `n-j+1`, with the same multiplicity conventions. -/
theorem finMassShift_orderedEigenvalue_negative_index {n : ℕ}
    (C : Matrix (Fin n) (Fin n) ℝ) (α : ℝ) (hα : 0 < α) (i : Fin n) :
    hermitianOrderedEigenvalue (finMassShift_isHermitian C α) (Fin.castAdd n i.rev).rev =
      -Real.sqrt (ascendingRealSpectrum C i ^ 2 + α ^ 2) := by
  rw [finMassShift_orderedEigenvalue C α hα, ascendingMassValues_castAdd, Fin.rev_rev]
  simp only [massMagnitude, add_comm]

/-- Explicit cardinality cast identifies Mathlib's decreasing ordered eigenvalues. -/
theorem finMassShift_mathlib_eigenvalues₀ {n : ℕ} (C : Matrix (Fin n) (Fin n) ℝ)
    (α : ℝ) (hα : 0 < α) (i : Fin (n + n)) :
    (finMassShift_isHermitian C α).eigenvalues₀
        (Fin.cast (Fintype.card_fin (n + n)).symm i.rev) =
      ascendingMassValues α (ascendingRealSpectrum C) i := by
  rw [eigenvalues₀_cast_eq_ordered]
  exact finMassShift_orderedEigenvalue C α hα i

/-- The mass signature as its full signed diagonal. -/
theorem massSignature_eq_diagonal (n : ℕ) (α : ℝ) :
    α • signature n = diagonal (Sum.elim (fun _ : Fin n => α) (fun _ : Fin n => -α)) := by
  ext i j
  cases i <;> cases j <;> simp [signature, Matrix.diagonal, Matrix.one_apply, mul_ite]
  split_ifs <;> simp_all

/-- Upper physical order is right,left, so its mass diagonal starts with `-α`. -/
def upperMassDiagonal (n : ℕ) (α : ℝ) : Fin (n + n) → ℝ :=
  Sum.elim (fun _ : Fin n => α) (fun _ : Fin n => -α) ∘ upperInterleaveCoord n

/-- Lower physical order is left,right, so its mass diagonal starts with `+α`. -/
def lowerMassDiagonal (n : ℕ) (α : ℝ) : Fin (n + n) → ℝ :=
  Sum.elim (fun _ : Fin n => α) (fun _ : Fin n => -α) ∘ lowerInterleaveCoord n

/-- Physical upper Golub--Kahan tridiagonal with its alternating mass diagonal. -/
def upperGolubKahanMassShift {n : ℕ} (C : Matrix (Fin n) (Fin n) ℝ) (α : ℝ) :
    Matrix (Fin (n + n)) (Fin (n + n)) ℝ :=
  upperGolubKahan C + diagonal (upperMassDiagonal n α)

/-- Physical lower Golub--Kahan tridiagonal with its alternating mass diagonal. -/
def lowerGolubKahanMassShift {n : ℕ} (C : Matrix (Fin n) (Fin n) ℝ) (α : ℝ) :
    Matrix (Fin (n + n)) (Fin (n + n)) ℝ :=
  lowerGolubKahan C + diagonal (lowerMassDiagonal n α)

/-- Upper physical mass entries alternate `-α,+α`. -/
theorem upperGolubKahanMassShift_diag {n : ℕ}
    (C : Matrix (Fin n) (Fin n) ℝ) (α : ℝ) (i : Fin n) :
    upperGolubKahanMassShift C α (interleaveIndex n (i, 0)) (interleaveIndex n (i, 0)) = -α ∧
    upperGolubKahanMassShift C α (interleaveIndex n (i, 1)) (interleaveIndex n (i, 1)) = α := by
  simp [upperGolubKahanMassShift, upperMassDiagonal, upperGolubKahan]

/-- Lower physical mass entries alternate `+α,-α`. -/
theorem lowerGolubKahanMassShift_diag {n : ℕ}
    (C : Matrix (Fin n) (Fin n) ℝ) (α : ℝ) (i : Fin n) :
    lowerGolubKahanMassShift C α (interleaveIndex n (i, 0)) (interleaveIndex n (i, 0)) = α ∧
    lowerGolubKahanMassShift C α (interleaveIndex n (i, 1)) (interleaveIndex n (i, 1)) = -α := by
  simp [lowerGolubKahanMassShift, lowerMassDiagonal, lowerGolubKahan, upperGolubKahan]

/-- Mass changes only diagonal entries, leaving every signed off-diagonal intact. -/
theorem golubKahanMassShift_offdiag {n : ℕ} (C : Matrix (Fin n) (Fin n) ℝ) (α : ℝ)
    (i j : Fin (n + n)) (hij : i ≠ j) :
    upperGolubKahanMassShift C α i j = upperGolubKahan C i j ∧
      lowerGolubKahanMassShift C α i j = lowerGolubKahan C i j := by
  simp [upperGolubKahanMassShift, lowerGolubKahanMassShift, Matrix.diagonal, hij]

/-- Exact upper physical reindexing, with its explicit signed mass diagonal. -/
theorem upperGolubKahanMassShift_eq_reindexed {n : ℕ}
    (C : Matrix (Fin n) (Fin n) ℝ) (hC : IsUpperBidiagonalSupport C) (α : ℝ) :
    upperGolubKahanMassShift C α =
      (massShift C α).submatrix (upperInterleaveCoord n) (upperInterleaveCoord n) := by
  rw [massShift, submatrix_add, massSignature_eq_diagonal]
  simp only [Pi.add_apply]
  rw [submatrix_diagonal_equiv, ← upperGolubKahan_eq_reindexed_embedding C hC]
  rfl

/-- Exact lower physical reindexing, retaining all signs and zero entries. -/
theorem lowerGolubKahanMassShift_eq_reindexed {n : ℕ}
    (C : Matrix (Fin n) (Fin n) ℝ) (hC : IsLowerBidiagonalSupport C) (α : ℝ) :
    lowerGolubKahanMassShift C α =
      (massShift C α).submatrix (lowerInterleaveCoord n) (lowerInterleaveCoord n) := by
  rw [massShift, submatrix_add, massSignature_eq_diagonal]
  simp only [Pi.add_apply]
  rw [submatrix_diagonal_equiv, ← lowerGolubKahan_eq_reindexed_embedding C hC]
  rfl

theorem upperGolubKahanMassShift_isHermitian {n : ℕ}
    (C : Matrix (Fin n) (Fin n) ℝ) (α : ℝ) : (upperGolubKahanMassShift C α).IsHermitian :=
  (upperGolubKahan_isHermitian C).add (Matrix.isHermitian_diagonal _)

theorem lowerGolubKahanMassShift_isHermitian {n : ℕ}
    (C : Matrix (Fin n) (Fin n) ℝ) (α : ℝ) : (lowerGolubKahanMassShift C α).IsHermitian :=
  (lowerGolubKahan_isHermitian C).add (Matrix.isHermitian_diagonal _)

private theorem mass_charpoly_submatrix {n : ℕ}
    (C : Matrix (Fin n) (Fin n) ℝ) (α : ℝ) (q : Fin (n + n) ≃ (Fin n ⊕ Fin n)) :
    ((massShift C α).submatrix q q).charpoly = (finMassShift C α).charpoly := by
  have hq := Matrix.charpoly_reindex q.symm (massShift C α)
  have he := Matrix.charpoly_reindex finSumFinEquiv (massShift C α)
  exact hq.trans he.symm

/-- Complete characteristic polynomial of the physical upper positive-mass matrix. -/
theorem upperGolubKahanMassShift_charpoly {n : ℕ}
    (C : Matrix (Fin n) (Fin n) ℝ) (hC : IsUpperBidiagonalSupport C)
    (α : ℝ) (hα : 0 < α) :
    (upperGolubKahanMassShift C α).charpoly =
      (diagonal (ascendingMassValues α (ascendingRealSpectrum C))).charpoly := by
  rw [upperGolubKahanMassShift_eq_reindexed C hC]
  exact (mass_charpoly_submatrix C α _).trans (finMassShift_charpoly C α hα)

/-- Complete characteristic polynomial of the physical lower positive-mass matrix. -/
theorem lowerGolubKahanMassShift_charpoly {n : ℕ}
    (C : Matrix (Fin n) (Fin n) ℝ) (hC : IsLowerBidiagonalSupport C)
    (α : ℝ) (hα : 0 < α) :
    (lowerGolubKahanMassShift C α).charpoly =
      (diagonal (ascendingMassValues α (ascendingRealSpectrum C))).charpoly := by
  rw [lowerGolubKahanMassShift_eq_reindexed C hC]
  exact (mass_charpoly_submatrix C α _).trans (finMassShift_charpoly C α hα)

/-- Every actual ascending eigenvalue of the physical upper mass shift. -/
theorem upperGolubKahanMassShift_orderedEigenvalue {n : ℕ}
    (C : Matrix (Fin n) (Fin n) ℝ) (hC : IsUpperBidiagonalSupport C)
    (α : ℝ) (hα : 0 < α) (i : Fin (n + n)) :
    hermitianOrderedEigenvalue (upperGolubKahanMassShift_isHermitian C α) i.rev =
      ascendingMassValues α (ascendingRealSpectrum C) i := by
  exact orderedEigenvalue_eq_of_charpoly_diagonal (upperGolubKahanMassShift_isHermitian C α) _
    (ascendingMassValues_ascendingRealSpectrum_monotone C α) (upperGolubKahanMassShift_charpoly C hC α hα) i

/-- Every actual ascending eigenvalue of the physical lower mass shift. -/
theorem lowerGolubKahanMassShift_orderedEigenvalue {n : ℕ}
    (C : Matrix (Fin n) (Fin n) ℝ) (hC : IsLowerBidiagonalSupport C)
    (α : ℝ) (hα : 0 < α) (i : Fin (n + n)) :
    hermitianOrderedEigenvalue (lowerGolubKahanMassShift_isHermitian C α) i.rev =
      ascendingMassValues α (ascendingRealSpectrum C) i := by
  exact orderedEigenvalue_eq_of_charpoly_diagonal (lowerGolubKahanMassShift_isHermitian C α) _
    (ascendingMassValues_ascendingRealSpectrum_monotone C α) (lowerGolubKahanMassShift_charpoly C hC α hα) i

/-- Positive prescribed upper physical rank, including zeros and repetitions. -/
theorem upperGolubKahanMassShift_positive_index {n : ℕ}
    (C : Matrix (Fin n) (Fin n) ℝ) (hC : IsUpperBidiagonalSupport C)
    (α : ℝ) (hα : 0 < α) (i : Fin n) :
    hermitianOrderedEigenvalue (upperGolubKahanMassShift_isHermitian C α) (Fin.natAdd n i).rev =
      Real.sqrt (ascendingRealSpectrum C i ^ 2 + α ^ 2) := by
  rw [upperGolubKahanMassShift_orderedEigenvalue C hC α hα, ascendingMassValues_natAdd]
  simp only [massMagnitude, add_comm]

/-- Negative prescribed upper physical partner. -/
theorem upperGolubKahanMassShift_negative_index {n : ℕ}
    (C : Matrix (Fin n) (Fin n) ℝ) (hC : IsUpperBidiagonalSupport C)
    (α : ℝ) (hα : 0 < α) (i : Fin n) :
    hermitianOrderedEigenvalue (upperGolubKahanMassShift_isHermitian C α) (Fin.castAdd n i.rev).rev =
      -Real.sqrt (ascendingRealSpectrum C i ^ 2 + α ^ 2) := by
  rw [upperGolubKahanMassShift_orderedEigenvalue C hC α hα, ascendingMassValues_castAdd, Fin.rev_rev]
  simp only [massMagnitude, add_comm]

/-- Positive prescribed lower physical rank. -/
theorem lowerGolubKahanMassShift_positive_index {n : ℕ}
    (C : Matrix (Fin n) (Fin n) ℝ) (hC : IsLowerBidiagonalSupport C)
    (α : ℝ) (hα : 0 < α) (i : Fin n) :
    hermitianOrderedEigenvalue (lowerGolubKahanMassShift_isHermitian C α) (Fin.natAdd n i).rev =
      Real.sqrt (ascendingRealSpectrum C i ^ 2 + α ^ 2) := by
  rw [lowerGolubKahanMassShift_orderedEigenvalue C hC α hα, ascendingMassValues_natAdd]
  simp only [massMagnitude, add_comm]

/-- Negative prescribed lower physical partner. -/
theorem lowerGolubKahanMassShift_negative_index {n : ℕ}
    (C : Matrix (Fin n) (Fin n) ℝ) (hC : IsLowerBidiagonalSupport C)
    (α : ℝ) (hα : 0 < α) (i : Fin n) :
    hermitianOrderedEigenvalue (lowerGolubKahanMassShift_isHermitian C α) (Fin.castAdd n i.rev).rev =
      -Real.sqrt (ascendingRealSpectrum C i ^ 2 + α ^ 2) := by
  rw [lowerGolubKahanMassShift_orderedEigenvalue C hC α hα, ascendingMassValues_castAdd, Fin.rev_rev]
  simp only [massMagnitude, add_comm]

/-- The alternating mass diagonal preserves physical tridiagonal support. -/
theorem golubKahanMassShift_far {n : ℕ} (C : Matrix (Fin n) (Fin n) ℝ) (α : ℝ)
    (i j : Fin (n + n)) (hfar : i.val + 1 < j.val ∨ j.val + 1 < i.val) :
    upperGolubKahanMassShift C α i j = 0 ∧ lowerGolubKahanMassShift C α i j = 0 := by
  have hij : i ≠ j := by intro h; subst j; omega
  rw [(golubKahanMassShift_offdiag C α i j hij).1, (golubKahanMassShift_offdiag C α i j hij).2]
  exact golubKahan_far C i j hfar

/-- Mathlib's full ordered spectrum for the upper physical mass shift. -/
theorem upperGolubKahanMassShift_mathlib_eigenvalues₀ {n : ℕ}
    (C : Matrix (Fin n) (Fin n) ℝ) (hC : IsUpperBidiagonalSupport C)
    (α : ℝ) (hα : 0 < α) (i : Fin (n + n)) :
    (upperGolubKahanMassShift_isHermitian C α).eigenvalues₀
        (Fin.cast (Fintype.card_fin (n + n)).symm i.rev) =
      ascendingMassValues α (ascendingRealSpectrum C) i := by
  rw [eigenvalues₀_cast_eq_ordered]
  exact upperGolubKahanMassShift_orderedEigenvalue C hC α hα i

/-- Mathlib's full ordered spectrum for the lower physical mass shift. -/
theorem lowerGolubKahanMassShift_mathlib_eigenvalues₀ {n : ℕ}
    (C : Matrix (Fin n) (Fin n) ℝ) (hC : IsLowerBidiagonalSupport C)
    (α : ℝ) (hα : 0 < α) (i : Fin (n + n)) :
    (lowerGolubKahanMassShift_isHermitian C α).eigenvalues₀
        (Fin.cast (Fintype.card_fin (n + n)).symm i.rev) =
      ascendingMassValues α (ascendingRealSpectrum C) i := by
  rw [eigenvalues₀_cast_eq_ordered]
  exact lowerGolubKahanMassShift_orderedEigenvalue C hC α hα i

end NumStability.Matrix.Bipartite
