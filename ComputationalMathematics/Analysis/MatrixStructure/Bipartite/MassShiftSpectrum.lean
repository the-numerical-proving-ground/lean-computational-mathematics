import ComputationalMathematics.Analysis.MatrixStructure.Bipartite.ZeroMassSpectrum
import ComputationalMathematics.Analysis.MatrixStructure.Bipartite.MassShiftDiagonalization

/-!
# Complete canonical and ascending mass-shift spectra

The canonical full SVD supplies every singular coordinate. Explicit reindexing
then puts the negative branch in reverse singular order before the positive
branch. Zero and repeated singular labels remain present with multiplicity.
-/

open Matrix

namespace NumStability.Matrix.Bipartite

/-- Full canonical sign-grouped orthogonal diagonalization for every real square matrix. -/
theorem exists_orthogonal_massShift_diagonalization {n : ℕ}
    (C : Matrix (Fin n) (Fin n) ℝ) (α : ℝ) (hα : 0 < α) :
    ∃ W : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ,
      Wᵀ * W = 1 ∧ W * Wᵀ = 1 ∧
      massShift C α * W = W * diagonal
        (signedMassValues α (ascendingRealSpectrum C)) := by
  obtain ⟨U, V, _hmono, _hnonneg, hC⟩ :=
    exists_orthonormalBases_ascendingRealSpectrum C
  exact exists_orthogonal_massShift_diagonalization_of_svd C α
    (ascendingRealSpectrum C) (orthonormalBasisMatrix U) (orthonormalBasisMatrix V) hα
    (orthonormalBasisMatrix_transpose_mul_self U)
    (orthonormalBasisMatrix_transpose_mul_self V)
    (orthonormalBasisMatrix_mul_transpose U)
    (orthonormalBasisMatrix_mul_transpose V) hC

/-- Negative mass magnitudes in reverse singular order, then positive magnitudes. -/
noncomputable def ascendingMassValues {n : ℕ} (α : ℝ) (s : Fin n → ℝ) :
    Fin (n + n) → ℝ :=
  ascendingZeroMassValues (fun i => massMagnitude α (s i))

@[simp] theorem ascendingMassValues_castAdd {n : ℕ} (α : ℝ) (s : Fin n → ℝ)
    (i : Fin n) :
    ascendingMassValues α s (Fin.castAdd n i) = -massMagnitude α (s i.rev) :=
  ascendingZeroMassValues_castAdd _ i

@[simp] theorem ascendingMassValues_natAdd {n : ℕ} (α : ℝ) (s : Fin n → ℝ)
    (i : Fin n) :
    ascendingMassValues α s (Fin.natAdd n i) = massMagnitude α (s i) :=
  ascendingZeroMassValues_natAdd _ i

theorem massMagnitude_pos {α : ℝ} (s : ℝ) (hα : 0 < α) :
    0 < massMagnitude α s := by
  exact Real.sqrt_pos.2 (add_pos_of_pos_of_nonneg (sq_pos_of_pos hα) (sq_nonneg s))

/-- Magnitudes preserve order on the nonnegative singular labels. -/
theorem massMagnitude_le_massMagnitude (α : ℝ) {s t : ℝ}
    (hs : 0 ≤ s) (hst : s ≤ t) : massMagnitude α s ≤ massMagnitude α t := by
  apply Real.sqrt_le_sqrt
  nlinarith

/-- The explicit signed list is ascending, including repeated and zero singular labels. -/
theorem ascendingMassValues_monotone {n : ℕ} (α : ℝ) (s : Fin n → ℝ)
    (hmono : Monotone s) (hnonneg : ∀ i, 0 ≤ s i) :
    Monotone (ascendingMassValues α s) :=
  ascendingZeroMassValues_monotone _
    (fun _ _ hij => massMagnitude_le_massMagnitude α (hnonneg _) (hmono hij))
    (fun _ => massMagnitude_nonneg _ _)

/-- A complete orthogonal eigenbasis with columns indexed by the ascending list.
Rows retain the original two parity sets; all `n+n` column labels are present. -/
theorem exists_orthogonal_massShift_ascending_diagonalization {n : ℕ}
    (C : Matrix (Fin n) (Fin n) ℝ) (α : ℝ) (hα : 0 < α) :
    ∃ W : Matrix (Fin n ⊕ Fin n) (Fin (n + n)) ℝ,
      Wᵀ * W = 1 ∧ W * Wᵀ = 1 ∧
      massShift C α * W = W * diagonal
        (ascendingMassValues α (ascendingRealSpectrum C)) := by
  obtain ⟨Q, hcol, hrow, hdiag⟩ := exists_orthogonal_massShift_diagonalization C α hα
  let q := ascendingZeroMassCoord n
  refine ⟨Q.submatrix id q, ?_, ?_, ?_⟩
  · change Qᵀ.submatrix q (Equiv.refl _) * Q.submatrix (Equiv.refl _) q = 1
    rw [submatrix_mul_equiv, hcol, submatrix_one_equiv]
  · change Q.submatrix id q * Qᵀ.submatrix q id = 1
    rw [submatrix_mul_equiv, hrow]
    exact submatrix_one_equiv (Equiv.refl _)
  · have h := congrArg (fun A => A.submatrix id q) hdiag
    change (massShift C α * Q).submatrix id q =
      (Q * diagonal (signedMassValues α (ascendingRealSpectrum C))).submatrix id q at h
    rw [← submatrix_mul_equiv (massShift C α) Q id (Equiv.refl _) q,
      ← submatrix_mul_equiv Q (diagonal (signedMassValues α (ascendingRealSpectrum C)))
        id q q, submatrix_diagonal_equiv] at h
    exact h

/-- Square `Fin (n+n)` transport of the complete ascending diagonalization. -/
theorem exists_orthogonal_massShift_fin_ascending_diagonalization {n : ℕ}
    (C : Matrix (Fin n) (Fin n) ℝ) (α : ℝ) (hα : 0 < α) :
    ∃ W : Matrix (Fin (n + n)) (Fin (n + n)) ℝ,
      Wᵀ * W = 1 ∧ W * Wᵀ = 1 ∧
      (massShift C α).submatrix finSumFinEquiv.symm finSumFinEquiv.symm * W =
        W * diagonal (ascendingMassValues α (ascendingRealSpectrum C)) := by
  obtain ⟨Q, hcol, hrow, hdiag⟩ :=
    exists_orthogonal_massShift_ascending_diagonalization C α hα
  let e : Fin (n + n) ≃ (Fin n ⊕ Fin n) := finSumFinEquiv.symm
  refine ⟨Q.submatrix e id, ?_, ?_, ?_⟩
  · change Qᵀ.submatrix id e * Q.submatrix e id = 1
    rw [submatrix_mul_equiv, hcol]
    exact submatrix_one_equiv (Equiv.refl _)
  · change Q.submatrix e (Equiv.refl _) * Qᵀ.submatrix (Equiv.refl _) e = 1
    rw [submatrix_mul_equiv, hrow, submatrix_one_equiv]
  · have h := congrArg (fun A => A.submatrix e id) hdiag
    change (massShift C α * Q).submatrix e id =
      (Q * diagonal (ascendingMassValues α (ascendingRealSpectrum C))).submatrix e id at h
    rw [← submatrix_mul_equiv (massShift C α) Q e e id,
      ← submatrix_mul_equiv Q (diagonal (ascendingMassValues α (ascendingRealSpectrum C)))
        e (Equiv.refl _) id] at h
    exact h

/-- The canonical signed spectrum is ascending without rank or gap assumptions. -/
theorem ascendingMassValues_ascendingRealSpectrum_monotone {n : ℕ}
    (C : Matrix (Fin n) (Fin n) ℝ) (α : ℝ) :
    Monotone (ascendingMassValues α (ascendingRealSpectrum C)) := by
  obtain ⟨_U, _V, hmono, hnonneg, _hC⟩ :=
    exists_orthonormalBases_ascendingRealSpectrum C
  exact ascendingMassValues_monotone α _ hmono hnonneg

/-- The positive label for singular index `i` occupies zero-based position `n+i`. -/
theorem ascendingMassValues_positive_index {n : ℕ} (α : ℝ) (s : Fin n → ℝ)
    (i : Fin n) :
    ascendingMassValues α s ⟨n + i.val, by omega⟩ = massMagnitude α (s i) := by
  exact ascendingMassValues_natAdd α s i

/-- The negative label for singular index `i` occupies zero-based position `n-1-i`. -/
theorem ascendingMassValues_negative_index {n : ℕ} (α : ℝ) (s : Fin n → ℝ)
    (i : Fin n) :
    ascendingMassValues α s ⟨n - 1 - i.val, by omega⟩ = -massMagnitude α (s i) := by
  have h := ascendingMassValues_castAdd α s i.rev
  have hindex : Fin.castAdd n i.rev = (⟨n - 1 - i.val, by omega⟩ : Fin (n + n)) := by
    apply Fin.ext
    simp only [Fin.val_castAdd, Fin.val_rev]
    omega
  rw [hindex, Fin.rev_rev] at h
  exact h

/-- Positive positions have strictly positive labels when the mass is positive. -/
theorem ascendingMassValues_positive {n : ℕ} {α : ℝ} (s : Fin n → ℝ)
    (hα : 0 < α) (i : Fin n) :
    0 < ascendingMassValues α s (Fin.natAdd n i) := by
  rw [ascendingMassValues_natAdd]
  exact massMagnitude_pos _ hα

/-- Negative positions have strictly negative labels when the mass is positive. -/
theorem ascendingMassValues_negative {n : ℕ} {α : ℝ} (s : Fin n → ℝ)
    (hα : 0 < α) (i : Fin n) :
    ascendingMassValues α s (Fin.castAdd n i) < 0 := by
  rw [ascendingMassValues_castAdd]
  exact neg_neg_of_pos (massMagnitude_pos _ hα)

end NumStability.Matrix.Bipartite
