import ComputationalMathematics.Analysis.MatrixStructure.Bipartite.MassShift
import ComputationalMathematics.Analysis.SingularValues.FullRealSVD.Basic
import Mathlib.Analysis.Matrix.Spectrum
import ComputationalMathematics.Analysis.Eigenvalues.CourantFischer
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-!
# Complete ascending spectrum of the unshifted symmetric embedding

A full SVD and the constant `1 / sqrt 2` Hadamard mixing provide a complete
orthogonal eigenbasis, even at zero singular values. No positive-mass
normalization or division by a singular value is used.
-/

open Matrix

namespace NumStability.Matrix.Bipartite

/-- Constant Hadamard mixing of the two complete singular bases. -/
noncomputable def zeroMassEigenbasis {n : ℕ} (U V : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ :=
  (Real.sqrt 2)⁻¹ • fromBlocks U U V (-V)

private theorem sqrt_two_inv_mul_self :
    (Real.sqrt 2)⁻¹ * (Real.sqrt 2)⁻¹ = (1 / 2 : ℝ) := by
  have hs : Real.sqrt 2 ^ 2 = (2 : ℝ) := Real.sq_sqrt (by norm_num)
  have hn : Real.sqrt 2 ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  field_simp
  nlinarith

/-- Column orthogonality of the full Hadamard eigenbasis. -/
theorem zeroMassEigenbasis_transpose_mul {n : ℕ}
    (U V : Matrix (Fin n) (Fin n) ℝ) (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1) :
    (zeroMassEigenbasis U V)ᵀ * zeroMassEigenbasis U V = 1 := by
  simp only [zeroMassEigenbasis, transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    sqrt_two_inv_mul_self, fromBlocks_transpose, transpose_neg, fromBlocks_multiply,
    hU, hV, mul_neg, neg_mul, neg_neg]
  ext i j
  cases i <;> cases j <;> simp [Matrix.one_apply] <;> ring

/-- Row orthogonality of the full Hadamard eigenbasis. -/
theorem zeroMassEigenbasis_mul_transpose {n : ℕ}
    (U V : Matrix (Fin n) (Fin n) ℝ) (hU : U * Uᵀ = 1) (hV : V * Vᵀ = 1) :
    zeroMassEigenbasis U V * (zeroMassEigenbasis U V)ᵀ = 1 := by
  simp only [zeroMassEigenbasis, transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    sqrt_two_inv_mul_self, fromBlocks_transpose, transpose_neg, fromBlocks_multiply,
    hU, hV, mul_neg, neg_mul, neg_neg]
  ext i j
  cases i <;> cases j <;> simp [Matrix.one_apply] <;> ring

/-- All signed eigenvector equations at once, for supplied compatible full SVD factors. -/
theorem embedding_mul_zeroMassEigenbasis_of_svd {n : ℕ}
    (C : Matrix (Fin n) (Fin n) ℝ) (s : Fin n → ℝ)
    (U V : Matrix (Fin n) (Fin n) ℝ)
    (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1)
    (hC : C = U * diagonal s * Vᵀ) :
    embedding C * zeroMassEigenbasis U V =
      zeroMassEigenbasis U V * diagonal (Sum.elim s (fun i => -s i)) := by
  have hCV : C * V = U * diagonal s := by
    rw [hC]
    simp only [Matrix.mul_assoc, hV, Matrix.mul_one]
  have hCU : Cᵀ * U = V * diagonal s := by
    rw [hC, transpose_mul, transpose_mul, transpose_transpose, diagonal_transpose]
    simp only [Matrix.mul_assoc, hU, Matrix.mul_one]
  rw [← fromBlocks_diagonal]
  simp [embedding, zeroMassEigenbasis,
    fromBlocks_multiply, hCV, hCU, ← diagonal_neg]

/-- Canonical complete signed singular spectrum of the unshifted embedding. -/
theorem exists_orthogonal_embedding_diagonalization {n : ℕ}
    (C : Matrix (Fin n) (Fin n) ℝ) :
    ∃ W : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ,
      Wᵀ * W = 1 ∧ W * Wᵀ = 1 ∧
      embedding C * W = W * diagonal
        (Sum.elim (ascendingRealSpectrum C) (fun i => -ascendingRealSpectrum C i)) := by
  obtain ⟨U, V, _hm, _hn, hC⟩ := exists_orthonormalBases_ascendingRealSpectrum C
  refine ⟨zeroMassEigenbasis (orthonormalBasisMatrix U) (orthonormalBasisMatrix V), ?_, ?_, ?_⟩
  · exact zeroMassEigenbasis_transpose_mul _ _
      (orthonormalBasisMatrix_transpose_mul_self U) (orthonormalBasisMatrix_transpose_mul_self V)
  · exact zeroMassEigenbasis_mul_transpose _ _
      (orthonormalBasisMatrix_mul_transpose U) (orthonormalBasisMatrix_mul_transpose V)
  · exact embedding_mul_zeroMassEigenbasis_of_svd C _ _ _
      (orthonormalBasisMatrix_transpose_mul_self U) (orthonormalBasisMatrix_transpose_mul_self V) hC

/-- Ascending signed coordinates in the original positive/negative column slots. -/
def ascendingZeroMassCoord (n : ℕ) : Fin (n + n) ≃ (Fin n ⊕ Fin n) :=
  finSumFinEquiv.symm.trans
    ((Equiv.sumCongr Fin.revPerm (Equiv.refl (Fin n))).trans (Equiv.sumComm _ _))

/-- Full ascending signed list: reversed negatives followed by ascending positives. -/
def ascendingZeroMassValues {n : ℕ} (s : Fin n → ℝ) : Fin (n + n) → ℝ :=
  Sum.elim s (fun i => -s i) ∘ ascendingZeroMassCoord n

@[simp] theorem ascendingZeroMassCoord_castAdd {n : ℕ} (i : Fin n) :
    ascendingZeroMassCoord n (Fin.castAdd n i) = Sum.inr i.rev := by
  simp [ascendingZeroMassCoord]

@[simp] theorem ascendingZeroMassCoord_natAdd {n : ℕ} (i : Fin n) :
    ascendingZeroMassCoord n (Fin.natAdd n i) = Sum.inl i := by
  change (Equiv.sumComm _ _) ((Equiv.sumCongr Fin.revPerm (Equiv.refl (Fin n)))
    (finSumFinEquiv.symm (Fin.natAdd n i))) = _
  rw [finSumFinEquiv_symm_apply_natAdd]
  rfl

@[simp] theorem ascendingZeroMassValues_castAdd {n : ℕ} (s : Fin n → ℝ) (i : Fin n) :
    ascendingZeroMassValues s (Fin.castAdd n i) = -s i.rev := by
  change Sum.elim s (fun i => -s i) (ascendingZeroMassCoord n _) = _
  rw [ascendingZeroMassCoord_castAdd]
  rfl

@[simp] theorem ascendingZeroMassValues_natAdd {n : ℕ} (s : Fin n → ℝ) (i : Fin n) :
    ascendingZeroMassValues s (Fin.natAdd n i) = s i := by
  change Sum.elim s (fun i => -s i) (ascendingZeroMassCoord n _) = _
  rw [ascendingZeroMassCoord_natAdd]
  rfl

/-- Sorting uses weak order throughout, so repeated labels and zeros are retained. -/
theorem ascendingZeroMassValues_monotone {n : ℕ} (s : Fin n → ℝ)
    (hmono : Monotone s) (hnonneg : ∀ i, 0 ≤ s i) :
    Monotone (ascendingZeroMassValues s) := by
  intro i j
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;>
    refine Fin.addCases (fun j => ?_) (fun j => ?_) j <;> intro hij
  · simp only [ascendingZeroMassValues_castAdd]
    exact neg_le_neg (hmono (Fin.rev_anti hij))
  · simp only [ascendingZeroMassValues_castAdd, ascendingZeroMassValues_natAdd]
    exact le_trans (neg_nonpos.mpr (hnonneg _)) (hnonneg _)
  · have hi := i.isLt
    have hj := j.isLt
    simp only [Fin.le_def, Fin.val_natAdd, Fin.val_castAdd] at hij
    omega
  · simp only [ascendingZeroMassValues_natAdd]
    apply hmono
    simpa only [Fin.le_def, Fin.val_natAdd, Nat.add_le_add_iff_left] using hij

/-- The exact zero-based positive singular rank is `n+i`. -/
theorem ascendingZeroMassValues_positive_index {n : ℕ} (s : Fin n → ℝ) (i : Fin n) :
    ascendingZeroMassValues s ⟨n + i.val, by omega⟩ = s i := by
  exact ascendingZeroMassValues_natAdd s i

/-- The exact zero-based negative singular rank is `n-1-i`. -/
theorem ascendingZeroMassValues_negative_index {n : ℕ} (s : Fin n → ℝ) (i : Fin n) :
    ascendingZeroMassValues s ⟨n - 1 - i.val, by omega⟩ = -s i := by
  have h := ascendingZeroMassValues_castAdd s i.rev
  have hindex : Fin.castAdd n i.rev = (⟨n - 1 - i.val, by omega⟩ : Fin (n + n)) := by
    apply Fin.ext
    simp only [Fin.val_castAdd, Fin.val_rev]
    omega
  rw [hindex, Fin.rev_rev] at h
  exact h

/-- The embedding in two contiguous `Fin n` coordinate blocks, reindexed to `Fin (n+n)`. -/
def finEmbedding {n : ℕ} (C : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin (n + n)) (Fin (n + n)) ℝ :=
  (embedding C).submatrix finSumFinEquiv.symm finSumFinEquiv.symm

/-- A complete square orthogonal diagonalization in ascending signed order. -/
theorem exists_orthogonal_finEmbedding_ascending_diagonalization {n : ℕ}
    (C : Matrix (Fin n) (Fin n) ℝ) :
    ∃ W : Matrix (Fin (n + n)) (Fin (n + n)) ℝ,
      Wᵀ * W = 1 ∧ W * Wᵀ = 1 ∧
      finEmbedding C * W = W * diagonal (ascendingZeroMassValues (ascendingRealSpectrum C)) := by
  obtain ⟨Q, hcol, hrow, hdiag⟩ := exists_orthogonal_embedding_diagonalization C
  let e : Fin (n + n) ≃ (Fin n ⊕ Fin n) := finSumFinEquiv.symm
  let q := ascendingZeroMassCoord n
  refine ⟨Q.submatrix e q, ?_, ?_, ?_⟩
  · change Qᵀ.submatrix q e * Q.submatrix e q = 1
    rw [submatrix_mul_equiv, hcol, submatrix_one_equiv]
  · change Q.submatrix e q * Qᵀ.submatrix q e = 1
    rw [submatrix_mul_equiv, hrow, submatrix_one_equiv]
  · have h := congrArg (fun A => A.submatrix e q) hdiag
    change (embedding C * Q).submatrix e q =
      (Q * diagonal (Sum.elim (ascendingRealSpectrum C) (fun i => -ascendingRealSpectrum C i))).submatrix e q at h
    rw [← submatrix_mul_equiv (embedding C) Q e e q,
      ← submatrix_mul_equiv Q (diagonal (Sum.elim (ascendingRealSpectrum C)
        (fun i => -ascendingRealSpectrum C i))) e q q, submatrix_diagonal_equiv] at h
    exact h

/-- Canonical signed singular labels are ascending, with all zero multiplicities. -/
theorem ascendingZeroMassValues_ascendingRealSpectrum_monotone {n : ℕ}
    (C : Matrix (Fin n) (Fin n) ℝ) :
    Monotone (ascendingZeroMassValues (ascendingRealSpectrum C)) := by
  obtain ⟨_U, _V, hm, hn, _hC⟩ := exists_orthonormalBases_ascendingRealSpectrum C
  exact ascendingZeroMassValues_monotone _ hm hn

/-- The contiguous-block embedding is a real Hermitian matrix. -/
theorem finEmbedding_isHermitian {n : ℕ} (C : Matrix (Fin n) (Fin n) ℝ) :
    (finEmbedding C).IsHermitian := by
  rw [Matrix.IsHermitian]
  rw [conjTranspose_eq_transpose_of_trivial]
  simp [finEmbedding, transpose_submatrix]

/-- Complete diagonalization identifies the characteristic polynomial, not only the eigenvalue set. -/
theorem finEmbedding_charpoly {n : ℕ} (C : Matrix (Fin n) (Fin n) ℝ) :
    (finEmbedding C).charpoly =
      (diagonal (ascendingZeroMassValues (ascendingRealSpectrum C))).charpoly := by
  obtain ⟨W, hcol, hrow, hd⟩ := exists_orthogonal_finEmbedding_ascending_diagonalization C
  have hA : finEmbedding C = (W * diagonal (ascendingZeroMassValues (ascendingRealSpectrum C))) * Wᵀ := by
    rw [← hd, Matrix.mul_assoc, hrow, Matrix.mul_one]
  rw [hA, Matrix.charpoly_mul_comm]
  simp only [← Matrix.mul_assoc, hcol, Matrix.one_mul]

private theorem eigenvalues₀_cast_eq_ordered {m : ℕ}
    {A : Matrix (Fin m) (Fin m) ℝ} (hA : A.IsHermitian) (i : Fin m) :
    hA.eigenvalues₀ (Fin.cast (Fintype.card_fin m).symm i) =
      hermitianOrderedEigenvalue hA i := by
  let hS := Matrix.isHermitian_iff_isSymmetric.mp hA
  have hcast {a b : ℕ}
      (ha : Module.finrank ℝ (EuclideanSpace ℝ (Fin m)) = a)
      (hb : Module.finrank ℝ (EuclideanSpace ℝ (Fin m)) = b)
      (hab : a = b) (j : Fin b) :
      hS.eigenvalues ha (Fin.cast hab.symm j) = hS.eigenvalues hb j := by
    cases hab
    simp only [Fin.cast_refl]
    rfl
  exact hcast finrank_euclideanSpace finrank_euclideanSpace_fin (Fintype.card_fin m) i

/-- Ordered-eigenvalue uniqueness for an ascending complete diagonal list. -/
private theorem orderedEigenvalue_eq_of_charpoly_diagonal {m : ℕ}
    {A : Matrix (Fin m) (Fin m) ℝ} (hA : A.IsHermitian) (d : Fin m → ℝ)
    (hd : Monotone d) (hc : A.charpoly = (diagonal d).charpoly) (i : Fin m) :
    hermitianOrderedEigenvalue hA i.rev = d i := by
  have hroots : A.charpoly.roots = Multiset.map d Finset.univ.val := by
    rw [hc, charpoly_diagonal, Polynomial.roots_prod]
    · simp
    · simp [Finset.prod_ne_zero_iff, Polynomial.X_sub_C_ne_zero]
  have hrev : Multiset.map d Finset.univ.val =
      Multiset.map (fun j : Fin m => d j.rev) Finset.univ.val := by
    calc
      _ = Multiset.map d (Multiset.map (Fin.revPerm : Equiv.Perm (Fin m)) Finset.univ.val) := by
        rw [Multiset.map_univ_val_equiv]
      _ = _ := by rw [Multiset.map_map]; rfl
  have hsort : (A.charpoly.roots.map RCLike.re).sort (· ≥ ·) =
      List.ofFn (hermitianOrderedEigenvalue hA) := by
    have h := hA.sort_roots_charpoly_eq_eigenvalues₀
    rw [List.ofFn_congr (Fintype.card_fin m)] at h
    convert h using 2
    funext j
    exact (eigenvalues₀_cast_eq_ordered hA j).symm
  rw [hroots] at hsort
  simp only [Multiset.map_map, RCLike.re_to_real, Function.comp_def] at hsort
  rw [hrev, Fin.univ_val_map, Multiset.coe_sort] at hsort
  have hanti : Antitone (fun j : Fin m => d j.rev) := fun _ _ h => hd (Fin.rev_anti h)
  have hmerge : (List.ofFn (fun j : Fin m => d j.rev)).mergeSort (fun a b => decide (a ≥ b)) =
      List.ofFn (fun j : Fin m => d j.rev) := by
    apply List.mergeSort_of_pairwise
    simp only [decide_eq_true_eq, ← List.sortedGE_iff_pairwise]
    exact hanti.sortedGE_ofFn
  rw [hmerge] at hsort
  have hf := List.ofFn_inj.mp hsort
  have hi := congrFun hf i.rev
  simpa only [Fin.rev_rev] using hi.symm

/-- Actual ordered eigenvalues of the embedding equal the complete ascending signed list. -/
theorem finEmbedding_orderedEigenvalue {n : ℕ} (C : Matrix (Fin n) (Fin n) ℝ)
    (i : Fin (n + n)) :
    hermitianOrderedEigenvalue (finEmbedding_isHermitian C) i.rev =
      ascendingZeroMassValues (ascendingRealSpectrum C) i := by
  exact orderedEigenvalue_eq_of_charpoly_diagonal (finEmbedding_isHermitian C) _
    (ascendingZeroMassValues_ascendingRealSpectrum_monotone C) (finEmbedding_charpoly C) i

/-- Source rank `n+j` for one-based `j=i+1`, including zero and repeated singular values. -/
theorem finEmbedding_orderedEigenvalue_positive_index {n : ℕ}
    (C : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) :
    hermitianOrderedEigenvalue (finEmbedding_isHermitian C) (Fin.natAdd n i).rev =
      ascendingRealSpectrum C i := by
  rw [finEmbedding_orderedEigenvalue, ascendingZeroMassValues_natAdd]

/-- The same identity for Mathlib's cardinality-indexed decreasing eigenvalues. -/
theorem finEmbedding_mathlib_eigenvalues₀ {n : ℕ} (C : Matrix (Fin n) (Fin n) ℝ)
    (i : Fin (n + n)) :
    (finEmbedding_isHermitian C).eigenvalues₀
        (Fin.cast (Fintype.card_fin (n + n)).symm i.rev) =
      ascendingZeroMassValues (ascendingRealSpectrum C) i := by
  rw [eigenvalues₀_cast_eq_ordered]
  exact finEmbedding_orderedEigenvalue C i

/-- The negative singular partner has zero-based ascending rank `n-1-i`. -/
theorem finEmbedding_orderedEigenvalue_negative_index {n : ℕ}
    (C : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) :
    hermitianOrderedEigenvalue (finEmbedding_isHermitian C) (Fin.castAdd n i.rev).rev =
      -ascendingRealSpectrum C i := by
  rw [finEmbedding_orderedEigenvalue, ascendingZeroMassValues_castAdd, Fin.rev_rev]

end NumStability.Matrix.Bipartite
