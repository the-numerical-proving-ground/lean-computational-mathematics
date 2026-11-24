import ComputationalMathematics.Analysis.MatrixStructure.Bipartite.MassShiftSVD
import Mathlib.Tactic.FieldSimp

/-!
# A complete sign-grouped orthogonal diagonalization of a mass shift

The two-coordinate basis is normalized by a positive norm, never by a singular
label. The full construction uses supplied orthogonal singular factors and
retains every label, including zero and repeated labels.
-/

open Matrix

namespace NumStability.Matrix.Bipartite

/-- Common positive normalization for both explicit two-coordinate eigenvectors. -/
noncomputable def massVectorNorm (α s : ℝ) : ℝ :=
  Real.sqrt ((massMagnitude α s + α) ^ 2 + s ^ 2)

/-- The normalized two-coordinate eigenvectors, with the positive column first. -/
noncomputable def massEigenbasis (α s : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![(massMagnitude α s + α) / massVectorNorm α s, -s / massVectorNorm α s;
    s / massVectorNorm α s, (massMagnitude α s + α) / massVectorNorm α s]

theorem massVectorNorm_pos {α : ℝ} (s : ℝ) (hα : 0 < α) :
    0 < massVectorNorm α s := by
  apply Real.sqrt_pos.2
  have hb : 0 < massMagnitude α s + α := add_pos_of_nonneg_of_pos
    (massMagnitude_nonneg α s) hα
  exact add_pos_of_pos_of_nonneg (sq_pos_of_pos hb) (sq_nonneg s)

theorem massVectorNorm_sq (α s : ℝ) :
    massVectorNorm α s ^ 2 = (massMagnitude α s + α) ^ 2 + s ^ 2 := by
  exact Real.sq_sqrt (add_nonneg (sq_nonneg _) (sq_nonneg _))

/-- The normalized positive/negative columns form an orthogonal two-coordinate matrix. -/
theorem massEigenbasis_transpose_mul {α : ℝ} (s : ℝ) (hα : 0 < α) :
    (massEigenbasis α s)ᵀ * massEigenbasis α s = 1 := by
  have hd : massVectorNorm α s ≠ 0 := ne_of_gt (massVectorNorm_pos s hα)
  have hs := massVectorNorm_sq α s
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [massEigenbasis, Matrix.mul_apply, Fin.sum_univ_succ] <;>
    field_simp <;> nlinarith

/-- The same normalized matrix is also orthogonal on rows. -/
theorem massEigenbasis_mul_transpose {α : ℝ} (s : ℝ) (hα : 0 < α) :
    massEigenbasis α s * (massEigenbasis α s)ᵀ = 1 := by
  have hd : massVectorNorm α s ≠ 0 := ne_of_gt (massVectorNorm_pos s hα)
  have hs := massVectorNorm_sq α s
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [massEigenbasis, Matrix.mul_apply, Fin.sum_univ_succ] <;>
    field_simp <;> nlinarith

/-- The normalized matrix gives both signed eigenvalues simultaneously. -/
theorem massBlock_mul_massEigenbasis {α : ℝ} (s : ℝ) (hα : 0 < α) :
    massBlock α s * massEigenbasis α s =
      massEigenbasis α s * diagonal ![massMagnitude α s, -massMagnitude α s] := by
  have hd : massVectorNorm α s ≠ 0 := ne_of_gt (massVectorNorm_pos s hα)
  have hs := massMagnitude_sq α s
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [massBlock, massEigenbasis, Matrix.mul_apply, Fin.sum_univ_succ] <;>
    field_simp <;> nlinarith

/-- The full sign-grouped list retains one positive and one negative label per index. -/
noncomputable def signedMassValues {n : ℕ} (α : ℝ) (s : Fin n → ℝ) :
    Fin n ⊕ Fin n → ℝ :=
  Sum.elim (fun i => massMagnitude α (s i)) (fun i => -massMagnitude α (s i))

/-- Assemble the two-coordinate bases and transport back to parity coordinates. -/
noncomputable def pairedMassEigenbasis {n : ℕ} (α : ℝ) (s : Fin n → ℝ) :
    Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ :=
  (blockDiagonal (fun i : Fin n => massEigenbasis α (s i))).submatrix
    (pairCoord n).symm (pairCoord n).symm

/-- Pairing the sign-grouped diagonal gives the local signed diagonals. -/
theorem signedMassValues_pairing {n : ℕ} (α : ℝ) (s : Fin n → ℝ) :
    (diagonal (signedMassValues α s)).submatrix (pairCoord n) (pairCoord n) =
      blockDiagonal (fun i : Fin n => diagonal ![massMagnitude α (s i), -massMagnitude α (s i)]) := by
  rw [submatrix_diagonal_equiv, blockDiagonal_diagonal]
  congr 1
  funext ⟨a, i⟩
  fin_cases a <;> simp [signedMassValues]

/-- Column orthogonality survives assembly and exact coordinate transport. -/
theorem pairedMassEigenbasis_transpose_mul {n : ℕ} (α : ℝ) (s : Fin n → ℝ)
    (hα : 0 < α) :
    (pairedMassEigenbasis α s)ᵀ * pairedMassEigenbasis α s = 1 := by
  have hlocal : (fun i : Fin n => (massEigenbasis α (s i))ᵀ * massEigenbasis α (s i)) =
      fun _ => (1 : Matrix (Fin 2) (Fin 2) ℝ) :=
    funext fun i => massEigenbasis_transpose_mul (s i) hα
  simp only [pairedMassEigenbasis, transpose_submatrix, submatrix_mul_equiv,
    blockDiagonal_transpose, ← blockDiagonal_mul, hlocal]
  change (blockDiagonal (1 : Fin n → Matrix (Fin 2) (Fin 2) ℝ)).submatrix
    (pairCoord n).symm (pairCoord n).symm = 1
  rw [blockDiagonal_one, submatrix_one_equiv]

/-- Row orthogonality survives assembly and exact coordinate transport. -/
theorem pairedMassEigenbasis_mul_transpose {n : ℕ} (α : ℝ) (s : Fin n → ℝ)
    (hα : 0 < α) :
    pairedMassEigenbasis α s * (pairedMassEigenbasis α s)ᵀ = 1 := by
  have hlocal : (fun i : Fin n => massEigenbasis α (s i) * (massEigenbasis α (s i))ᵀ) =
      fun _ => (1 : Matrix (Fin 2) (Fin 2) ℝ) :=
    funext fun i => massEigenbasis_mul_transpose (s i) hα
  simp only [pairedMassEigenbasis, transpose_submatrix, submatrix_mul_equiv,
    blockDiagonal_transpose, ← blockDiagonal_mul, hlocal]
  change (blockDiagonal (1 : Fin n → Matrix (Fin 2) (Fin 2) ℝ)).submatrix
    (pairCoord n).symm (pairCoord n).symm = 1
  rw [blockDiagonal_one, submatrix_one_equiv]

/-- The assembled bases diagonalize the mass shift of the supplied diagonal. -/
theorem massShift_diagonal_mul_pairedMassEigenbasis {n : ℕ} (α : ℝ) (s : Fin n → ℝ)
    (hα : 0 < α) :
    massShift (diagonal s) α * pairedMassEigenbasis α s =
      pairedMassEigenbasis α s * diagonal (signedMassValues α s) := by
  let L := blockDiagonal (fun i : Fin n => massBlock α (s i))
  let R := blockDiagonal (fun i : Fin n => massEigenbasis α (s i))
  let D := blockDiagonal (fun i : Fin n =>
    diagonal ![massMagnitude α (s i), -massMagnitude α (s i)])
  have hlocal : L * R = R * D := by
    dsimp only [L, R, D]
    rw [← blockDiagonal_mul, ← blockDiagonal_mul]
    congr 1
    funext i
    exact massBlock_mul_massEigenbasis (s i) hα
  have hL : L.submatrix (pairCoord n).symm (pairCoord n).symm = massShift (diagonal s) α := by
    dsimp only [L]
    rw [← massShift_diagonal_pairing]
    simp
  have hD : D.submatrix (pairCoord n).symm (pairCoord n).symm =
      diagonal (signedMassValues α s) := by
    dsimp only [D]
    rw [← signedMassValues_pairing]
    simp
  have h := congrArg (fun A => A.submatrix (pairCoord n).symm (pairCoord n).symm) hlocal
  change (L * R).submatrix (pairCoord n).symm (pairCoord n).symm =
    (R * D).submatrix (pairCoord n).symm (pairCoord n).symm at h
  rw [← submatrix_mul_equiv L R (pairCoord n).symm (pairCoord n).symm (pairCoord n).symm,
    ← submatrix_mul_equiv R D (pairCoord n).symm (pairCoord n).symm (pairCoord n).symm,
    hL, hD] at h
  exact h

/-- A full orthogonal diagonalization with sign-grouped labels, from supplied full
orthogonal singular factors. It includes zero and repeated labels. -/
theorem exists_orthogonal_massShift_diagonalization_of_svd {n : ℕ}
    (C : Matrix (Fin n) (Fin n) ℝ) (α : ℝ) (s : Fin n → ℝ)
    (U V : Matrix (Fin n) (Fin n) ℝ) (hα : 0 < α)
    (hUcol : Uᵀ * U = 1) (hVcol : Vᵀ * V = 1)
    (hUrow : U * Uᵀ = 1) (hVrow : V * Vᵀ = 1)
    (hC : C = U * diagonal s * Vᵀ) :
    ∃ W : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ,
      Wᵀ * W = 1 ∧ W * Wᵀ = 1 ∧
      massShift C α * W = W * diagonal
        (Sum.elim (fun i => massMagnitude α (s i)) (fun i => -massMagnitude α (s i))) := by
  let P := parityBasis U V
  let R := pairedMassEigenbasis α s
  have hPcol : Pᵀ * P = 1 := parityBasis_transpose_mul U V hUcol hVcol
  have hProw : P * Pᵀ = 1 := parityBasis_mul_transpose U V hUrow hVrow
  have hRcol : Rᵀ * R = 1 := pairedMassEigenbasis_transpose_mul α s hα
  have hRrow : R * Rᵀ = 1 := pairedMassEigenbasis_mul_transpose α s hα
  have hTP : massShift C α * P = P * massShift (diagonal s) α := by
    calc
      _ = (P * Pᵀ) * (massShift C α * P) := by rw [hProw, Matrix.one_mul]
      _ = P * (Pᵀ * massShift C α * P) := by simp only [Matrix.mul_assoc]
      _ = P * massShift (diagonal s) α := by
        rw [massShift_conjugate_of_svd C α s U V hUcol hVcol hC]
  refine ⟨P * R, ?_, ?_, ?_⟩
  · calc
      _ = Rᵀ * (Pᵀ * P) * R := by simp only [transpose_mul, Matrix.mul_assoc]
      _ = 1 := by rw [hPcol, Matrix.mul_one, hRcol]
  · calc
      _ = P * (R * Rᵀ) * Pᵀ := by simp only [transpose_mul, Matrix.mul_assoc]
      _ = 1 := by rw [hRrow, Matrix.mul_one, hProw]
  · change massShift C α * (P * R) = (P * R) * diagonal (signedMassValues α s)
    calc
      _ = P * (massShift (diagonal s) α * R) := by rw [← Matrix.mul_assoc, hTP, Matrix.mul_assoc]
      _ = P * (R * diagonal (signedMassValues α s)) := by
        rw [massShift_diagonal_mul_pairedMassEigenbasis α s hα]
      _ = _ := by rw [Matrix.mul_assoc]

end NumStability.Matrix.Bipartite
