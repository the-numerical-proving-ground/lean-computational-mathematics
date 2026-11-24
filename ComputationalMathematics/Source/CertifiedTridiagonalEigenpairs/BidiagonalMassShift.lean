import ComputationalMathematics.Analysis.MatrixStructure.Bipartite.MassShiftOrderedEigenvalues
import ComputationalMathematics.Analysis.FloatingPointArithmetic.UnboundedBinary.Basic
import ComputationalMathematics.Analysis.Eigenvalues.HermitianL1

/-!
# The exact tridiagonal input for the bidiagonal SVD construction

The physical orientation is `true` for upper bidiagonal inputs and `false` for
lower bidiagonal inputs. The same signed off-diagonal words are used before and
after the mass shift. Only the diagonal words gain the signed mass.
-/

open Matrix NumStability.Matrix.Bipartite
open NumStability.FloatingPointFormat.UnboundedBinary
open scoped Matrix.Norms.L2Operator

namespace NumStability.CertifiedTridiagonalEigenpairs

/-- The bidiagonal support used for the physical orientation. -/
def bidiagonalSupport {n : ℕ} (upper : Bool) (C : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  if upper then IsUpperBidiagonalSupport C else IsLowerBidiagonalSupport C

/-- Physical position to original left/right coordinate. -/
def bidiagonalParityCoord (upper : Bool) (n : ℕ) : Fin (n + n) ≃ (Fin n ⊕ Fin n) :=
  if upper then upperInterleaveCoord n else lowerInterleaveCoord n

/-- The interleaved parity signature, with the original left sign `+1`. -/
def bidiagonalParitySignature (upper : Bool) (n : ℕ) :
    Matrix (Fin (n + n)) (Fin (n + n)) ℝ :=
  (signature n).submatrix (bidiagonalParityCoord upper n) (bidiagonalParityCoord upper n)

/-- The upper orientation interleaves right then left, and the lower orientation left then right. -/
theorem bidiagonalParityCoord_even_odd {n : ℕ} (upper : Bool) (i : Fin n) :
    (bidiagonalParityCoord upper n (interleaveIndex n (i, 0))) =
        (if upper then Sum.inr i else Sum.inl i) ∧
    (bidiagonalParityCoord upper n (interleaveIndex n (i, 1))) =
        (if upper then Sum.inl i else Sum.inr i) := by
  cases upper <;> simp [bidiagonalParityCoord]

/-- The parity signature remains diagonal in the interleaved order. -/
theorem bidiagonalParitySignature_eq_diagonal (upper : Bool) (n : ℕ) :
    bidiagonalParitySignature upper n = diagonal
      (Sum.elim (fun _ : Fin n => (1 : ℝ)) (fun _ : Fin n => -1) ∘ bidiagonalParityCoord upper n) := by
  unfold bidiagonalParitySignature
  have h := massSignature_eq_diagonal n 1
  rw [one_smul] at h
  rw [h, submatrix_diagonal_equiv]

/-- Physical chain matrix with diagonal masses `−α,+α,…` for the upper orientation
and `+α,−α,…` for the lower orientation. -/
def bidiagonalMassShift {n : ℕ} (upper : Bool) (C : Matrix (Fin n) (Fin n) ℝ) (α : ℝ) :
    Matrix (Fin (n + n)) (Fin (n + n)) ℝ :=
  if upper then upperGolubKahanMassShift C α else lowerGolubKahanMassShift C α

/-- The shifted physical chain is exactly the block matrix `H₀ + αJ` in interleaved order. -/
theorem bidiagonalMassShift_eq_reindexed {n : ℕ} (upper : Bool)
    (C : Matrix (Fin n) (Fin n) ℝ) (α : ℝ) (hC : bidiagonalSupport upper C) :
    bidiagonalMassShift upper C α =
      (massShift C α).submatrix (bidiagonalParityCoord upper n) (bidiagonalParityCoord upper n) := by
  cases upper
  · exact lowerGolubKahanMassShift_eq_reindexed C hC α
  · exact upperGolubKahanMassShift_eq_reindexed C hC α

/-- The physical mass addition uses the same permutation as the unshifted dilation. -/
theorem bidiagonalMassShift_eq_add_signature {n : ℕ} (upper : Bool)
    (C : Matrix (Fin n) (Fin n) ℝ) (α : ℝ) (hC : bidiagonalSupport upper C) :
    bidiagonalMassShift upper C α =
      bidiagonalMassShift upper C 0 + α • bidiagonalParitySignature upper n := by
  rw [bidiagonalMassShift_eq_reindexed upper C α hC,
    bidiagonalMassShift_eq_reindexed upper C 0 hC]
  simp [massShift, submatrix_add, submatrix_smul, bidiagonalParitySignature]

theorem bidiagonalMassShift_isHermitian {n : ℕ} (upper : Bool)
    (C : Matrix (Fin n) (Fin n) ℝ) (α : ℝ) : (bidiagonalMassShift upper C α).IsHermitian := by
  cases upper
  · exact lowerGolubKahanMassShift_isHermitian C α
  · exact upperGolubKahanMassShift_isHermitian C α

/-- The same tridiagonal support holds before and after the shift. -/
theorem bidiagonalMassShift_far {n : ℕ} (upper : Bool)
    (C : Matrix (Fin n) (Fin n) ℝ) (α : ℝ) (i j : Fin (n + n))
    (hfar : i.val + 1 < j.val ∨ j.val + 1 < i.val) : bidiagonalMassShift upper C α i j = 0 := by
  cases upper
  · exact (golubKahanMassShift_far C α i j hfar).2
  · exact (golubKahanMassShift_far C α i j hfar).1

/-- The unshifted interleaved dilation contains every signed singular value in ascending order. -/
theorem bidiagonalMassShift_zero_orderedEigenvalue {n : ℕ} (upper : Bool)
    (C : Matrix (Fin n) (Fin n) ℝ) (hC : bidiagonalSupport upper C) (i : Fin (n + n)) :
    hermitianOrderedEigenvalue (bidiagonalMassShift_isHermitian upper C 0) i.rev =
      ascendingZeroMassValues (ascendingRealSpectrum C) i := by
  have hzero : bidiagonalMassShift upper C 0 =
      if upper then upperGolubKahan C else lowerGolubKahan C := by
    cases upper <;>
      simp [bidiagonalMassShift, upperGolubKahanMassShift, lowerGolubKahanMassShift,
        upperMassDiagonal, lowerMassDiagonal, Function.comp_def]
  cases upper
  · simp only [Bool.false_eq_true, if_false] at hzero
    exact (orderedEigenvalue_eq_of_charpoly _ (lowerGolubKahan_isHermitian C)
      (congrArg Matrix.charpoly hzero) _).trans (lowerGolubKahan_orderedEigenvalue C hC i)
  · simp only [ite_true] at hzero
    exact (orderedEigenvalue_eq_of_charpoly _ (upperGolubKahan_isHermitian C)
      (congrArg Matrix.charpoly hzero) _).trans (upperGolubKahan_orderedEigenvalue C hC i)

/-- Source rank `n+j` of `H₀`, where `j=i+1`, including zero and repeated singular values. -/
theorem bidiagonalMassShift_zero_positive_index {n : ℕ} (upper : Bool)
    (C : Matrix (Fin n) (Fin n) ℝ) (hC : bidiagonalSupport upper C) (i : Fin n) :
    hermitianOrderedEigenvalue (bidiagonalMassShift_isHermitian upper C 0) (Fin.natAdd n i).rev =
      ascendingRealSpectrum C i := by
  rw [bidiagonalMassShift_zero_orderedEigenvalue upper C hC, ascendingZeroMassValues_natAdd]

/-- The complete ordered spectrum of the actual positive-mass tridiagonal input. -/
theorem bidiagonalMassShift_orderedEigenvalue {n : ℕ} (upper : Bool)
    (C : Matrix (Fin n) (Fin n) ℝ) (α : ℝ) (hC : bidiagonalSupport upper C)
    (hα : 0 < α) (i : Fin (n + n)) :
    hermitianOrderedEigenvalue (bidiagonalMassShift_isHermitian upper C α) i.rev =
      ascendingMassValues α (ascendingRealSpectrum C) i := by
  cases upper
  · exact lowerGolubKahanMassShift_orderedEigenvalue C hC α hα i
  · exact upperGolubKahanMassShift_orderedEigenvalue C hC α hα i

/-- The one-based source ranks `n+j` and `n-j+1`, for `j=i+1`, yield the two prescribed values. -/
theorem bidiagonalMassShift_signed_ranks {n : ℕ} (upper : Bool)
    (C : Matrix (Fin n) (Fin n) ℝ) (α : ℝ) (hC : bidiagonalSupport upper C)
    (hα : 0 < α) (i : Fin n) :
    hermitianOrderedEigenvalue (bidiagonalMassShift_isHermitian upper C α) (Fin.natAdd n i).rev =
        massMagnitude α (ascendingRealSpectrum C i) ∧
    hermitianOrderedEigenvalue (bidiagonalMassShift_isHermitian upper C α)
        (Fin.castAdd n i.rev).rev = -massMagnitude α (ascendingRealSpectrum C i) := by
  simp only [bidiagonalMassShift_orderedEigenvalue upper C α hC hα,
    ascendingMassValues_natAdd, ascendingMassValues_castAdd, Fin.rev_rev, and_self]

private theorem singular_le_operatorNorm {n : ℕ}
    (C : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) :
    ascendingRealSpectrum C i ≤ realMatrixOperatorNorm C := by
  obtain ⟨U, V, _, hs, hC⟩ := exists_orthonormalBases_ascendingRealSpectrum C
  have hCV : C * orthonormalBasisMatrix V =
      orthonormalBasisMatrix U * diagonal (ascendingRealSpectrum C) := by
    nth_rewrite 1 [hC]
    simp only [Matrix.mul_assoc, orthonormalBasisMatrix_transpose_mul_self, Matrix.mul_one]
  have hvec : Matrix.toEuclideanCLM (𝕜 := ℝ) C (V i) = ascendingRealSpectrum C i • U i := by
    ext j
    have hj := congrFun (congrFun hCV j) i
    rw [Matrix.mul_diagonal] at hj
    simpa [Matrix.ofLp_toEuclideanCLM, Matrix.mulVec, dotProduct, Matrix.mul_apply,
      orthonormalBasisMatrix, mul_comm] using hj
  have h := Matrix.l2_opNorm_mulVec C (V i)
  change ‖Matrix.toEuclideanCLM (𝕜 := ℝ) C (V i)‖ ≤ _ at h
  rw [hvec, norm_smul, U.orthonormal.norm_eq_one i,
    V.orthonormal.norm_eq_one i, Real.norm_eq_abs, abs_of_nonneg (hs i), mul_one, mul_one] at h
  exact h

/-- The exact tridiagonal has norm bounded by the scaled singular norm plus the mass. -/
theorem bidiagonalMassShift_operatorNorm_le {n : ℕ} (upper : Bool)
    (C : Matrix (Fin n) (Fin n) ℝ) (α : ℝ) (hC : bidiagonalSupport upper C)
    (hα : 0 < α) :
    realMatrixOperatorNorm (bidiagonalMassShift upper C α) ≤ realMatrixOperatorNorm C + α := by
  let hA := bidiagonalMassShift_isHermitian upper C α
  have hnorm : 0 ≤ realMatrixOperatorNorm C := norm_nonneg _
  have hmass (i : Fin n) :
      massMagnitude α (ascendingRealSpectrum C i) ≤ realMatrixOperatorNorm C + α := by
    apply (massMagnitude_le_massMagnitude α (rectSingularValue_nonneg _ _)
      (singular_le_operatorNorm C i)).trans
    rw [massMagnitude, Real.sqrt_le_iff]
    exact ⟨by positivity, by nlinarith [mul_nonneg hα.le hnorm]⟩
  rw [← hermitianSpectralMatrix_eigenvalues hA]
  apply operatorNorm_hermitianSpectralMatrix_le hA _ (by positivity)
  intro i
  rw [← Fin.rev_rev i, bidiagonalMassShift_orderedEigenvalue upper C α hC hα]
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i.rev
  · rw [ascendingMassValues_castAdd, abs_neg, abs_of_nonneg (massMagnitude_nonneg _ _)]
    exact hmass _
  · rw [ascendingMassValues_natAdd, abs_of_nonneg (massMagnitude_nonneg _ _)]
    exact hmass _

/-- With the paper's bounds on the scaled matrix and the mass, the oracle input has norm below one. -/
theorem bidiagonalMassShift_operatorNorm_lt_one {n : ℕ} (upper : Bool)
    (C : Matrix (Fin n) (Fin n) ℝ) (α u : ℝ) (hC : bidiagonalSupport upper C)
    (hα : 0 < α) (hαu : α ≤ u) (hCnorm : realMatrixOperatorNorm C ≤ 1 / 2) (hu : u < 1 / 2) :
    realMatrixOperatorNorm (bidiagonalMassShift upper C α) ≤ 1 / 2 + u ∧
      realMatrixOperatorNorm (bidiagonalMassShift upper C α) < 1 := by
  have h := (bidiagonalMassShift_operatorNorm_le upper C α hC hα).trans (add_le_add hCnorm hαu)
  exact ⟨h, h.trans_lt (by linarith)⟩

private theorem upperGolubKahanOffdiag_native {p n : ℕ} (hp : 2 ≤ p)
    (C : Matrix (Fin n) (Fin n) ℝ) (hC : ∀ i j, Native p hp (C i j)) (i : Fin (n + n)) :
    Native p hp (upperGolubKahanOffdiag C i) := by
  unfold upperGolubKahanOffdiag
  split_ifs
  · exact hC _ _
  · exact hC _ _
  · exact native_zero p hp

private theorem mass_diagonal_native {p n : ℕ} (hp : 2 ≤ p) (upper : Bool)
    {α : ℝ} (hα : Native p hp α) (i : Fin (n + n)) :
    Native p hp ((Sum.elim (fun _ => α) (fun _ => -α)) (bidiagonalParityCoord upper n i)) := by
  cases bidiagonalParityCoord upper n i
  · exact hα
  · exact native_neg hα

/-- If the scaled input entries are native, a binary power as mass gives exact native
entries in the actual tridiagonal. The assembly only copies words or changes the sign of the mass. -/
theorem bidiagonalMassShift_native {p n : ℕ} (hp : 2 ≤ p) (upper : Bool)
    (C : Matrix (Fin n) (Fin n) ℝ) (hC : ∀ i j, Native p hp (C i j))
    (e : ℤ) (i j : Fin (n + n)) : Native p hp (bidiagonalMassShift upper C ((2 : ℝ) ^ e) i j) := by
  have hα := native_zpow p hp e
  have hentry (D : Matrix (Fin n) (Fin n) ℝ) (hD : ∀ i j, Native p hp (D i j))
      (b : Bool) :
      Native p hp ((upperGolubKahan D + diagonal
        (Sum.elim (fun _ => (2 : ℝ) ^ e) (fun _ => -((2 : ℝ) ^ e)) ∘
          bidiagonalParityCoord b n)) i j) := by
    by_cases hij : i = j
    · subst j
      simpa only [Matrix.add_apply, upperGolubKahan, zeroDiagonalTridiagonal_diag,
        diagonal_apply_eq, zero_add] using mass_diagonal_native hp b hα i
    · rw [Matrix.add_apply, diagonal_apply_ne _ hij, add_zero]
      unfold upperGolubKahan zeroDiagonalTridiagonal
      split_ifs
      · exact upperGolubKahanOffdiag_native hp D hD i
      · exact upperGolubKahanOffdiag_native hp D hD j
      · exact native_zero p hp
  cases upper
  · exact hentry Cᵀ (fun i j => hC j i) false
  · exact hentry C hC true

end NumStability.CertifiedTridiagonalEigenpairs
