import ComputationalMathematics.Analysis.MatrixStructure.Bipartite.ZeroMassSpectrum

/-!
# Physical Golub--Kahan tridiagonals and their complete ordered spectra

For upper bidiagonal inputs, the physical order is right₀,left₀,right₁,left₁,…;
for lower bidiagonal inputs it is left₀,right₀,left₁,right₁,… . Off-diagonal
entries keep their original signs. No nonzero-entry or simple-spectrum
assumption is made.
-/

open Matrix

namespace NumStability.Matrix.Bipartite

/-- Upper bidiagonal support: only the diagonal and first superdiagonal may be nonzero. -/
def IsUpperBidiagonalSupport {n : ℕ} (C : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∀ i j, i ≠ j → j.val ≠ i.val + 1 → C i j = 0

/-- Lower bidiagonal support: only the diagonal and first subdiagonal may be nonzero. -/
def IsLowerBidiagonalSupport {n : ℕ} (C : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∀ i j, i ≠ j → i.val ≠ j.val + 1 → C i j = 0

/-- The pair `(i,p)` is at physical zero-based position `2*i+p`. -/
def interleaveIndex (n : ℕ) : (Fin n × Fin 2) ≃ Fin (n + n) :=
  finProdFinEquiv.trans (finCongr (Nat.mul_two n))

@[simp] theorem interleaveIndex_val {n : ℕ} (i : Fin n) (p : Fin 2) :
    (interleaveIndex n (i, p)).val = p.val + 2 * i.val := by
  rfl

/-- Lower orientation: even coordinates are left, odd coordinates are right. -/
def lowerInterleaveCoord (n : ℕ) : Fin (n + n) ≃ (Fin n ⊕ Fin n) :=
  (interleaveIndex n).symm.trans ((Equiv.prodComm _ _).trans
    ((Equiv.prodCongr finTwoEquiv (Equiv.refl (Fin n))).trans
      (Equiv.boolProdEquivSum (Fin n))))

/-- Upper orientation: even coordinates are right, odd coordinates are left. -/
def upperInterleaveCoord (n : ℕ) : Fin (n + n) ≃ (Fin n ⊕ Fin n) :=
  (lowerInterleaveCoord n).trans (Equiv.sumComm _ _)

@[simp] theorem lowerInterleaveCoord_even {n : ℕ} (i : Fin n) :
    lowerInterleaveCoord n (interleaveIndex n (i, 0)) = Sum.inl i := by
  simp [lowerInterleaveCoord, finTwoEquiv]

@[simp] theorem lowerInterleaveCoord_odd {n : ℕ} (i : Fin n) :
    lowerInterleaveCoord n (interleaveIndex n (i, 1)) = Sum.inr i := by
  simp [lowerInterleaveCoord, finTwoEquiv]

@[simp] theorem upperInterleaveCoord_even {n : ℕ} (i : Fin n) :
    upperInterleaveCoord n (interleaveIndex n (i, 0)) = Sum.inr i := by
  simp [upperInterleaveCoord]

@[simp] theorem upperInterleaveCoord_odd {n : ℕ} (i : Fin n) :
    upperInterleaveCoord n (interleaveIndex n (i, 1)) = Sum.inl i := by
  simp [upperInterleaveCoord]

/-- The singular coordinate belonging to a physical position. -/
def interleaveHalf {n : ℕ} (i : Fin (n + n)) : Fin n :=
  ⟨i.val / 2, by have hi := i.isLt; omega⟩

/-- Upper signed off-diagonal sequence `a₀,b₀,a₁,b₁,…`.
The unused final coefficient is zero; this convention also covers dimensions zero and one. -/
def upperGolubKahanOffdiag {n : ℕ} (C : Matrix (Fin n) (Fin n) ℝ)
    (k : Fin (n + n)) : ℝ :=
  if k.val % 2 = 0 then C (interleaveHalf k) (interleaveHalf k)
  else if h : k.val / 2 + 1 < n then C (interleaveHalf k) ⟨k.val / 2 + 1, h⟩
  else 0

/-- Symmetric zero-diagonal tridiagonal matrix built from its signed off-diagonals. -/
def zeroDiagonalTridiagonal {m : ℕ} (t : Fin m → ℝ) : Matrix (Fin m) (Fin m) ℝ :=
  fun i j => if j.val = i.val + 1 then t i else if i.val = j.val + 1 then t j else 0

/-- Physical upper-bidiagonal Golub--Kahan tridiagonal. -/
def upperGolubKahan {n : ℕ} (C : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin (n + n)) (Fin (n + n)) ℝ :=
  zeroDiagonalTridiagonal (upperGolubKahanOffdiag C)

/-- Physical lower-bidiagonal Golub--Kahan tridiagonal, using the subdiagonal of `C`. -/
def lowerGolubKahan {n : ℕ} (C : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin (n + n)) (Fin (n + n)) ℝ :=
  upperGolubKahan Cᵀ

@[simp] theorem upperGolubKahanOffdiag_even {n : ℕ}
    (C : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) :
    upperGolubKahanOffdiag C (interleaveIndex n (i, 0)) = C i i := by
  simp [upperGolubKahanOffdiag, interleaveHalf, interleaveIndex, finProdFinEquiv]

@[simp] theorem upperGolubKahanOffdiag_odd {n : ℕ}
    (C : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) (hi : i.val + 1 < n) :
    upperGolubKahanOffdiag C (interleaveIndex n (i, 1)) = C i ⟨i.val + 1, hi⟩ := by
  have hd : (1 + 2 * i.val) / 2 = i.val := by omega
  simp [upperGolubKahanOffdiag, interleaveHalf, interleaveIndex, finProdFinEquiv, hd, hi]

/-- All physical diagonal entries vanish. -/
@[simp] theorem zeroDiagonalTridiagonal_diag {m : ℕ} (t : Fin m → ℝ) (i : Fin m) :
    zeroDiagonalTridiagonal t i i = 0 := by
  simp [zeroDiagonalTridiagonal]

/-- There are no entries outside the first off-diagonals. -/
theorem zeroDiagonalTridiagonal_far {m : ℕ} (t : Fin m → ℝ) (i j : Fin m)
    (h : i.val + 1 < j.val ∨ j.val + 1 < i.val) :
    zeroDiagonalTridiagonal t i j = 0 := by
  have h1 : j.val ≠ i.val + 1 := by omega
  have h2 : i.val ≠ j.val + 1 := by omega
  simp [zeroDiagonalTridiagonal, h1, h2]

/-- The explicit physical tridiagonal is symmetric. -/
theorem zeroDiagonalTridiagonal_transpose {m : ℕ} (t : Fin m → ℝ) :
    (zeroDiagonalTridiagonal t)ᵀ = zeroDiagonalTridiagonal t := by
  ext i j
  simp only [transpose_apply, zeroDiagonalTridiagonal]
  by_cases h1 : j.val = i.val + 1
  · have h2 : i.val ≠ j.val + 1 := by omega
    simp only [if_pos h1, if_neg h2]
  · by_cases h2 : i.val = j.val + 1
    · simp only [if_neg h1, if_pos h2]
    · simp only [if_neg h1, if_neg h2]

private theorem upperGolubKahan_same_parity {n : ℕ}
    (C : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) (p : Fin 2) :
    upperGolubKahan C (interleaveIndex n (i, p)) (interleaveIndex n (j, p)) = 0 := by
  have h1 : p.val + 2 * j.val ≠ p.val + 2 * i.val + 1 := by omega
  have h2 : p.val + 2 * i.val ≠ p.val + 2 * j.val + 1 := by omega
  simp [upperGolubKahan, zeroDiagonalTridiagonal, h1, h2]

private theorem upperGolubKahan_even_odd {n : ℕ}
    (C : Matrix (Fin n) (Fin n) ℝ) (hC : IsUpperBidiagonalSupport C) (i j : Fin n) :
    upperGolubKahan C (interleaveIndex n (i, 0)) (interleaveIndex n (j, 1)) = C j i := by
  by_cases hji : j = i
  · subst j
    have h1 : 1 + 2 * i.val = 0 + 2 * i.val + 1 := by omega
    simp only [upperGolubKahan, zeroDiagonalTridiagonal, interleaveIndex_val,
      Fin.val_zero, Fin.val_one, if_pos h1]
    exact upperGolubKahanOffdiag_even C i
  · by_cases hnext : i.val = j.val + 1
    · have hn : j.val + 1 < n := by omega
      have hi : (⟨j.val + 1, hn⟩ : Fin n) = i := Fin.ext hnext.symm
      have h1 : 1 + 2 * j.val ≠ 0 + 2 * i.val + 1 := by omega
      have h2 : 0 + 2 * i.val = 1 + 2 * j.val + 1 := by omega
      simp only [upperGolubKahan, zeroDiagonalTridiagonal, interleaveIndex_val,
        Fin.val_zero, Fin.val_one, if_neg h1, if_pos h2]
      rw [upperGolubKahanOffdiag_odd C j hn, hi]
    · have hv : j.val ≠ i.val := fun h => hji (Fin.ext h)
      have h1 : 1 + 2 * j.val ≠ 0 + 2 * i.val + 1 := by omega
      have h2 : 0 + 2 * i.val ≠ 1 + 2 * j.val + 1 := by omega
      simp only [upperGolubKahan, zeroDiagonalTridiagonal, interleaveIndex_val,
        Fin.val_zero, Fin.val_one, if_neg h1, if_neg h2]
      exact (hC j i hji hnext).symm

/-- The explicit upper physical tridiagonal is exactly a permutation of the symmetric embedding. -/
theorem upperGolubKahan_eq_reindexed_embedding {n : ℕ}
    (C : Matrix (Fin n) (Fin n) ℝ) (hC : IsUpperBidiagonalSupport C) :
    upperGolubKahan C = (embedding C).submatrix (upperInterleaveCoord n) (upperInterleaveCoord n) := by
  ext a b
  obtain ⟨⟨i, p⟩, rfl⟩ := (interleaveIndex n).surjective a
  obtain ⟨⟨j, q⟩, rfl⟩ := (interleaveIndex n).surjective b
  fin_cases p <;> fin_cases q
  · simpa [embedding] using upperGolubKahan_same_parity C i j 0
  · simpa [embedding] using upperGolubKahan_even_odd C hC i j
  · have hsym := congrFun (congrFun (zeroDiagonalTridiagonal_transpose
        (upperGolubKahanOffdiag C)) (interleaveIndex n (j, 0))) (interleaveIndex n (i, 1))
    change upperGolubKahan C (interleaveIndex n (i, 1)) (interleaveIndex n (j, 0)) =
      upperGolubKahan C (interleaveIndex n (j, 0)) (interleaveIndex n (i, 1)) at hsym
    simpa [embedding] using hsym.trans (upperGolubKahan_even_odd C hC j i)
  · simpa [embedding] using upperGolubKahan_same_parity C i j 1

/-- Lower support becomes upper support after transpose. -/
theorem IsLowerBidiagonalSupport.transpose {n : ℕ} {C : Matrix (Fin n) (Fin n) ℝ}
    (hC : IsLowerBidiagonalSupport C) : IsUpperBidiagonalSupport Cᵀ := by
  intro i j hij hnext
  exact hC j i (Ne.symm hij) hnext

/-- The lower physical order is the left/right-swapped upper order of the transpose. -/
theorem lower_reindexed_embedding_eq_upper_transpose {n : ℕ}
    (C : Matrix (Fin n) (Fin n) ℝ) :
    (embedding C).submatrix (lowerInterleaveCoord n) (lowerInterleaveCoord n) =
      (embedding Cᵀ).submatrix (upperInterleaveCoord n) (upperInterleaveCoord n) := by
  ext a b
  obtain ⟨⟨i, p⟩, rfl⟩ := (interleaveIndex n).surjective a
  obtain ⟨⟨j, q⟩, rfl⟩ := (interleaveIndex n).surjective b
  fin_cases p <;> fin_cases q <;> simp [embedding]

/-- The physical lower tridiagonal is exactly the lower-orientation permutation. -/
theorem lowerGolubKahan_eq_reindexed_embedding {n : ℕ}
    (C : Matrix (Fin n) (Fin n) ℝ) (hC : IsLowerBidiagonalSupport C) :
    lowerGolubKahan C = (embedding C).submatrix (lowerInterleaveCoord n) (lowerInterleaveCoord n) := by
  rw [lower_reindexed_embedding_eq_upper_transpose]
  exact upperGolubKahan_eq_reindexed_embedding Cᵀ hC.transpose

/-- Both orientations have a zero physical diagonal. -/
theorem golubKahan_diag {n : ℕ} (C : Matrix (Fin n) (Fin n) ℝ) (i : Fin (n + n)) :
    upperGolubKahan C i i = 0 ∧ lowerGolubKahan C i i = 0 := by
  constructor <;> exact zeroDiagonalTridiagonal_diag _ i

/-- Both orientations have tridiagonal support. -/
theorem golubKahan_far {n : ℕ} (C : Matrix (Fin n) (Fin n) ℝ) (i j : Fin (n + n))
    (h : i.val + 1 < j.val ∨ j.val + 1 < i.val) :
    upperGolubKahan C i j = 0 ∧ lowerGolubKahan C i j = 0 := by
  constructor <;> exact zeroDiagonalTridiagonal_far _ i j h

/-- Signed diagonal entries of `C` occur in the even physical off-diagonal slots. -/
theorem golubKahan_even_offdiag {n : ℕ}
    (C : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) :
    upperGolubKahan C (interleaveIndex n (i, 0)) (interleaveIndex n (i, 1)) = C i i ∧
    lowerGolubKahan C (interleaveIndex n (i, 0)) (interleaveIndex n (i, 1)) = C i i := by
  have hpos : 1 + 2 * i.val = 0 + 2 * i.val + 1 := by omega
  simp only [upperGolubKahan, lowerGolubKahan, zeroDiagonalTridiagonal,
    interleaveIndex_val, Fin.val_zero, Fin.val_one, if_pos hpos]
  simp

/-- Upper superdiagonal and lower subdiagonal entries occupy the odd physical slots. -/
theorem golubKahan_odd_offdiag {n : ℕ}
    (C : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) (hi : i.val + 1 < n) :
    upperGolubKahan C (interleaveIndex n (i, 1))
        (interleaveIndex n (⟨i.val + 1, hi⟩, 0)) = C i ⟨i.val + 1, hi⟩ ∧
    lowerGolubKahan C (interleaveIndex n (i, 1))
        (interleaveIndex n (⟨i.val + 1, hi⟩, 0)) = C ⟨i.val + 1, hi⟩ i := by
  have hpos : 0 + 2 * (i.val + 1) = 1 + 2 * i.val + 1 := by omega
  simp only [upperGolubKahan, lowerGolubKahan, zeroDiagonalTridiagonal,
    interleaveIndex_val, Fin.val_zero, Fin.val_one, if_pos hpos]
  simp [upperGolubKahanOffdiag_odd, hi]

/-- The physical upper tridiagonal is Hermitian, independently of the support hypothesis. -/
theorem upperGolubKahan_isHermitian {n : ℕ} (C : Matrix (Fin n) (Fin n) ℝ) :
    (upperGolubKahan C).IsHermitian := by
  rw [Matrix.IsHermitian, conjTranspose_eq_transpose_of_trivial]
  exact zeroDiagonalTridiagonal_transpose _

/-- The physical lower tridiagonal is Hermitian. -/
theorem lowerGolubKahan_isHermitian {n : ℕ} (C : Matrix (Fin n) (Fin n) ℝ) :
    (lowerGolubKahan C).IsHermitian :=
  upperGolubKahan_isHermitian Cᵀ

/-- Coordinate permutations retain the complete characteristic polynomial. -/
private theorem charpoly_embedding_submatrix {n : ℕ}
    (C : Matrix (Fin n) (Fin n) ℝ) (q : Fin (n + n) ≃ (Fin n ⊕ Fin n)) :
    ((embedding C).submatrix q q).charpoly = (finEmbedding C).charpoly := by
  have hq := Matrix.charpoly_reindex q.symm (embedding C)
  have he := Matrix.charpoly_reindex finSumFinEquiv (embedding C)
  exact hq.trans he.symm

/-- Upper physical and contiguous-block embeddings have the same multiplicities. -/
theorem upperGolubKahan_charpoly {n : ℕ}
    (C : Matrix (Fin n) (Fin n) ℝ) (hC : IsUpperBidiagonalSupport C) :
    (upperGolubKahan C).charpoly = (finEmbedding C).charpoly := by
  rw [upperGolubKahan_eq_reindexed_embedding C hC]
  exact charpoly_embedding_submatrix C _

/-- Lower physical and contiguous-block embeddings have the same multiplicities. -/
theorem lowerGolubKahan_charpoly {n : ℕ}
    (C : Matrix (Fin n) (Fin n) ℝ) (hC : IsLowerBidiagonalSupport C) :
    (lowerGolubKahan C).charpoly = (finEmbedding C).charpoly := by
  rw [lowerGolubKahan_eq_reindexed_embedding C hC]
  exact charpoly_embedding_submatrix C _

/-- Characteristic-polynomial invariance transports the actual ordered eigenvalues. -/
theorem orderedEigenvalue_eq_of_charpoly {m : ℕ}
    {A B : Matrix (Fin m) (Fin m) ℝ} (hA : A.IsHermitian) (hB : B.IsHermitian)
    (hc : A.charpoly = B.charpoly) (i : Fin m) :
    hermitianOrderedEigenvalue hA i = hermitianOrderedEigenvalue hB i := by
  have hE : hA.eigenvalues₀ = hB.eigenvalues₀ := by
    apply List.ofFn_inj.mp
    rw [← hA.sort_roots_charpoly_eq_eigenvalues₀, ← hB.sort_roots_charpoly_eq_eigenvalues₀, hc]
  have h := congrFun hE (Fin.cast (Fintype.card_fin m).symm i)
  rw [eigenvalues₀_cast_eq_ordered, eigenvalues₀_cast_eq_ordered] at h
  exact h

/-- Complete ascending physical upper spectrum, including all zero and repeated labels. -/
theorem upperGolubKahan_orderedEigenvalue {n : ℕ}
    (C : Matrix (Fin n) (Fin n) ℝ) (hC : IsUpperBidiagonalSupport C) (i : Fin (n + n)) :
    hermitianOrderedEigenvalue (upperGolubKahan_isHermitian C) i.rev =
      ascendingZeroMassValues (ascendingRealSpectrum C) i := by
  rw [orderedEigenvalue_eq_of_charpoly (upperGolubKahan_isHermitian C)
    (finEmbedding_isHermitian C) (upperGolubKahan_charpoly C hC)]
  exact finEmbedding_orderedEigenvalue C i

/-- Complete ascending physical lower spectrum with the same multiplicities. -/
theorem lowerGolubKahan_orderedEigenvalue {n : ℕ}
    (C : Matrix (Fin n) (Fin n) ℝ) (hC : IsLowerBidiagonalSupport C) (i : Fin (n + n)) :
    hermitianOrderedEigenvalue (lowerGolubKahan_isHermitian C) i.rev =
      ascendingZeroMassValues (ascendingRealSpectrum C) i := by
  rw [orderedEigenvalue_eq_of_charpoly (lowerGolubKahan_isHermitian C)
    (finEmbedding_isHermitian C) (lowerGolubKahan_charpoly C hC)]
  exact finEmbedding_orderedEigenvalue C i

/-- Prescribed positive upper index: zero-based `n+i`, or one-based `n+j` for `j=i+1`. -/
theorem upperGolubKahan_orderedEigenvalue_positive_index {n : ℕ}
    (C : Matrix (Fin n) (Fin n) ℝ) (hC : IsUpperBidiagonalSupport C) (i : Fin n) :
    hermitianOrderedEigenvalue (upperGolubKahan_isHermitian C) (Fin.natAdd n i).rev =
      ascendingRealSpectrum C i := by
  rw [upperGolubKahan_orderedEigenvalue C hC, ascendingZeroMassValues_natAdd]

/-- Prescribed positive lower index, retaining zero singular values and multiplicities. -/
theorem lowerGolubKahan_orderedEigenvalue_positive_index {n : ℕ}
    (C : Matrix (Fin n) (Fin n) ℝ) (hC : IsLowerBidiagonalSupport C) (i : Fin n) :
    hermitianOrderedEigenvalue (lowerGolubKahan_isHermitian C) (Fin.natAdd n i).rev =
      ascendingRealSpectrum C i := by
  rw [lowerGolubKahan_orderedEigenvalue C hC, ascendingZeroMassValues_natAdd]

/-- The upper negative partner occupies zero-based ascending index `n-1-i`. -/
theorem upperGolubKahan_orderedEigenvalue_negative_index {n : ℕ}
    (C : Matrix (Fin n) (Fin n) ℝ) (hC : IsUpperBidiagonalSupport C) (i : Fin n) :
    hermitianOrderedEigenvalue (upperGolubKahan_isHermitian C) (Fin.castAdd n i.rev).rev =
      -ascendingRealSpectrum C i := by
  rw [upperGolubKahan_orderedEigenvalue C hC, ascendingZeroMassValues_castAdd, Fin.rev_rev]

/-- The lower negative partner occupies the same prescribed ascending index. -/
theorem lowerGolubKahan_orderedEigenvalue_negative_index {n : ℕ}
    (C : Matrix (Fin n) (Fin n) ℝ) (hC : IsLowerBidiagonalSupport C) (i : Fin n) :
    hermitianOrderedEigenvalue (lowerGolubKahan_isHermitian C) (Fin.castAdd n i.rev).rev =
      -ascendingRealSpectrum C i := by
  rw [lowerGolubKahan_orderedEigenvalue C hC, ascendingZeroMassValues_castAdd, Fin.rev_rev]

/-- Mathlib's ordered eigenvalues of the upper physical tridiagonal, with explicit casts. -/
theorem upperGolubKahan_mathlib_eigenvalues₀ {n : ℕ}
    (C : Matrix (Fin n) (Fin n) ℝ) (hC : IsUpperBidiagonalSupport C) (i : Fin (n + n)) :
    (upperGolubKahan_isHermitian C).eigenvalues₀
        (Fin.cast (Fintype.card_fin (n + n)).symm i.rev) =
      ascendingZeroMassValues (ascendingRealSpectrum C) i := by
  rw [eigenvalues₀_cast_eq_ordered]
  exact upperGolubKahan_orderedEigenvalue C hC i

/-- Mathlib's ordered eigenvalues of the lower physical tridiagonal, with explicit casts. -/
theorem lowerGolubKahan_mathlib_eigenvalues₀ {n : ℕ}
    (C : Matrix (Fin n) (Fin n) ℝ) (hC : IsLowerBidiagonalSupport C) (i : Fin (n + n)) :
    (lowerGolubKahan_isHermitian C).eigenvalues₀
        (Fin.cast (Fintype.card_fin (n + n)).symm i.rev) =
      ascendingZeroMassValues (ascendingRealSpectrum C) i := by
  rw [eigenvalues₀_cast_eq_ordered]
  exact lowerGolubKahan_orderedEigenvalue C hC i

/-- A uniform entry bound on `C` bounds every physical off-diagonal coefficient. -/
theorem upperGolubKahanOffdiag_abs_le {n : ℕ}
    (C : Matrix (Fin n) (Fin n) ℝ) (M : ℝ) (hM : 0 ≤ M)
    (hC : ∀ i j, |C i j| ≤ M) (k : Fin (n + n)) :
    |upperGolubKahanOffdiag C k| ≤ M := by
  unfold upperGolubKahanOffdiag
  split_ifs
  · exact hC _ _
  · exact hC _ _
  · simpa using hM

end NumStability.Matrix.Bipartite
