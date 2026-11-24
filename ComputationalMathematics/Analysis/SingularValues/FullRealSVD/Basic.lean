import ComputationalMathematics.Analysis.SingularValues.FullRealSVD.Defs
import ComputationalMathematics.HDP.Matrix.RealSVDFullBases
import ComputationalMathematics.Analysis.SingularValues.InverseSVD
import ComputationalMathematics.Analysis.SingularValues.Transpose
import Mathlib.Data.Fin.Embedding

/-!
# Complete ascending real singular-value decompositions

Transport the existing compatible full singular bases to the complete canonical
ascending spectrum, retaining zero singular values and all multiplicities.
-/

namespace NumStability

open scoped BigOperators

/-- Internal transport used only to extend the existing rank reconstruction
sum by its known zero tail. This is not an additional SVD construction/API.
-/
private theorem sum_eq_sum_embedding {n r : ℕ} (I : Fin r ↪ Fin n)
    (f : Fin n → ℝ) (hzero : ∀ i, (∀ j, I j ≠ i) → f i = 0) :
    (∑ i, f i) = ∑ j, f (I j) := by
  classical
  let image : Finset (Fin n) := Finset.univ.map I
  have hsum : image.sum f = ∑ i, f i := by
    apply Finset.sum_subset (Finset.subset_univ image)
    intro i _hi hnot
    apply hzero i
    intro j hij
    apply hnot
    exact Finset.mem_map.mpr ⟨j, Finset.mem_univ _, hij⟩
  calc
    (∑ i, f i) = image.sum f := hsum.symm
    _ = ∑ j, f (I j) := by simp [image]

/-- Complete canonical ascending real SVD, including all zero values and n=0.
Actual existing full orthonormal bases are reindexed by Fin.revPerm; their
rank-length reconstruction is extended only by its known zero terms.
-/
theorem exists_orthonormalBases_ascendingRealSpectrum {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) :
    ∃ U V : OrthonormalBasis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)),
      Monotone (ascendingRealSpectrum A) ∧
      (∀ i, 0 ≤ ascendingRealSpectrum A i) ∧
      A = orthonormalBasisMatrix U * Matrix.diagonal (ascendingRealSpectrum A) *
        (orthonormalBasisMatrix V).transpose := by
  classical
  obtain ⟨r, hm, hn, s, U, V, h⟩ :=
    exists_realMatrixSVD_full_orthonormal_bases A
  have hfull : IsSquareRealSVD A s U V := by
    intro a b
    have hsum : (∑ i : Fin n, s i * U i a * V i b) =
        ∑ j : Fin r, s (Fin.castLE hn j) * U (Fin.castLE hn j) a *
          V (Fin.castLE hn j) b := by
      apply sum_eq_sum_embedding (Fin.castLEEmb hn)
      intro i hi
      have hri : r ≤ i.val := by
        by_contra hnot
        have hir : i.val < r := lt_of_not_ge hnot
        exact hi ⟨i.val, hir⟩ (Fin.ext rfl)
      rw [h.singularValues_zero_of_rank_le i hri]
      simp
    exact (h.reconstruction a b).trans hsum.symm
  have hasc : IsSquareRealSVD A (fun i : Fin n => s i.rev)
      (U.reindex Fin.revPerm) (V.reindex Fin.revPerm) := by
    intro a b
    calc
      A a b = ∑ i : Fin n, s i * U i a * V i b := hfull a b
      _ = ∑ i : Fin n, s i.rev * U i.rev a * V i.rev b :=
        (Equiv.sum_comp Fin.revPerm (fun i => s i * U i a * V i b)).symm
      _ = ∑ i : Fin n, s i.rev * (U.reindex Fin.revPerm) i a *
          (V.reindex Fin.revPerm) i b := by
        simp only [OrthonormalBasis.reindex_apply, Fin.revPerm_symm, Fin.revPerm_apply]
  have hs : (fun i : Fin n => s i.rev) = ascendingRealSpectrum A := by
    funext i
    exact h.toIsRealMatrixSVD.singularValue_eq_rectSingularValue i.rev
  refine ⟨U.reindex Fin.revPerm, V.reindex Fin.revPerm, ?_, ?_, ?_⟩
  · rw [← hs]
    intro i j hij
    exact h.singularValues_antitone (Fin.rev_anti hij)
  · rw [← hs]
    intro i
    exact h.singularValues_nonnegative _
  · rw [← hs]
    exact isSquareRealSVD_eq_matrix_mul hasc


end NumStability
