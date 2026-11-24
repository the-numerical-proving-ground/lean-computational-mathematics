import ComputationalMathematics.Analysis.SingularValues.FullRealSVD.Basic
import ComputationalMathematics.Order.Finset.ThresholdCounts
import Mathlib.Analysis.Matrix.Spectrum

/-!
# Canonical spectrum of an unsorted full nonnegative diagonal factorization

A full orthogonal factorization with a nonnegative diagonal preserves the
complete singular multiset. The actual ascending canonical spectrum is the
supplied tuple composed with its sorting permutation. Zero diagonal entries,
repeated values and dimension zero are included; the factorization is never
misinterpreted as a rank-equals-dimension SVD certificate.
-/

namespace NumStability

open scoped BigOperators

/-- A full orthogonal factorization identifies the characteristic polynomial
of the actual right Gram with that of the squared diagonal. -/
theorem charpoly_gram_of_orthogonal_factorization {n : ℕ}
    (A U V : Matrix (Fin n) (Fin n) ℝ) (v : Fin n → ℝ)
    (hU : U.transpose * U = 1) (hV : V.transpose * V = 1)
    (hA : A = U * Matrix.diagonal v * V.transpose) :
    (A.transpose * A).charpoly = (Matrix.diagonal (fun i => v i ^ 2)).charpoly := by
  have hgram : A.transpose * A = V * Matrix.diagonal (fun i => v i ^ 2) * V.transpose := by
    rw [hA]
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.diagonal_transpose,
      Matrix.mul_assoc, ← Matrix.mul_assoc U.transpose, hU, Matrix.one_mul]
    rw [← Matrix.mul_assoc (Matrix.diagonal v), Matrix.diagonal_mul_diagonal]
    simp only [pow_two]
  rw [hgram, Matrix.charpoly_mul_comm]
  simp only [← Matrix.mul_assoc, hV, Matrix.one_mul]

private theorem roots_charpoly_diagonal {n : ℕ} (v : Fin n → ℝ) :
    (Matrix.diagonal v).charpoly.roots = Multiset.map v Finset.univ.val := by
  rw [Matrix.charpoly_diagonal, Polynomial.roots_prod]
  · simp
  · simp [Finset.prod_ne_zero_iff, Polynomial.X_sub_C_ne_zero]

/-- The actual complete canonical singular multiset equals the supplied full
nonnegative diagonal multiset, including all zero entries and multiplicities. -/
theorem multiset_ascendingRealSpectrum_of_orthogonal_factorization {n : ℕ}
    (A U V : Matrix (Fin n) (Fin n) ℝ) (v : Fin n → ℝ)
    (hU : U.transpose * U = 1) (hV : V.transpose * V = 1)
    (hv : ∀ i, 0 ≤ v i) (hA : A = U * Matrix.diagonal v * V.transpose) :
    Multiset.map (ascendingRealSpectrum A) Finset.univ.val =
      Multiset.map v Finset.univ.val := by
  obtain ⟨U₀, V₀, _hmono, hnonneg, hcanonical⟩ :=
    exists_orthonormalBases_ascendingRealSpectrum A
  have hcanonicalGram := charpoly_gram_of_orthogonal_factorization A
    (orthonormalBasisMatrix U₀) (orthonormalBasisMatrix V₀) (ascendingRealSpectrum A)
    (orthonormalBasisMatrix_transpose_mul_self U₀)
    (orthonormalBasisMatrix_transpose_mul_self V₀) hcanonical
  have hgivenGram := charpoly_gram_of_orthogonal_factorization A U V v hU hV hA
  have hsquares := congrArg Polynomial.roots (hcanonicalGram.symm.trans hgivenGram)
  rw [roots_charpoly_diagonal, roots_charpoly_diagonal] at hsquares
  have hsqrt := congrArg (Multiset.map Real.sqrt) hsquares
  have hc (i : Fin n) : Real.sqrt (ascendingRealSpectrum A i ^ 2) = ascendingRealSpectrum A i :=
    Real.sqrt_sq (hnonneg i)
  have hv' (i : Fin n) : Real.sqrt (v i ^ 2) = v i := Real.sqrt_sq (hv i)
  simpa only [Multiset.map_map, Function.comp_def, hc, hv'] using hsqrt

/-- The canonical ascending spectrum is the supplied nonnegative diagonal
composed with the actual tuple-sorting permutation. -/
theorem ascendingRealSpectrum_eq_sorted_of_orthogonal_factorization {n : ℕ}
    (A U V : Matrix (Fin n) (Fin n) ℝ) (v : Fin n → ℝ)
    (hU : U.transpose * U = 1) (hV : V.transpose * V = 1)
    (hv : ∀ i, 0 ≤ v i) (hA : A = U * Matrix.diagonal v * V.transpose) :
    ascendingRealSpectrum A = v ∘ Tuple.sort v := by
  obtain ⟨_, _, hmono, _, _⟩ := exists_orthonormalBases_ascendingRealSpectrum A
  have hm := multiset_ascendingRealSpectrum_of_orthogonal_factorization A U V v hU hV hv hA
  have hp : (List.ofFn (ascendingRealSpectrum A)).Perm (List.ofFn v) := by
    apply Multiset.coe_eq_coe.mp
    simpa only [Fin.univ_val_map] using hm
  have hp' : (List.ofFn (ascendingRealSpectrum A)).Perm (List.ofFn (v ∘ Tuple.sort v)) :=
    hp.trans ((Tuple.sort v).ofFn_comp_perm v).symm
  exact List.ofFn_inj.mp (hp'.eq_of_pairwise' hmono.sortedLE_ofFn.pairwise
    (Tuple.monotone_sort v).sortedLE_ofFn.pairwise)

/-- Raw threshold counts of the actual canonical spectrum equal the raw
multiplicity counts of the supplied nonnegative full diagonal. -/
theorem countLE_ascendingRealSpectrum_eq_of_orthogonal_factorization {n : ℕ}
    (A U V : Matrix (Fin n) (Fin n) ℝ) (v : Fin n → ℝ)
    (hU : U.transpose * U = 1) (hV : V.transpose * V = 1)
    (hv : ∀ i, 0 ≤ v i) (hA : A = U * Matrix.diagonal v * V.transpose) (x : ℝ) :
    OrderStatistics.countLE (ascendingRealSpectrum A) x = OrderStatistics.countLE v x := by
  rw [ascendingRealSpectrum_eq_sorted_of_orthogonal_factorization A U V v hU hV hv hA]
  unfold OrderStatistics.countLE
  exact Equiv.sum_comp (Tuple.sort v) (fun i : Fin n => if v i ≤ x then (1 : ℝ) else 0)

end NumStability
