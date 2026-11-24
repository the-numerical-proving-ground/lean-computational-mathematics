import ComputationalMathematics.Analysis.Eigenvalues.StrictSpectralCount
import Mathlib.Analysis.Matrix.Spectrum

/-!
# Characteristic roots of an ascending Hermitian spectrum

The ascending eigenvalue list of a real Hermitian matrix enumerates the roots
of its characteristic polynomial with their algebraic multiplicities.
-/

namespace NumStability.NoisyRankCertificate

/-- The multiset of characteristic roots is the multiset of ascending
eigenvalues, with one occurrence for each index. -/
theorem roots_charpoly_eq_ascendingEigenvalues {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.IsHermitian) :
    A.charpoly.roots = Multiset.map (ascendingEigenvalue hA)
      (Finset.univ : Finset (Fin n)).val := by
  let h := Matrix.isHermitian_iff_isSymmetric.mp hA
  have reindex {k l : ℕ} (hk : Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = k)
      (hl : Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = l)
      (e : k = l) (i : Fin k) :
      h.eigenvalues hk i = h.eigenvalues hl (finCongr e i) := by
    cases e
    rfl
  let e := (finCongr (Fintype.card_fin n)).trans (Fin.revPerm : Equiv.Perm (Fin n))
  rw [Matrix.IsHermitian.roots_charpoly_eq_eigenvalues₀ hA]
  conv_rhs => rw [← Multiset.map_univ_val_equiv e, Multiset.map_map]
  congr 1
  funext i
  change h.eigenvalues finrank_euclideanSpace i =
    h.eigenvalues finrank_euclideanSpace_fin ((finCongr (Fintype.card_fin n) i).rev.rev)
  rw [Fin.rev_rev]
  exact reindex finrank_euclideanSpace finrank_euclideanSpace_fin (Fintype.card_fin n) i

end NumStability.NoisyRankCertificate
