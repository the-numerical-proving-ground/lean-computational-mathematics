import ComputationalMathematics.Analysis.Eigenvalues.StrictSpectralCount
import ComputationalMathematics.Analysis.FunctionalCalculus.Resolvent.ImaginaryShift

/-! Relate the rank used by the real gate to the Section 6 complex spectrum. -/

namespace NumStability.CertifiedTridiagonalEigenpairs

open Matrix NoisyRankCertificate

/-- The Section 6 eigenvalue enumeration indexes the decreasing spectrum by
Mathlib's finite-type equivalence. Reverse the increasing gate index first. -/
noncomputable def sectionSixRank (n : ℕ) : Fin n ≃ Fin n :=
  Fin.revPerm.trans <| (finCongr (Fintype.card_fin n).symm).trans
    (Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card (Fin n))))

private theorem ordered_values_cast {n m : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.IsHermitian) (h : n = m) (i : Fin n) :
    (isHermitian_iff_isSymmetric.mp hA).eigenvalues
      (finrank_euclideanSpace_fin.trans h) (Fin.cast h i) =
      hermitianOrderedEigenvalue hA i := by
  subst m
  rfl

theorem sectionSixRank_eigenvalue {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.IsHermitian) (hAs : A.IsSymm) (i : Fin n) :
    (MatrixResolvent.isHermitian_map_ofReal hAs).eigenvalues (sectionSixRank n i) =
      ascendingEigenvalue hA i := by
  let hC := MatrixResolvent.isHermitian_map_ofReal hAs
  have hroots :
      (A.map Complex.ofReal).charpoly.roots = A.charpoly.roots.map Complex.ofReal := by
    change (A.map Complex.ofRealHom).charpoly.roots = A.charpoly.roots.map Complex.ofRealHom
    rw [Matrix.charpoly_map]
    exact (Polynomial.roots_map_of_injective_of_card_eq_natDegree Complex.ofReal_injective
      (Polynomial.splits_iff_card_roots.mp hA.splits_charpoly)).symm
  have hre :
      ((A.map Complex.ofReal).charpoly.roots.map (RCLike.re (K := ℂ))) =
        A.charpoly.roots.map (RCLike.re (K := ℝ)) := by
    rw [hroots, Multiset.map_map]
    simp
  have heq : hC.eigenvalues₀ = hA.eigenvalues₀ := by
    apply List.ofFn_inj.mp
    rw [← hC.sort_roots_charpoly_eq_eigenvalues₀, ← hA.sort_roots_charpoly_eq_eigenvalues₀, hre]
  simp only [Matrix.IsHermitian.eigenvalues, sectionSixRank, Equiv.trans_apply,
    Equiv.symm_apply_apply]
  change hC.eigenvalues₀ (Fin.cast (Fintype.card_fin n).symm i.rev) = ascendingEigenvalue hA i
  rw [heq]
  exact ordered_values_cast hA (Fintype.card_fin n).symm i.rev

end NumStability.CertifiedTridiagonalEigenpairs
