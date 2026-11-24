import ComputationalMathematics.Analysis.Eigenvalues.StrictSpectralCount
import ComputationalMathematics.HDP.Matrix.OrderedEigenbasis

/-!
# Ordered eigenbasis retaining prescribed eigenvectors

Unit vectors supplied for selected simple eigenvalues can be retained at their
canonical indices in a full orthonormal eigenbasis.
-/

namespace NumStability

open NoisyRankCertificate
open scoped RealInnerProductSpace

theorem exists_ascendingEigenbasis_preserving_selected {n k : ℕ}
    {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsHermitian)
    (I : Fin k → Fin n) (hI : Function.Injective I)
    (U : Fin k → EuclideanSpace ℝ (Fin n))
    (hsimple : ∀ j i, i ≠ I j → ascendingEigenvalue hA i ≠ ascendingEigenvalue hA (I j))
    (hU : ∀ j, ‖U j‖ = 1 ∧ A.toEuclideanLin (U j) = ascendingEigenvalue hA (I j) • U j) :
    ∃ b : OrthonormalBasis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)),
      (∀ i, A.toEuclideanLin (b i) = ascendingEigenvalue hA i • b i) ∧
      (∀ j, b (I j) = U j) := by
  classical
  let b₀ := (hermitianOrderedEigenbasis hA).reindex Fin.revPerm
  have hb₀ (i : Fin n) : b₀ i = hermitianOrderedEigenbasis hA i.rev := by
    simp [b₀, Fin.revPerm]
  let v (i : Fin n) := if h : ∃ j, I j = i then U h.choose else b₀ i
  have hv (j : Fin k) : v (I j) = U j := by
    have h : ∃ l, I l = I j := ⟨j, rfl⟩
    simp only [v, dif_pos h, hI h.choose_spec]
  have hvEig (i : Fin n) : A.toEuclideanLin (v i) = ascendingEigenvalue hA i • v i := by
    by_cases h : ∃ j, I j = i
    · rw [← h.choose_spec, hv]
      exact (hU _).2
    · simpa only [v, dif_neg h, hb₀] using hermitianOrderedEigenbasis_apply hA i.rev
  have hvNorm (i : Fin n) : ‖v i‖ = 1 := by
    by_cases h : ∃ j, I j = i
    · rw [← h.choose_spec, hv]
      exact (hU _).1
    · simpa only [v, dif_neg h] using b₀.norm_eq_one i
  have horth_of_ne {i j : Fin n}
      (hne : ascendingEigenvalue hA i ≠ ascendingEigenvalue hA j) :
      ⟪v i, v j⟫ = 0 := by
    have h := (Matrix.isHermitian_iff_isSymmetric.mp hA) (v i) (v j)
    change ⟪A.toEuclideanLin (v i), v j⟫ = ⟪v i, A.toEuclideanLin (v j)⟫ at h
    simp only [hvEig, real_inner_smul_left, real_inner_smul_right] at h
    exact (mul_eq_zero.mp (by rw [sub_mul, sub_eq_zero]; exact h :
      (ascendingEigenvalue hA i - ascendingEigenvalue hA j) * ⟪v i, v j⟫ = 0)).resolve_left
      (sub_ne_zero.mpr hne)
  have horth : Orthonormal ℝ v := by
    apply orthonormal_iff_ite.mpr
    intro i j
    by_cases hij : i = j
    · subst j
      simp [hvNorm]
    · rw [if_neg hij]
      by_cases hi : ∃ l, I l = i
      · exact horth_of_ne ((show ascendingEigenvalue hA j ≠ ascendingEigenvalue hA i by
          rw [← hi.choose_spec]
          exact hsimple _ _ (by simpa only [hi.choose_spec] using Ne.symm hij)).symm)
      by_cases hj : ∃ l, I l = j
      · apply horth_of_ne
        rw [← hj.choose_spec]
        exact hsimple _ _ (by simpa only [hj.choose_spec] using hij)
      · simpa only [v, dif_neg hi, dif_neg hj, if_neg hij] using b₀.inner_eq_ite i j
  have hspan := (horth.linearIndependent.span_eq_top_of_card_eq_finrank'
    (by rw [Fintype.card_fin, finrank_euclideanSpace_fin])).ge
  let b := OrthonormalBasis.mk horth hspan
  have hb : ⇑b = v := OrthonormalBasis.coe_mk horth hspan
  exact ⟨b, by simpa only [hb] using hvEig, by simpa only [hb] using hv⟩

/-- An ascending eigenvalue list on a complete orthonormal eigenbasis is the
canonical ordered list, with the same multiplicities. -/
theorem ascendingEigenvalue_eq_of_eigenbasis {n : ℕ}
    {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsHermitian)
    (b : OrthonormalBasis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)))
    (d : Fin n → ℝ) (hd : Monotone d)
    (heig : ∀ i, A.toEuclideanLin (b i) = d i • b i) (i : Fin n) :
    ascendingEigenvalue hA i = d i := by
  have h := HDP.Matrix.antitone_eigenvalue_eq_ordered_of_eigenbasis hA
    (fun j => d j.rev) (b.reindex Fin.revPerm)
    (fun _ _ h => hd (Fin.rev_anti h)) (fun j => by simpa [Fin.revPerm] using heig j.rev)
  simpa only [ascendingEigenvalue, Fin.rev_rev] using (congrFun h i.rev).symm

end NumStability
