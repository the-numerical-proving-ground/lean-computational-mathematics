import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Principal-submatrix interlacing for Hermitian matrices

Deleting one coordinate preserves the Rayleigh form on vectors extended by zero.
Intersecting the appropriate spectral subspaces gives both interlacing
inequalities for decreasing eigenvalue lists, with multiplicity.
-/

open scoped BigOperators

namespace Matrix
namespace IsHermitian

variable {𝕜 : Type*} [RCLike 𝕜] {n : ℕ}

/-- The eigenvalues of a Hermitian matrix in decreasing order, with multiplicity. -/
noncomputable def orderedEigenvaluesFin {A : Matrix (Fin n) (Fin n) 𝕜}
    (hA : A.IsHermitian) : Fin n → ℝ :=
  (isHermitian_iff_isSymmetric.mp hA).eigenvalues finrank_euclideanSpace_fin

theorem antitone_orderedEigenvaluesFin {A : Matrix (Fin n) (Fin n) 𝕜}
    (hA : A.IsHermitian) : Antitone hA.orderedEigenvaluesFin :=
  (isHermitian_iff_isSymmetric.mp hA).eigenvalues_antitone finrank_euclideanSpace_fin

/-- The orthonormal eigenbasis corresponding to decreasing eigenvalues. -/
noncomputable def orderedEigenbasisFin {A : Matrix (Fin n) (Fin n) 𝕜}
    (hA : A.IsHermitian) : OrthonormalBasis (Fin n) 𝕜 (EuclideanSpace 𝕜 (Fin n)) :=
  (isHermitian_iff_isSymmetric.mp hA).eigenvectorBasis finrank_euclideanSpace_fin

private theorem rayleigh_eq_sum {A : Matrix (Fin n) (Fin n) 𝕜}
    (hA : A.IsHermitian) (x : EuclideanSpace 𝕜 (Fin n)) :
    RCLike.re (inner 𝕜 x (A.toEuclideanLin x)) =
      ∑ j, hA.orderedEigenvaluesFin j * ‖inner 𝕜 (hA.orderedEigenbasisFin j) x‖ ^ 2 := by
  rw [← hA.orderedEigenbasisFin.sum_inner_mul_inner, map_sum]
  apply Finset.sum_congr rfl
  intro j _
  let b := hA.orderedEigenbasisFin
  have hcoord := (isHermitian_iff_isSymmetric.mp hA).eigenvectorBasis_apply_self_apply
    finrank_euclideanSpace_fin x j
  change b.repr (A.toEuclideanLin x) j = (hA.orderedEigenvaluesFin j : 𝕜) * b.repr x j
    at hcoord
  rw [OrthonormalBasis.repr_apply_apply, OrthonormalBasis.repr_apply_apply] at hcoord
  change RCLike.re (inner 𝕜 x (b j) * inner 𝕜 (b j) (A.toEuclideanLin x)) = _
  rw [hcoord, mul_comm (hA.orderedEigenvaluesFin j : 𝕜), ← mul_assoc,
    RCLike.re_mul_ofReal, inner_mul_symm_re_eq_norm]
  rw [← inner_conj_symm x (b j), norm_mul, RCLike.norm_conj, ← pow_two, mul_comm]

private noncomputable def spectralSubspace (b : OrthonormalBasis (Fin n) 𝕜
    (EuclideanSpace 𝕜 (Fin n))) (s : Finset (Fin n)) :
    Submodule 𝕜 (EuclideanSpace 𝕜 (Fin n)) :=
  Submodule.span 𝕜 (⇑b '' (s : Set (Fin n)))

private theorem finrank_spectralSubspace (b : OrthonormalBasis (Fin n) 𝕜
    (EuclideanSpace 𝕜 (Fin n))) (s : Finset (Fin n)) :
    Module.finrank 𝕜 (spectralSubspace b s) = s.card := by
  classical
  have hli : LinearIndependent 𝕜 (fun k : {j // j ∈ s} => b k) :=
    (b.orthonormal.comp (fun k : {j // j ∈ s} => (k : Fin n))
      Subtype.val_injective).linearIndependent
  have hrange : Set.range (fun k : {j // j ∈ s} => b k) = ⇑b '' (s : Set (Fin n)) := by
    ext x
    constructor
    · rintro ⟨⟨j, hj⟩, rfl⟩
      exact ⟨j, hj, rfl⟩
    · rintro ⟨j, hj, rfl⟩
      exact ⟨⟨j, hj⟩, rfl⟩
  rw [spectralSubspace, ← hrange, finrank_span_eq_card hli, Fintype.card_coe]

private theorem inner_eq_zero_of_mem_spectralSubspace
    (b : OrthonormalBasis (Fin n) 𝕜 (EuclideanSpace 𝕜 (Fin n))) (s : Finset (Fin n))
    {x : EuclideanSpace 𝕜 (Fin n)} (hx : x ∈ spectralSubspace b s)
    {j : Fin n} (hj : j ∉ s) : inner 𝕜 (b j) x = 0 := by
  refine Submodule.span_induction (p := fun y _ => inner 𝕜 (b j) y = 0) ?_ ?_ ?_ ?_ hx
  · rintro y ⟨k, hk, rfl⟩
    have hjk : j ≠ k := by rintro rfl; exact hj hk
    rw [orthonormal_iff_ite.mp b.orthonormal j k, if_neg hjk]
  · exact inner_zero_right _
  · intro u v _ _ hu hv
    rw [inner_add_right, hu, hv, add_zero]
  · intro a u _ hu
    rw [inner_smul_right, hu, mul_zero]

private theorem mul_norm_sq_le_rayleigh {A : Matrix (Fin n) (Fin n) 𝕜}
    (hA : A.IsHermitian) (s : Finset (Fin n)) {t : ℝ}
    (hs : ∀ j ∈ s, t ≤ hA.orderedEigenvaluesFin j)
    {x : EuclideanSpace 𝕜 (Fin n)} (hx : x ∈ spectralSubspace hA.orderedEigenbasisFin s) :
    t * ‖x‖ ^ 2 ≤ RCLike.re (inner 𝕜 x (A.toEuclideanLin x)) := by
  rw [rayleigh_eq_sum hA, ← hA.orderedEigenbasisFin.sum_sq_norm_inner_right, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _
  by_cases hj : j ∈ s
  · exact mul_le_mul_of_nonneg_right (hs j hj) (sq_nonneg _)
  · simp [inner_eq_zero_of_mem_spectralSubspace _ _ hx hj]

private theorem rayleigh_le_mul_norm_sq {A : Matrix (Fin n) (Fin n) 𝕜}
    (hA : A.IsHermitian) (s : Finset (Fin n)) {t : ℝ}
    (hs : ∀ j ∈ s, hA.orderedEigenvaluesFin j ≤ t)
    {x : EuclideanSpace 𝕜 (Fin n)} (hx : x ∈ spectralSubspace hA.orderedEigenbasisFin s) :
    RCLike.re (inner 𝕜 x (A.toEuclideanLin x)) ≤ t * ‖x‖ ^ 2 := by
  rw [rayleigh_eq_sum hA, ← hA.orderedEigenbasisFin.sum_sq_norm_inner_right, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _
  by_cases hj : j ∈ s
  · exact mul_le_mul_of_nonneg_right (hs j hj) (sq_nonneg _)
  · simp [inner_eq_zero_of_mem_spectralSubspace _ _ hx hj]

private theorem exists_nonzero_mem_of_finrank_lt {E F : Submodule 𝕜 (EuclideanSpace 𝕜 (Fin n))}
    (h : n < Module.finrank 𝕜 E + Module.finrank 𝕜 F) :
    ∃ x, x ∈ E ∧ x ∈ F ∧ x ≠ 0 := by
  have hinf : E ⊓ F ≠ ⊥ := by
    intro heq
    have hdisj : Disjoint E F := by rw [disjoint_iff_inf_le, heq]
    have hle := Submodule.finrank_add_finrank_le_of_disjoint hdisj
    rw [finrank_euclideanSpace_fin] at hle
    omega
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hinf
  exact ⟨x, hx.1, hx.2, hx0⟩

/-- A uniform upper bound on the difference of the Rayleigh forms bounds
each difference of the ordered eigenvalues. -/
theorem orderedEigenvaluesFin_sub_le_of_rayleigh {A B : Matrix (Fin n) (Fin n) 𝕜}
    (hA : A.IsHermitian) (hB : B.IsHermitian) (j : Fin n) {d : ℝ}
    (hd : ∀ x : EuclideanSpace 𝕜 (Fin n),
      RCLike.re (inner 𝕜 x (A.toEuclideanLin x)) ≤
        RCLike.re (inner 𝕜 x (B.toEuclideanLin x)) + d * ‖x‖ ^ 2) :
    hA.orderedEigenvaluesFin j - hB.orderedEigenvaluesFin j ≤ d := by
  let E := spectralSubspace hA.orderedEigenbasisFin (Finset.Iic j)
  let F := spectralSubspace hB.orderedEigenbasisFin (Finset.Ici j)
  have hdim : n < Module.finrank 𝕜 E + Module.finrank 𝕜 F := by
    change n < Module.finrank 𝕜 (spectralSubspace _ _) +
      Module.finrank 𝕜 (spectralSubspace _ _)
    rw [finrank_spectralSubspace, finrank_spectralSubspace, Fin.card_Iic, Fin.card_Ici]
    have := j.isLt
    omega
  obtain ⟨x, hxE, hxF, hx0⟩ := exists_nonzero_mem_of_finrank_lt hdim
  have hlower := mul_norm_sq_le_rayleigh hA (Finset.Iic j)
    (fun k hk => hA.antitone_orderedEigenvaluesFin (Finset.mem_Iic.mp hk)) hxE
  have hupper := rayleigh_le_mul_norm_sq hB (Finset.Ici j)
    (fun k hk => hB.antitone_orderedEigenvaluesFin (Finset.mem_Ici.mp hk)) hxF
  apply le_of_mul_le_mul_right _ (sq_pos_of_ne_zero (norm_ne_zero_iff.mpr hx0))
  linarith [hlower, hd x, hupper, sub_mul (hA.orderedEigenvaluesFin j)
    (hB.orderedEigenvaluesFin j) (‖x‖ ^ 2)]

/-- The Mathlib basis label for a decreasing spectral rank. -/
noncomputable def eigenbasisIndexFin (n : ℕ) : Fin n ≃ Fin n :=
  (Fin.castOrderIso (Fintype.card_fin n).symm).toEquiv.trans
    (Fintype.equivOfCardEq (Fintype.card_fin _))

private theorem eigenvalues_finrank_cast {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
    {T : E →ₗ[𝕜] E} (hT : T.IsSymmetric) {m n : ℕ}
    (hm : Module.finrank 𝕜 E = m) (hn : Module.finrank 𝕜 E = n) (j : Fin n) :
    hT.eigenvalues hm (Fin.cast (hn.symm.trans hm) j) = hT.eigenvalues hn j := by
  subst m
  subst n
  rfl

theorem eigenvalues_eigenbasisIndexFin {A : Matrix (Fin n) (Fin n) 𝕜}
    (hA : A.IsHermitian) (j : Fin n) :
    hA.eigenvalues (eigenbasisIndexFin n j) = hA.orderedEigenvaluesFin j := by
  rw [eigenvalues, eigenbasisIndexFin, Equiv.trans_apply, Equiv.symm_apply_apply]
  exact eigenvalues_finrank_cast ..

private noncomputable def insertZero (i : Fin (n + 1)) :
    EuclideanSpace 𝕜 (Fin n) →ₗ[𝕜] EuclideanSpace 𝕜 (Fin (n + 1)) where
  toFun x := WithLp.toLp 2 (i.insertNth 0 x)
  map_add' x y := by
    ext j
    cases j using Fin.succAboveCases i <;> simp
  map_smul' a x := by
    ext j
    cases j using Fin.succAboveCases i <;> simp

@[simp] private theorem insertZero_same (i : Fin (n + 1)) (x : EuclideanSpace 𝕜 (Fin n)) :
    insertZero i x i = 0 :=
  by exact @Fin.insertNth_apply_same n (fun _ => 𝕜) i 0 (fun j => x j)

@[simp] private theorem insertZero_succAbove (i : Fin (n + 1)) (x : EuclideanSpace 𝕜 (Fin n))
    (j : Fin n) : insertZero i x (i.succAbove j) = x j :=
  by exact @Fin.insertNth_apply_succAbove n (fun _ => 𝕜) i 0 (fun j => x j) j

private theorem insertZero_injective (i : Fin (n + 1)) :
    Function.Injective (insertZero (𝕜 := 𝕜) i) := by
  intro x y h
  ext j
  simpa using congrArg (fun z : EuclideanSpace 𝕜 (Fin (n + 1)) => z (i.succAbove j)) h

private theorem norm_insertZero_sq (i : Fin (n + 1)) (x : EuclideanSpace 𝕜 (Fin n)) :
    ‖insertZero i x‖ ^ 2 = ‖x‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, Fin.sum_univ_succAbove _ i]
  simp

private theorem rayleigh_insertZero (A : Matrix (Fin (n + 1)) (Fin (n + 1)) 𝕜)
    (i : Fin (n + 1)) (x : EuclideanSpace 𝕜 (Fin n)) :
    inner 𝕜 (insertZero i x) (A.toEuclideanLin (insertZero i x)) =
      inner 𝕜 x ((A.submatrix i.succAbove i.succAbove).toEuclideanLin x) := by
  rw [PiLp.inner_apply, PiLp.inner_apply, Fin.sum_univ_succAbove _ i]
  simp only [insertZero_same, inner_zero_left, zero_add, insertZero_succAbove,
    Matrix.toLpLin_apply]
  apply Finset.sum_congr rfl
  intro j _
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_succAbove _ i, insertZero_same,
    mul_zero, zero_add, insertZero_succAbove, Matrix.submatrix_apply]

/-- Deleting one row and the corresponding column interlaces the ordered eigenvalues. -/
theorem orderedEigenvaluesFin_submatrix_interlace {A : Matrix (Fin (n + 1)) (Fin (n + 1)) 𝕜}
    (hA : A.IsHermitian) (i : Fin (n + 1)) (j : Fin n) :
    hA.orderedEigenvaluesFin j.succ ≤ (hA.submatrix i.succAbove).orderedEigenvaluesFin j ∧
      (hA.submatrix i.succAbove).orderedEigenvaluesFin j ≤ hA.orderedEigenvaluesFin j.castSucc := by
  let hB := hA.submatrix i.succAbove
  let f := insertZero (𝕜 := 𝕜) i
  constructor
  · let E := spectralSubspace hA.orderedEigenbasisFin (Finset.Iic j.succ)
    let F := spectralSubspace hB.orderedEigenbasisFin (Finset.Ici j)
    have hdim : n + 1 < Module.finrank 𝕜 E + Module.finrank 𝕜 (F.map f) := by
      rw [(Submodule.equivMapOfInjective f (insertZero_injective i) F).finrank_eq.symm]
      change n + 1 < Module.finrank 𝕜 (spectralSubspace _ _) +
        Module.finrank 𝕜 (spectralSubspace _ _)
      rw [finrank_spectralSubspace, finrank_spectralSubspace, Fin.card_Iic, Fin.card_Ici]
      have := j.isLt
      simp only [Fin.val_succ]
      omega
    obtain ⟨y, hyE, ⟨x, hxF, rfl⟩, hy0⟩ := exists_nonzero_mem_of_finrank_lt hdim
    have hlower := mul_norm_sq_le_rayleigh hA (Finset.Iic j.succ)
      (fun k hk => hA.antitone_orderedEigenvaluesFin (Finset.mem_Iic.mp hk)) hyE
    have hupper := rayleigh_le_mul_norm_sq hB (Finset.Ici j)
      (fun k hk => hB.antitone_orderedEigenvaluesFin (Finset.mem_Ici.mp hk)) hxF
    change hA.orderedEigenvaluesFin j.succ * ‖insertZero i x‖ ^ 2 ≤ _ at hlower
    rw [norm_insertZero_sq, rayleigh_insertZero] at hlower
    exact le_of_mul_le_mul_right (hlower.trans hupper)
      (sq_pos_of_ne_zero (norm_ne_zero_iff.mpr (by rintro rfl; exact hy0 (map_zero f))))
  · let E := spectralSubspace hA.orderedEigenbasisFin (Finset.Ici j.castSucc)
    let F := spectralSubspace hB.orderedEigenbasisFin (Finset.Iic j)
    have hdim : n + 1 < Module.finrank 𝕜 E + Module.finrank 𝕜 (F.map f) := by
      rw [(Submodule.equivMapOfInjective f (insertZero_injective i) F).finrank_eq.symm]
      change n + 1 < Module.finrank 𝕜 (spectralSubspace _ _) +
        Module.finrank 𝕜 (spectralSubspace _ _)
      rw [finrank_spectralSubspace, finrank_spectralSubspace, Fin.card_Ici, Fin.card_Iic]
      have := j.isLt
      simp only [Fin.val_castSucc]
      omega
    obtain ⟨y, hyE, ⟨x, hxF, rfl⟩, hy0⟩ := exists_nonzero_mem_of_finrank_lt hdim
    have hupper := rayleigh_le_mul_norm_sq hA (Finset.Ici j.castSucc)
      (fun k hk => hA.antitone_orderedEigenvaluesFin (Finset.mem_Ici.mp hk)) hyE
    have hlower := mul_norm_sq_le_rayleigh hB (Finset.Iic j)
      (fun k hk => hB.antitone_orderedEigenvaluesFin (Finset.mem_Iic.mp hk)) hxF
    change _ ≤ hA.orderedEigenvaluesFin j.castSucc * ‖insertZero i x‖ ^ 2 at hupper
    rw [norm_insertZero_sq, rayleigh_insertZero] at hupper
    exact le_of_mul_le_mul_right (hlower.trans hupper)
      (sq_pos_of_ne_zero (norm_ne_zero_iff.mpr (by rintro rfl; exact hy0 (map_zero f))))

end IsHermitian
end Matrix
