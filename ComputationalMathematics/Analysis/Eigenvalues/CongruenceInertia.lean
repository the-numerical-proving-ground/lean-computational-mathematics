import ComputationalMathematics.Analysis.Eigenvalues.CourantFischer
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Negative inertia under real congruence

Strictly negative weights determine the maximal dimension of a negative
quadratic subspace. Projection onto the negative coordinates is injective on
such a subspace; zero and repeated weights require no exceptional cases.
-/
namespace NumStability.CongruenceInertia
noncomputable section
open scoped BigOperators RealInnerProductSpace

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- The weighted real sum of coordinate squares. -/
private def weightedSquareSum (w : ι → ℝ) (x : ι → ℝ) : ℝ := ∑ i, w i * (x i) ^ 2

/-- The strictly negative index, with zero weights excluded. -/
def negativeCount (w : ι → ℝ) : ℕ := by
  classical
  exact Fintype.card {i // w i < 0}

/-- Embed the negative coordinate space by setting all other coordinates zero. -/
def negativeEmbed (w : ι → ℝ) : ({i // w i < 0} → ℝ) →ₗ[ℝ] (ι → ℝ) := by
  classical
  exact {
    toFun := fun x i => if h : w i < 0 then x ⟨i, h⟩ else 0
    map_add' := by intro x y; ext i; by_cases h : w i < 0 <;> simp [h]
    map_smul' := by intro a x; ext i; by_cases h : w i < 0 <;> simp [h] }

/-- Restrict a vector to the strictly negative coordinates. -/
def negativeProject (w : ι → ℝ) : (ι → ℝ) →ₗ[ℝ] ({i // w i < 0} → ℝ) where
  toFun x i := x i.val
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem weightedSquareSum_negativeEmbed_neg (w : ι → ℝ)
    (x : {i // w i < 0} → ℝ) (hx : x ≠ 0) :
    weightedSquareSum w (negativeEmbed w x) < 0 := by
  classical
  unfold weightedSquareSum
  apply Finset.sum_neg'
  · intro i hi
    by_cases h : w i < 0
    · exact mul_nonpos_of_nonpos_of_nonneg h.le (sq_nonneg _)
    · simp [negativeEmbed, h]
  · obtain ⟨i, hi⟩ := Function.ne_iff.mp hx
    have hxi : x i ≠ 0 := hi
    refine ⟨i.val, Finset.mem_univ _, ?_⟩
    simpa only [negativeEmbed, LinearMap.coe_mk, AddHom.coe_mk, dif_pos i.property] using
      mul_neg_of_neg_of_pos i.property (sq_pos_of_ne_zero hxi)

private theorem weightedSquareSum_nonneg_of_project_eq_zero (w : ι → ℝ) (x : ι → ℝ)
    (hx : negativeProject w x = 0) : 0 ≤ weightedSquareSum w x := by
  classical
  apply Finset.sum_nonneg
  intro i hi
  by_cases h : w i < 0
  · have hxi : x i = 0 := congrFun hx ⟨i, h⟩
    simp [hxi]
  · exact mul_nonneg (le_of_not_gt h) (sq_nonneg _)

/-- Projection onto the negative coordinates is injective on every subspace
where the weighted quadratic form is strictly negative away from zero. -/
private theorem negativeProject_injective_on_subspace (w : ι → ℝ)
    (S : Submodule ℝ (ι → ℝ))
    (hS : ∀ x ∈ S, x ≠ 0 → weightedSquareSum w x < 0) :
    Function.Injective ((negativeProject w).comp S.subtype) := by
  have hz : ∀ x : S, ((negativeProject w).comp S.subtype) x = 0 → x = 0 := by
    intro x hx
    by_contra hne
    have hxne : (x : ι → ℝ) ≠ 0 := by
      intro h
      exact hne (Subtype.ext h)
    have hn := weightedSquareSum_nonneg_of_project_eq_zero w x hx
    have hneg := hS x x.property hxne
    linarith
  intro x y hxy
  have hzero : ((negativeProject w).comp S.subtype) (x - y) = 0 := by
    rw [map_sub, hxy, sub_self]
  exact sub_eq_zero.mp (hz (x - y) hzero)

/-- The negative coordinate count bounds the dimension of every negative
quadratic subspace. This is the upper half of the maximal-dimension property. -/
private theorem finrank_le_negativeCount (w : ι → ℝ) (S : Submodule ℝ (ι → ℝ))
    (hS : ∀ x ∈ S, x ≠ 0 → weightedSquareSum w x < 0) :
    Module.finrank ℝ S ≤ negativeCount w := by
  classical
  simpa [negativeCount] using LinearMap.finrank_le_finrank_of_injective
    (negativeProject_injective_on_subspace w S hS)

omit [Fintype ι] in
theorem negativeEmbed_injective (w : ι → ℝ) : Function.Injective (negativeEmbed w) := by
  classical
  intro x y hxy
  funext i
  have hi := congrFun hxy i.val
  simpa only [negativeEmbed, LinearMap.coe_mk, AddHom.coe_mk, dif_pos i.property] using hi

/-- The negative coordinate space attains the dimension bound, so
`negativeCount` is exactly the maximal negative-subspace dimension. -/
private theorem exists_negative_subspace (w : ι → ℝ) :
    ∃ S : Submodule ℝ (ι → ℝ), Module.finrank ℝ S = negativeCount w ∧
      ∀ x ∈ S, x ≠ 0 → weightedSquareSum w x < 0 := by
  classical
  refine ⟨(negativeEmbed w).range, ?_, ?_⟩
  · simpa [negativeCount] using LinearMap.finrank_range_of_inj (negativeEmbed_injective w)
  · intro x hx hxne
    obtain ⟨y, rfl⟩ := hx
    apply weightedSquareSum_negativeEmbed_neg w y
    intro hy
    apply hxne
    rw [hy, map_zero]

/-- The negative index cannot decrease under a quadratic-form preserving
linear map. Its negative-coordinate projection is proved injective. -/
private theorem negativeCount_le_of_quadratic_map (w : ι → ℝ) (v : κ → ℝ)
    (f : (ι → ℝ) →ₗ[ℝ] (κ → ℝ))
    (hf : ∀ x, weightedSquareSum v (f x) = weightedSquareSum w x) :
    negativeCount w ≤ negativeCount v := by
  classical
  let g := (negativeProject v).comp (f.comp (negativeEmbed w))
  have hz : ∀ x, g x = 0 → x = 0 := by
    intro x hx
    by_contra hne
    have hneg := weightedSquareSum_negativeEmbed_neg w x hne
    have hn := weightedSquareSum_nonneg_of_project_eq_zero v (f (negativeEmbed w x)) hx
    rw [hf] at hn
    linarith
  have hg : Function.Injective g := by
    intro x y hxy
    have hzero : g (x - y) = 0 := by rw [map_sub, hxy, sub_self]
    exact sub_eq_zero.mp (hz (x - y) hzero)
  simpa [negativeCount] using LinearMap.finrank_le_finrank_of_injective hg

/-- Sylvester's negative-inertia equality for diagonal forms, including zero
weights and arbitrary multiplicities. -/
private theorem negativeCount_eq_of_equiv (w : ι → ℝ) (v : κ → ℝ)
    (e : (ι → ℝ) ≃ₗ[ℝ] (κ → ℝ))
    (he : ∀ x, weightedSquareSum v (e x) = weightedSquareSum w x) :
    negativeCount w = negativeCount v := by
  apply Nat.le_antisymm
  · exact negativeCount_le_of_quadratic_map w v e.toLinearMap he
  · apply negativeCount_le_of_quadratic_map v w e.symm.toLinearMap
    intro x
    simpa using (he (e.symm x)).symm

/-- Eigenbasis coordinates as an ordinary real coordinate linear equivalence. -/
def eigenCoordinateEquiv {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsHermitian) :
    EuclideanSpace ℝ (Fin n) ≃ₗ[ℝ] (Fin n → ℝ) :=
  (hermitianOrderedEigenbasis hA).repr.toLinearEquiv.trans
    (WithLp.linearEquiv 2 ℝ (Fin n → ℝ))

private theorem weightedSquareSum_eigenCoordinate {n : ℕ}
    {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsHermitian)
    (x : EuclideanSpace ℝ (Fin n)) :
    weightedSquareSum (hermitianOrderedEigenvalue hA) (eigenCoordinateEquiv hA x) =
      matrixRayleighForm A x := by
  exact (matrixRayleighForm_eq_sum hA x).symm

/-- The number of strictly negative eigenvalues is invariant under an actual
linear equivalence preserving the two real Rayleigh forms. -/
theorem negative_eigenvalue_count_eq_of_rayleigh_equiv {n : ℕ}
    {A B : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsHermitian) (hB : B.IsHermitian)
    (e : EuclideanSpace ℝ (Fin n) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin n))
    (he : ∀ x, matrixRayleighForm B (e x) = matrixRayleighForm A x) :
    negativeCount (hermitianOrderedEigenvalue hA) =
      negativeCount (hermitianOrderedEigenvalue hB) := by
  let ec := (eigenCoordinateEquiv hA).symm.trans (e.trans (eigenCoordinateEquiv hB))
  apply negativeCount_eq_of_equiv _ _ ec
  intro x
  change weightedSquareSum (hermitianOrderedEigenvalue hB)
    (eigenCoordinateEquiv hB (e ((eigenCoordinateEquiv hA).symm x))) = _
  rw [weightedSquareSum_eigenCoordinate, he]
  rw [← weightedSquareSum_eigenCoordinate hA]
  simp

private theorem rayleigh_toLp {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) :
    matrixRayleighForm A (WithLp.toLp 2 x) = x ⬝ᵥ A.mulVec x := by
  simp only [matrixRayleighForm, Matrix.toLpLin_apply, PiLp.inner_apply]
  change (∑ i, A.mulVec x i * x i) = x ⬝ᵥ A.mulVec x
  exact dotProduct_comm _ _

private theorem quadratic_congruence {n : ℕ}
    (L B : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) :
    x ⬝ᵥ (L * B * L.transpose).mulVec x =
      (L.transpose.mulVec x) ⬝ᵥ B.mulVec (L.transpose.mulVec x) := by
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec]
  have htrans : Matrix.vecMul x L = L.transpose.mulVec x := by
    simpa only [Matrix.transpose_transpose] using Matrix.vecMul_transpose L.transpose x
  rw [htrans]

/-- An invertible matrix and its explicitly stored inverse induce the transpose
coordinate equivalence used in a congruence. -/
def transposeCongruenceEquiv {n : ℕ} (L : (Matrix (Fin n) (Fin n) ℝ)ˣ) :
    (Fin n → ℝ) ≃ₗ[ℝ] (Fin n → ℝ) where
  toLinearMap := Matrix.toLin' (L.val.transpose)
  invFun := fun x => (↑(L⁻¹) : Matrix (Fin n) (Fin n) ℝ).transpose.mulVec x
  left_inv := by
    intro x
    change ((↑(L⁻¹) : Matrix (Fin n) (Fin n) ℝ).transpose).mulVec (L.val.transpose.mulVec x) = x
    rw [Matrix.mulVec_mulVec, ← Matrix.transpose_mul]
    simp
  right_inv := by
    intro x
    change L.val.transpose.mulVec (((↑(L⁻¹) : Matrix (Fin n) (Fin n) ℝ).transpose).mulVec x) = x
    rw [Matrix.mulVec_mulVec, ← Matrix.transpose_mul]
    simp

/-- Sylvester's negative-inertia law for invertible matrix congruence. Zeros,
repeated eigenvalues and indefinite matrices are all included. -/
theorem negative_eigenvalue_count_eq_congruence {n : ℕ}
    {A B : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsHermitian) (hB : B.IsHermitian)
    (L : (Matrix (Fin n) (Fin n) ℝ)ˣ)
    (hcong : A = L.val * B * L.val.transpose) :
    negativeCount (hermitianOrderedEigenvalue hA) =
      negativeCount (hermitianOrderedEigenvalue hB) := by
  let c := WithLp.linearEquiv 2 ℝ (Fin n → ℝ)
  let e := c.trans ((transposeCongruenceEquiv L).trans c.symm)
  apply negative_eigenvalue_count_eq_of_rayleigh_equiv hA hB e
  intro x
  obtain ⟨y, rfl⟩ := c.symm.surjective x
  change matrixRayleighForm B (WithLp.toLp 2 (L.val.transpose.mulVec y)) =
    matrixRayleighForm A (WithLp.toLp 2 y)
  rw [rayleigh_toLp, rayleigh_toLp, hcong, quadratic_congruence]

/-- The diagonal form itself has exactly its coordinate negative index. -/
theorem negative_eigenvalue_count_diagonal {n : ℕ} (d : Fin n → ℝ) :
    negativeCount (hermitianOrderedEigenvalue (Matrix.isHermitian_diagonal d)) = negativeCount d := by
  let hD := Matrix.isHermitian_diagonal d
  let c := WithLp.linearEquiv 2 ℝ (Fin n → ℝ)
  let e := (eigenCoordinateEquiv hD).symm.trans c
  have hdiag : ∀ y : EuclideanSpace ℝ (Fin n),
      matrixRayleighForm (Matrix.diagonal d) y = weightedSquareSum d (c y) := by
    intro y
    obtain ⟨z, rfl⟩ := c.symm.surjective y
    rw [rayleigh_toLp]
    change z ⬝ᵥ (Matrix.diagonal d).mulVec z = weightedSquareSum d z
    simp only [Matrix.mulVec_diagonal, dotProduct, weightedSquareSum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  apply negativeCount_eq_of_equiv _ _ e
  intro x
  change weightedSquareSum d (c ((eigenCoordinateEquiv hD).symm x)) = _
  rw [← hdiag, ← weightedSquareSum_eigenCoordinate hD]
  simp

/-- An invertible LDLᵀ factorization determines the number of strictly
negative eigenvalues. The diagonal may contain zeros; no nonzero-diagonal,
positive-definite, irreducibility or simple-spectrum premise is needed. -/
theorem negative_eigenvalue_count_eq_diagonal_congruence {n : ℕ}
    {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsHermitian)
    (L : (Matrix (Fin n) (Fin n) ℝ)ˣ) (d : Fin n → ℝ)
    (hfactor : A = L.val * Matrix.diagonal d * L.val.transpose) :
    negativeCount (hermitianOrderedEigenvalue hA) = negativeCount d :=
  (negative_eigenvalue_count_eq_congruence hA (Matrix.isHermitian_diagonal d) L hfactor).trans
    (negative_eigenvalue_count_diagonal d)

/-- Finset-cardinality form of the LDLᵀ sign count, directly suited to a
stored-pivot list. Strict negativity excludes zero eigenvalues and pivots. -/
theorem card_negative_eigenvalue_eq_card_negative_diagonal {n : ℕ}
    {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsHermitian)
    (L : (Matrix (Fin n) (Fin n) ℝ)ˣ) (d : Fin n → ℝ)
    (hfactor : A = L.val * Matrix.diagonal d * L.val.transpose) :
    Finset.card {i | hermitianOrderedEigenvalue hA i < 0} =
      Finset.card {i | d i < 0} := by
  classical
  simpa only [negativeCount, Fintype.card_subtype] using
    negative_eigenvalue_count_eq_diagonal_congruence hA L d hfactor

/-- The same strict sign count after the explicit `Fin.rev` conversion to
ascending eigenvalue indices. -/
theorem card_negative_ascending_eigenvalue_eq_card_negative_diagonal {n : ℕ}
    {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsHermitian)
    (L : (Matrix (Fin n) (Fin n) ℝ)ˣ) (d : Fin n → ℝ)
    (hfactor : A = L.val * Matrix.diagonal d * L.val.transpose) :
    Finset.card {i : Fin n | hermitianOrderedEigenvalue hA i.rev < 0} =
      Finset.card {i | d i < 0} := by
  classical
  have hrev : Finset.card {i : Fin n | hermitianOrderedEigenvalue hA i.rev < 0} =
      Finset.card {i | hermitianOrderedEigenvalue hA i < 0} := by
    apply Finset.card_bij (fun i _ => i.rev)
    · intro i hi
      simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hi
    · intro i hi j hj hij
      have h := congrArg Fin.rev hij
      simpa using h
    · intro j hj
      refine ⟨j.rev, ?_, ?_⟩
      · simpa using hj
      · simp
  exact hrev.trans (card_negative_eigenvalue_eq_card_negative_diagonal hA L d hfactor)

/-- A matrix argument with an explicit `IsUnit` certificate can be used
directly, without replacing the factorization's matrix by a unit wrapper. -/
theorem card_negative_eigenvalue_eq_of_isUnit {n : ℕ}
    {A L : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsHermitian) (hL : IsUnit L)
    (d : Fin n → ℝ) (hfactor : A = L * Matrix.diagonal d * L.transpose) :
    Finset.card {i | hermitianOrderedEigenvalue hA i < 0} =
      Finset.card {i | d i < 0} := by
  obtain ⟨u, rfl⟩ := hL
  exact card_negative_eigenvalue_eq_card_negative_diagonal hA u d hfactor

end
end NumStability.CongruenceInertia
