import ComputationalMathematics.Analysis.FunctionalCalculus.Resolvent.HermitianShift
import Mathlib.LinearAlgebra.Matrix.SchurComplement

/-!
# Resolvents of diagonal rank-one perturbations

The resolvent uses the sign convention `(A - z • 1)⁻¹`. Deleting the
perturbed coordinate gives the Schur complement governing the corresponding
diagonal entry.
-/

open Matrix

namespace NumStability

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] in
/-- A real shift of a single diagonal coordinate preserves Hermitian symmetry. -/
theorem isHermitian_add_diagonal_single {A : Matrix ι ι ℂ} (hA : A.IsHermitian)
    (i : ι) (t : ℝ) : (A + Matrix.diagonal (Pi.single i (t : ℂ))).IsHermitian := by
  apply hA.add
  rw [Matrix.isHermitian_diagonal_iff]
  intro j
  by_cases hj : j = i
  · subst j
    simp [IsSelfAdjoint]
  · simp [Pi.single_eq_of_ne hj, IsSelfAdjoint]

/-- The complex center of the diagonal resolvent for a perturbation at coordinate `i`. -/
def coordinateResolventCenter (A : Matrix ι ι ℂ) (i : ι) (z : ℂ) : ℂ :=
  let b : {j : ι // j ≠ i} → ℂ := fun j => A j i
  z - A i i + star b ⬝ᵥ ((A.submatrix Subtype.val Subtype.val - z • 1)⁻¹ *ᵥ b)

/-- The imaginary part of a Hermitian resolvent quadratic form is nonnegative
in the upper half-plane. -/
theorem im_star_dotProduct_hermitian_resolvent_mulVec_nonneg {A : Matrix ι ι ℂ}
    (hA : A.IsHermitian) {z : ℂ} (hz : 0 < z.im) (b : ι → ℂ) :
    0 ≤ (star b ⬝ᵥ ((A - z • 1)⁻¹ *ᵥ b)).im := by
  let D := A - z • (1 : Matrix ι ι ℂ)
  let x := D⁻¹ *ᵥ b
  have hD : IsUnit D := MatrixResolvent.isUnit_sub_smul_one hA hz.ne'
  have hx : D *ᵥ x = b := by
    rw [show x = D⁻¹ *ᵥ b from rfl, Matrix.mulVec_mulVec,
      Matrix.mul_nonsing_inv _ (D.isUnit_iff_isUnit_det.mp hD), Matrix.one_mulVec]
  have hdot : star x ⬝ᵥ x = ((∑ j, Complex.normSq (x j) : ℝ) : ℂ) := by
    simp [dotProduct, Complex.mul_conj, mul_comm]
  change 0 ≤ (star b ⬝ᵥ x).im
  calc
    0 ≤ z.im * ∑ j, Complex.normSq (x j) :=
      mul_nonneg hz.le (Finset.sum_nonneg fun j _ => Complex.normSq_nonneg (x j))
    _ = (star b ⬝ᵥ x).im := by
      rw [star_dotProduct, ← hx]
      change _ = (star (star x ⬝ᵥ ((A - z • 1) *ᵥ x))).im
      rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
        dotProduct_sub, dotProduct_smul, hdot]
      have him : (star x ⬝ᵥ A *ᵥ x).im = 0 := hA.im_star_dotProduct_mulVec_self x
      simp [Complex.mul_im, him]

/-- The center lies at least as high as the spectral parameter in the upper half-plane. -/
theorem le_im_coordinateResolventCenter {A : Matrix ι ι ℂ} (hA : A.IsHermitian)
    (i : ι) {z : ℂ} (hz : 0 < z.im) :
    z.im ≤ (coordinateResolventCenter A i z).im := by
  have hdiag : (A i i).im = 0 := by
    have h := congrArg Complex.im (hA.apply i i)
    simp at h
    linarith
  have hform := im_star_dotProduct_hermitian_resolvent_mulVec_nonneg
    (hA.submatrix (Subtype.val : {j : ι // j ≠ i} → ι)) hz (fun j => A j i)
  simpa [coordinateResolventCenter, hdiag] using add_le_add_left hform z.im

private theorem inv_apply_unit (S : Matrix Unit Unit ℂ) (hS : IsUnit S) :
    S⁻¹ () () = (S () ())⁻¹ := by
  have hdet := S.isUnit_iff_isUnit_det.mp hS
  have hval : S () () ≠ 0 := by simpa [Matrix.det_unique] using hdet.ne_zero
  apply (mul_eq_one_iff_eq_inv₀ hval).mp
  simpa [Matrix.mul_apply] using
    congrFun (congrFun (Matrix.nonsing_inv_mul S hdet) ()) ()

/-- The diagonal entry of the resolvent after a real perturbation of a single
coordinate is the reciprocal of the perturbation minus its complex center. -/
theorem diagonal_rankOne_resolvent {A : Matrix ι ι ℂ} (hA : A.IsHermitian)
    (i : ι) (t : ℝ) {z : ℂ} (hz : 0 < z.im) :
    (A + Matrix.diagonal (Pi.single i (t : ℂ)) - z • 1)⁻¹ i i =
      ((t : ℂ) - coordinateResolventCenter A i z)⁻¹ := by
  let κ := {j : ι // j ≠ i}
  let e : Unit ⊕ κ ≃ ι :=
    (Equiv.sumCongr (Equiv.ofUnique Unit ({i} : Set ι)) (Equiv.refl κ)).trans
      (Equiv.Set.sumCompl ({i} : Set ι))
  have he₁ (u : Unit) : e (Sum.inl u) = i := rfl
  have he₂ (j : κ) : e (Sum.inr j) = j := rfl
  let M := A + Matrix.diagonal (Pi.single i (t : ℂ)) - z • 1
  let P : Matrix Unit Unit ℂ := fun _ _ => A i i + (t : ℂ) - z
  let B : Matrix Unit κ ℂ := fun _ j => star (A j i)
  let C : Matrix κ Unit ℂ := fun j _ => A j i
  let D : Matrix κ κ ℂ := A.submatrix Subtype.val Subtype.val - z • 1
  have hblocks : M.submatrix e e = Matrix.fromBlocks P B C D := by
    ext a b
    rcases a with a | a <;> rcases b with b | b
    · simp [M, P, he₁]
    · simp [M, B, he₁, he₂, Ne.symm b.property, hA.apply]
    · simp [M, C, he₁, he₂, a.property]
    · have hinj : (a : ι) = (b : ι) ↔ a = b := Subtype.val_injective.eq_iff
      simp [M, D, he₂, Matrix.one_apply, Matrix.diagonal_apply, hinj, Pi.single_eq_of_ne a.property]
  have hM : IsUnit M := MatrixResolvent.isUnit_sub_smul_one
    (isHermitian_add_diagonal_single hA i t) hz.ne'
  have hD : IsUnit D := MatrixResolvent.isUnit_sub_smul_one
    (hA.submatrix Subtype.val) hz.ne'
  have hblockUnit : IsUnit (Matrix.fromBlocks P B C D) :=
    hblocks ▸ (Matrix.isUnit_submatrix_equiv e e).mpr hM
  letI : Invertible D := hD.invertible
  letI : Invertible (Matrix.fromBlocks P B C D) := hblockUnit.invertible
  letI : Invertible (P - B * ⅟D * C) := Matrix.invertibleOfFromBlocks₂₂Invertible P B C D
  have hentry := congrFun (congrFun (Matrix.invOf_fromBlocks₂₂_eq P B C D)
    (Sum.inl ())) (Sum.inl ())
  simp only [Matrix.fromBlocks_apply₁₁, Matrix.invOf_eq_nonsing_inv] at hentry
  have hMentry : M⁻¹ i i = (Matrix.fromBlocks P B C D)⁻¹ (Sum.inl ()) (Sum.inl ()) := by
    rw [← hblocks, Matrix.inv_submatrix_equiv]
    simp [he₁]
  have hscalar : (P - B * D⁻¹ * C) () () = (t : ℂ) - coordinateResolventCenter A i z := by
    simp only [Matrix.sub_apply, Matrix.mul_assoc, Matrix.mul_apply, P, B, C, D,
      coordinateResolventCenter, dotProduct, Matrix.mulVec, Pi.star_apply]
    ring
  calc
    M⁻¹ i i = (Matrix.fromBlocks P B C D)⁻¹ (Sum.inl ()) (Sum.inl ()) := hMentry
    _ = (P - B * D⁻¹ * C)⁻¹ () () := hentry
    _ = ((t : ℂ) - coordinateResolventCenter A i z)⁻¹ := by
      have hS : IsUnit (P - B * D⁻¹ * C) := by
        rw [← Matrix.invOf_eq_nonsing_inv]
        exact isUnit_of_invertible _
      rw [inv_apply_unit _ hS, hscalar]

end

end NumStability
