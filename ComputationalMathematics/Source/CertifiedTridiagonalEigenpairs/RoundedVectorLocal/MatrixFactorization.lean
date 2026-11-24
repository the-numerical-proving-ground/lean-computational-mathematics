import Mathlib.Algebra.Group.Pi.Units
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic.Ring
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.RingTheory.Nilpotent.Basic

namespace NumStability.CertifiedTridiagonalEigenpairs

open scoped Matrix

section RootedFactorization

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The strictly triangular part in a rooted elimination. A non-root column
is supported only in the row of its parent. -/
noncomputable def rootedEliminationPart (r : ι) (parent : ι → ι)
    (β d : ι → ℂ) : Matrix ι ι ℂ :=
  fun i j => if j ≠ r ∧ parent j = i then β j / d j else 0

/-- The symmetric matrix with the supplied diagonal and offdiagonal
coefficients attached to the non-root columns. -/
noncomputable def rootedSymmetricMatrix (r : ι) (parent : ι → ι)
    (β D : ι → ℂ) : Matrix ι ι ℂ :=
  fun i j => if i = j then D i else
    (if j ≠ r ∧ parent j = i then β j else 0) +
      (if i ≠ r ∧ parent i = j then β i else 0)

private theorem rooted_elimination_nilpotent (r : ι) (parent : ι → ι) (β d : ι → ℂ)
    (rank : ι → ℕ) (bound : ℕ) (hbound : ∀ i, rank i < bound)
    (hparent : ∀ j ≠ r, rank (parent j) + 1 = rank j) :
    IsNilpotent (rootedEliminationPart r parent β d) := by
  let N := rootedEliminationPart r parent β d
  have hzero (k : ℕ) (i j : ι) (hij : rank j ≠ rank i + k) : (N ^ k) i j = 0 := by
    induction k generalizing i j with
    | zero =>
      have hin : i ≠ j := by intro he; apply hij; simp [he]
      simp [Matrix.one_apply_ne hin]
    | succ k ih =>
      rw [pow_succ, Matrix.mul_apply]
      refine Finset.sum_eq_zero (fun u _ => ?_)
      by_cases hu : j ≠ r ∧ parent j = u
      · have hru := hparent j hu.1
        rw [hu.2] at hru
        have hneq : rank u ≠ rank i + k := by omega
        simp [ih i u hneq]
      · simp [N, rootedEliminationPart, hu]
  exact ⟨bound, Matrix.ext fun i j => hzero bound i j (by have := hbound j; omega)⟩

/-- Rooted exact elimination reconstructs the symmetric matrix when each
stored pivot equals the corresponding diagonal minus its child corrections. -/
theorem rootedElimination_factor
    (r : ι) (parent : ι → ι) (β d D : ι → ℂ) (hd : ∀ i, d i ≠ 0)
    (hparent : ∀ j ≠ r, parent j ≠ j)
    (hdiag : ∀ i, D i = d i + ∑ j, if j ≠ r ∧ parent j = i then β j ^ 2 / d j else 0) :
    let L := 1 + rootedEliminationPart r parent β d
    rootedSymmetricMatrix r parent β D = L * Matrix.diagonal d * Lᵀ := by
  let N := rootedEliminationPart r parent β d
  let H : Matrix ι ι ℂ := Matrix.diagonal d
  have hcross (i j : ι) :
      (N * H) i j = if j ≠ r ∧ parent j = i then β j else 0 := by
    rw [Matrix.mul_diagonal]
    by_cases hij : j ≠ r ∧ parent j = i
    · simp [N, rootedEliminationPart, hij, div_mul_cancel₀ _ (hd j)]
    · simp [N, rootedEliminationPart, hij]
  have hcross' (i j : ι) :
      (H * Nᵀ) i j = if i ≠ r ∧ parent i = j then β i else 0 := by
    rw [Matrix.diagonal_mul, Matrix.transpose_apply, mul_comm]
    simpa only [Matrix.mul_diagonal, H] using hcross j i
  have hquad (i j : ι) :
      (N * H * Nᵀ) i j =
        if i = j then ∑ u, if u ≠ r ∧ parent u = i then β u ^ 2 / d u else 0 else 0 := by
    rw [Matrix.mul_apply]
    by_cases hij : i = j
    · subst j
      rw [if_pos rfl]
      refine Finset.sum_congr rfl fun u _ => ?_
      rw [hcross, Matrix.transpose_apply]
      by_cases hu : u ≠ r ∧ parent u = i
      · simp [N, rootedEliminationPart, hu]
        ring
      · simp [hu]
    · rw [if_neg hij]
      refine Finset.sum_eq_zero fun u _ => ?_
      rw [hcross, Matrix.transpose_apply]
      by_cases hu : u ≠ r ∧ parent u = i
      · simp [N, rootedEliminationPart, hu, hij]
      · simp [hu]
  change rootedSymmetricMatrix r parent β D = (1 + N) * H * (1 + N)ᵀ
  rw [Matrix.transpose_add, Matrix.transpose_one, add_mul, mul_add, mul_one, one_mul,
    add_mul]
  apply Matrix.ext
  intro i j
  simp only [Matrix.add_apply, hcross, hcross', hquad, rootedSymmetricMatrix]
  by_cases hij : i = j
  · subst j
    have hn : ¬ (i ≠ r ∧ parent i = i) := fun h => (hparent i h.1) h.2
    simp [hn, H, hdiag]
  · simp [hij, H]

/-- The root diagonal of the inverse of a rooted exact factorization is the
inverse of the final pivot. The rank order makes the elimination factor a unit. -/
theorem rootedElimination_inv_apply
    (r : ι) (parent : ι → ι) (β d : ι → ℂ) (hd : ∀ i, d i ≠ 0)
    (rank : ι → ℕ) (bound : ℕ) (hbound : ∀ i, rank i < bound)
    (hparent : ∀ j ≠ r, rank (parent j) + 1 = rank j) :
    let L := 1 + rootedEliminationPart r parent β d
    IsUnit (L * Matrix.diagonal d * Lᵀ) ∧
      (L * Matrix.diagonal d * Lᵀ)⁻¹ r r = (d r)⁻¹ := by
  let L := 1 + rootedEliminationPart r parent β d
  let H : Matrix ι ι ℂ := Matrix.diagonal d
  have hL : IsUnit L := (rooted_elimination_nilpotent r parent β d rank bound hbound hparent).isUnit_one_add
  have hH : IsUnit H := Matrix.isUnit_diagonal.mpr (Pi.isUnit_iff.mpr (fun i => isUnit_iff_ne_zero.mpr (hd i)))
  have hLT : IsUnit Lᵀ := (Matrix.isUnit_transpose L).mpr hL
  refine ⟨(hL.mul hH).mul hLT, ?_⟩
  let e : ι → ℂ := Pi.single r 1
  have hLe : L *ᵥ e = e := by
    funext i
    change (L *ᵥ Pi.single r 1) i = (Pi.single r (1 : ℂ) : ι → ℂ) i
    rw [Matrix.mulVec_single_one]
    by_cases h : i = r
    · subst i
      simp [L, rootedEliminationPart, Pi.single_eq_same]
    · simp [L, rootedEliminationPart, Matrix.one_apply_ne h, Pi.single_eq_of_ne h]
  have hLinv : L⁻¹ *ᵥ e = e := by
    calc
      _ = L⁻¹ *ᵥ (L *ᵥ e) := congrArg _ hLe.symm
      _ = _ := by
        rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ ((L.isUnit_iff_isUnit_det).mp hL),
          Matrix.one_mulVec]
  have hcol (i : ι) : L⁻¹ i r = e i := by
    have hi := congrFun hLinv i
    exact (congrFun (Matrix.mulVec_single_one L⁻¹ r) i).symm.trans hi
  change (L * H * Lᵀ)⁻¹ r r = (d r)⁻¹
  have hHinv : H⁻¹ = Matrix.diagonal (fun i => (d i)⁻¹) := by
    apply Matrix.inv_eq_left_inv
    change Matrix.diagonal (fun i => (d i)⁻¹) * Matrix.diagonal d = 1
    rw [Matrix.diagonal_mul_diagonal]
    have hD : (fun i => (d i)⁻¹ * d i) = (fun _ => 1) :=
      funext fun i => inv_mul_cancel₀ (hd i)
    rw [hD, Matrix.diagonal_one]
  rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, ← Matrix.transpose_nonsing_inv, hHinv,
    Matrix.mul_apply, Finset.sum_eq_single r]
  · simp [hcol, e, Matrix.diagonal_mul]
  · intro i _ hi
    rw [Matrix.transpose_apply, hcol, show e i = 0 by exact Pi.single_eq_of_ne hi 1]
    simp
  · simp

end RootedFactorization

end NumStability.CertifiedTridiagonalEigenpairs
