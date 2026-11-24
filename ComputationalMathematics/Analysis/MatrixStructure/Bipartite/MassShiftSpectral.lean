import ComputationalMathematics.Analysis.MatrixStructure.Bipartite.MassShift
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Squares and two-coordinate eigenvectors for a mass shift

Exact real-matrix identities underlying the two-by-two mass-shift blocks.
-/

open Matrix

namespace NumStability.Matrix.Bipartite

/-- Squaring the bipartite embedding separates the two coordinate sets. -/
theorem embedding_sq {n : ℕ} (C : Matrix (Fin n) (Fin n) ℝ) :
    embedding C ^ 2 = fromBlocks (C * Cᵀ) 0 0 (Cᵀ * C) := by
  simp [pow_two, embedding, fromBlocks_multiply]

/-- The square of the shifted embedding has the shifted Gram blocks. -/
theorem massShift_sq {n : ℕ} (C : Matrix (Fin n) (Fin n) ℝ) (α : ℝ) :
    massShift C α ^ 2 =
      fromBlocks (C * Cᵀ + α ^ 2 • (1 : Matrix (Fin n) (Fin n) ℝ)) 0 0
        (Cᵀ * C + α ^ 2 • (1 : Matrix (Fin n) (Fin n) ℝ)) := by
  simp [pow_two, massShift, embedding, signature, fromBlocks_smul, fromBlocks_add,
    fromBlocks_multiply, smul_smul, add_comm]

/-- The real symmetric block corresponding to one singular value. -/
def massBlock (α s : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![α, s; s, -α]

/-- The nonnegative magnitude of the two mass-block eigenvalues. -/
noncomputable def massMagnitude (α s : ℝ) : ℝ := Real.sqrt (α ^ 2 + s ^ 2)

/-- An explicit vector for the positive mass-block eigenvalue, also at `s = 0`. -/
noncomputable def positiveMassVector (α s : ℝ) : Fin 2 → ℝ :=
  ![massMagnitude α s + α, s]

/-- An explicit vector for the negative mass-block eigenvalue, also at `s = 0`. -/
noncomputable def negativeMassVector (α s : ℝ) : Fin 2 → ℝ :=
  ![-s, massMagnitude α s + α]

theorem massMagnitude_sq (α s : ℝ) :
    massMagnitude α s ^ 2 = α ^ 2 + s ^ 2 := by
  exact Real.sq_sqrt (add_nonneg (sq_nonneg α) (sq_nonneg s))

theorem massMagnitude_nonneg (α s : ℝ) : 0 ≤ massMagnitude α s :=
  Real.sqrt_nonneg _

/-- For nonnegative mass, every shifted magnitude is at least the mass. -/
theorem le_massMagnitude {α : ℝ} (hα : 0 ≤ α) (s : ℝ) : α ≤ massMagnitude α s := by
  calc
    α = Real.sqrt (α ^ 2) := (Real.sqrt_sq hα).symm
    _ ≤ massMagnitude α s := Real.sqrt_le_sqrt (le_add_of_nonneg_right (sq_nonneg s))

/-- The scalar mass map is 1-Lipschitz. -/
theorem massMagnitude_sub_le (α s t : ℝ) :
    |massMagnitude α s - massMagnitude α t| ≤ |s - t| := by
  let v : ℝ → EuclideanSpace ℝ (Fin 2) := fun x => WithLp.toLp 2 ![α, x]
  have hv (x : ℝ) : ‖v x‖ = massMagnitude α x := by
    simp [v, EuclideanSpace.norm_eq, Fin.sum_univ_succ, massMagnitude,
      Real.norm_eq_abs, sq_abs]
  have hd : ‖v s - v t‖ = |s - t| := by
    simp [v, EuclideanSpace.norm_eq, Fin.sum_univ_succ,
      Real.norm_eq_abs, sq_abs, Real.sqrt_sq_eq_abs]
  simpa only [hv, hd] using abs_norm_sub_norm_le (v s) (v t)

/-- Positive mass guarantees a nonzero positive-eigenvalue vector, including at zero `s`. -/
theorem positiveMassVector_ne_zero {α s : ℝ} (hα : 0 < α) :
    positiveMassVector α s ≠ 0 := by
  intro h
  have h0 := congrFun h (0 : Fin 2)
  simp [positiveMassVector] at h0
  have := massMagnitude_nonneg α s
  linarith

/-- Positive mass guarantees a nonzero negative-eigenvalue vector, including at zero `s`. -/
theorem negativeMassVector_ne_zero {α s : ℝ} (hα : 0 < α) :
    negativeMassVector α s ≠ 0 := by
  intro h
  have h1 := congrFun h (1 : Fin 2)
  simp [negativeMassVector] at h1
  have := massMagnitude_nonneg α s
  linarith

/-- The explicit positive vector satisfies the matrix eigenvector equation. -/
theorem massBlock_mulVec_positive (α s : ℝ) :
    massBlock α s *ᵥ positiveMassVector α s =
      massMagnitude α s • positiveMassVector α s := by
  have hs := massMagnitude_sq α s
  ext i
  fin_cases i <;> simp [massBlock, positiveMassVector, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  · nlinarith
  · ring

/-- The explicit negative vector satisfies the matrix eigenvector equation. -/
theorem massBlock_mulVec_negative (α s : ℝ) :
    massBlock α s *ᵥ negativeMassVector α s =
      (-massMagnitude α s) • negativeMassVector α s := by
  have hs := massMagnitude_sq α s
  ext i
  fin_cases i <;> simp [massBlock, negativeMassVector, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  · ring
  · nlinarith

/-- The positive eigenvalue and its explicit nonzero vector in Mathlib's eigenvector API. -/
theorem massBlock_hasEigenvector_positive {α s : ℝ} (hα : 0 < α) :
    Module.End.HasEigenvector (massBlock α s).mulVecLin
      (massMagnitude α s) (positiveMassVector α s) := by
  rw [Module.End.hasEigenvector_iff, Module.End.mem_eigenspace_iff]
  exact ⟨massBlock_mulVec_positive α s, positiveMassVector_ne_zero hα⟩

/-- The negative eigenvalue and its explicit nonzero vector in Mathlib's eigenvector API. -/
theorem massBlock_hasEigenvector_negative {α s : ℝ} (hα : 0 < α) :
    Module.End.HasEigenvector (massBlock α s).mulVecLin
      (-massMagnitude α s) (negativeMassVector α s) := by
  rw [Module.End.hasEigenvector_iff, Module.End.mem_eigenspace_iff]
  exact ⟨massBlock_mulVec_negative α s, negativeMassVector_ne_zero hα⟩

/-- Both signed magnitudes are genuine eigenvalues; `s = 0` is included. -/
theorem massBlock_hasEigenvalues {α s : ℝ} (hα : 0 < α) (_hs : 0 ≤ s) :
    Module.End.HasEigenvalue (massBlock α s).mulVecLin (Real.sqrt (α ^ 2 + s ^ 2)) ∧
      Module.End.HasEigenvalue (massBlock α s).mulVecLin (-Real.sqrt (α ^ 2 + s ^ 2)) := by
  exact ⟨Module.End.hasEigenvalue_of_hasEigenvector (massBlock_hasEigenvector_positive hα),
    Module.End.hasEigenvalue_of_hasEigenvector (massBlock_hasEigenvector_negative hα)⟩

end NumStability.Matrix.Bipartite
