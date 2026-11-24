import Mathlib.Data.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Abel

/-!
# Exact algebra for a mass-shifted bipartite matrix

The two parity coordinate sets are represented by `Fin n ⊕ Fin n`. These helpers
concern exact real matrices, independently of any floating-point implementation.
-/

open Matrix

namespace NumStability.Matrix.Bipartite

/-- The symmetric bipartite embedding with off-diagonal blocks `C` and `Cᵀ`. -/
def embedding {n : ℕ} (C : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ :=
  fromBlocks 0 C Cᵀ 0

/-- The signature distinguishing the left and right coordinate sets. -/
def signature (n : ℕ) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ :=
  fromBlocks 1 0 0 (-1)

/-- The bipartite embedding shifted by a scalar multiple of its signature. -/
def massShift {n : ℕ} (C : Matrix (Fin n) (Fin n) ℝ) (α : ℝ) :
    Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ :=
  embedding C + α • signature n

@[simp]
theorem embedding_transpose {n : ℕ} (C : Matrix (Fin n) (Fin n) ℝ) :
    (embedding C)ᵀ = embedding C := by
  simp [embedding, fromBlocks_transpose]

@[simp]
theorem signature_transpose (n : ℕ) : (signature n)ᵀ = signature n := by
  simp [signature, fromBlocks_transpose]

@[simp]
theorem massShift_transpose {n : ℕ} (C : Matrix (Fin n) (Fin n) ℝ) (α : ℝ) :
    (massShift C α)ᵀ = massShift C α := by
  simp [massShift, transpose_add, transpose_smul]

/-- Squaring the signature gives the identity on both parity coordinate sets. -/
@[simp]
theorem signature_mul_self (n : ℕ) : signature n * signature n = 1 := by
  simp [signature, fromBlocks_multiply, fromBlocks_one]

/-- The unshifted bipartite matrix anticommutes with the parity signature. -/
theorem embedding_anticommutator {n : ℕ} (C : Matrix (Fin n) (Fin n) ℝ) :
    embedding C * signature n + signature n * embedding C = 0 := by
  simp [embedding, signature, fromBlocks_multiply, fromBlocks_add]

/-- The exact mass-shift anticommutator, `TJ + JT = 2αI`. -/
theorem massShift_anticommutator {n : ℕ} (C : Matrix (Fin n) (Fin n) ℝ) (α : ℝ) :
    massShift C α * signature n + signature n * massShift C α =
      (2 * α) • (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ) := by
  simp only [massShift, Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul,
    signature_mul_self]
  calc
    embedding C * signature n + α • 1 +
        (signature n * embedding C + α • 1) =
        (embedding C * signature n + signature n * embedding C) + (α + α) • 1 := by
          rw [add_smul]
          abel
    _ = (2 * α) • 1 := by rw [embedding_anticommutator, zero_add, two_mul]

/-- Compressing the anticommutator by orthonormal columns gives the residual
Sylvester identity. The residual is exactly `E = TQ - QΛ`, and the compressed
signature is exactly `QᵀJQ`. Symmetry of `Λ` suffices for this algebraic step. -/
theorem compressed_sylvester {n k : ℕ}
    (C : Matrix (Fin n) (Fin n) ℝ) (α : ℝ)
    (Q : Matrix (Fin n ⊕ Fin n) (Fin k) ℝ)
    (Λ : Matrix (Fin k) (Fin k) ℝ)
    (hQ : Qᵀ * Q = 1) (hΛ : Λ.IsSymm) :
    let T := massShift C α
    let J := signature n
    let E := T * Q - Q * Λ
    let Jc := Qᵀ * J * Q
    Λ * Jc + Jc * Λ =
      (2 * α) • (1 : Matrix (Fin k) (Fin k) ℝ) -
        Eᵀ * J * Q - Qᵀ * J * E := by
  dsimp only
  have hcompressed :
      Qᵀ * massShift C α * signature n * Q +
        Qᵀ * signature n * massShift C α * Q =
          (2 * α) • (1 : Matrix (Fin k) (Fin k) ℝ) := by
    calc
      _ = Qᵀ * (massShift C α * signature n + signature n * massShift C α) * Q := by
        simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
      _ = (2 * α) • 1 := by
        rw [massShift_anticommutator]
        simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hQ]
  rw [← hcompressed]
  simp only [transpose_sub, transpose_mul, massShift_transpose, hΛ.eq,
    Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_assoc]
  abel

end NumStability.Matrix.Bipartite
