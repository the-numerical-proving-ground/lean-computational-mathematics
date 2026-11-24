import ComputationalMathematics.Analysis.MatrixStructure.Bipartite.MassShiftSpectral
import Mathlib.Logic.Equiv.Prod

/-!
# Singular-factor conjugation and coordinate pairing of a mass shift

These exact real-matrix bridges use supplied singular factors. They require no
invertibility, gap, or nonzero singular-value assumption.
-/

open Matrix

namespace NumStability.Matrix.Bipartite

/-- The block-diagonal change of basis acting separately on the two parity sets. -/
def parityBasis {n : ℕ} (U V : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ :=
  fromBlocks U 0 0 V

/-- Column orthogonality of both supplied factors gives column orthogonality of the
parity change of basis. -/
theorem parityBasis_transpose_mul {n : ℕ} (U V : Matrix (Fin n) (Fin n) ℝ)
    (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1) :
    (parityBasis U V)ᵀ * parityBasis U V = 1 := by
  simp [parityBasis, fromBlocks_transpose, fromBlocks_multiply, hU, hV, fromBlocks_one]

/-- Row orthogonality of both supplied factors gives row orthogonality of the
parity change of basis. -/
theorem parityBasis_mul_transpose {n : ℕ} (U V : Matrix (Fin n) (Fin n) ℝ)
    (hU : U * Uᵀ = 1) (hV : V * Vᵀ = 1) :
    parityBasis U V * (parityBasis U V)ᵀ = 1 := by
  simp [parityBasis, fromBlocks_transpose, fromBlocks_multiply, hU, hV, fromBlocks_one]

/-- Conjugating by supplied singular factors replaces `C` with its diagonal factor.
Only the displayed column-orthogonality identities are needed for this equation. -/
theorem massShift_conjugate_of_svd {n : ℕ}
    (C : Matrix (Fin n) (Fin n) ℝ) (α : ℝ) (s : Fin n → ℝ)
    (U V : Matrix (Fin n) (Fin n) ℝ)
    (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1)
    (hC : C = U * diagonal s * Vᵀ) :
    (parityBasis U V)ᵀ * massShift C α * parityBasis U V =
      massShift (diagonal s) α := by
  have hc : Uᵀ * (C * V) = diagonal s := by
    rw [hC]
    calc
      _ = (Uᵀ * U) * diagonal s * (Vᵀ * V) := by simp only [Matrix.mul_assoc]
      _ = diagonal s := by rw [hU, hV, Matrix.one_mul, Matrix.mul_one]
  have hct : Vᵀ * (Cᵀ * U) = diagonal s := by
    have ht := congrArg Matrix.transpose hc
    simpa [transpose_mul, Matrix.mul_assoc] using ht
  simp [parityBasis, massShift, embedding, signature, fromBlocks_transpose,
    fromBlocks_smul, fromBlocks_add, fromBlocks_multiply, Matrix.mul_assoc,
    hU, hV, hc, hct]

/-- Pair the two parity coordinates belonging to a common singular index.
The pair `(0,i)` is the left coordinate, and `(1,i)` is the right coordinate. -/
def pairCoord (n : ℕ) : (Fin 2 × Fin n) ≃ (Fin n ⊕ Fin n) :=
  (Equiv.prodCongr finTwoEquiv (Equiv.refl (Fin n))).trans
    (Equiv.boolProdEquivSum (Fin n))

@[simp]
theorem pairCoord_zero {n : ℕ} (i : Fin n) :
    pairCoord n (0, i) = Sum.inl i := by
  rfl

@[simp]
theorem pairCoord_one {n : ℕ} (i : Fin n) :
    pairCoord n (1, i) = Sum.inr i := by
  rfl

/-- A diagonal singular factor pairs into one complete two-by-two mass block per index. -/
theorem massShift_diagonal_pairing {n : ℕ} (s : Fin n → ℝ) (α : ℝ) :
    (massShift (diagonal s) α).submatrix (pairCoord n) (pairCoord n) =
      blockDiagonal (fun i : Fin n => massBlock α (s i)) := by
  ext ⟨a, i⟩ ⟨b, j⟩
  fin_cases a <;> fin_cases b <;>
    by_cases hij : i = j <;>
    simp [Matrix.submatrix_apply, massShift, embedding, signature, massBlock,
      blockDiagonal_apply, hij]

/-- The two exact bridges compose without changing singular-index multiplicities. -/
theorem massShift_conjugate_pairing_of_svd {n : ℕ}
    (C : Matrix (Fin n) (Fin n) ℝ) (α : ℝ) (s : Fin n → ℝ)
    (U V : Matrix (Fin n) (Fin n) ℝ)
    (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1)
    (hC : C = U * diagonal s * Vᵀ) :
    ((parityBasis U V)ᵀ * massShift C α * parityBasis U V).submatrix
        (pairCoord n) (pairCoord n) =
      blockDiagonal (fun i : Fin n => massBlock α (s i)) := by
  rw [massShift_conjugate_of_svd C α s U V hU hV hC, massShift_diagonal_pairing]

end NumStability.Matrix.Bipartite
