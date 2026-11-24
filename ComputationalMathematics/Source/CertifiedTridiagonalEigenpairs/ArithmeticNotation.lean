import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-! Matrix, vector, and logarithm conventions in §1.1. -/

namespace NumStability.CertifiedTridiagonalEigenpairs.ArithmeticNotation

noncomputable section

/-- The paper's vector 2-norm. -/
def vectorNorm {n : ℕ} {𝕜 : Type*} [RCLike 𝕜] (x : EuclideanSpace 𝕜 (Fin n)) : ℝ :=
  ‖x‖

open scoped Matrix.Norms.L2Operator in
/-- The matrix norm induced by the Euclidean vector norms. -/
def matrixNorm {m n : ℕ} {𝕜 : Type*} [RCLike 𝕜] (a : Matrix (Fin m) (Fin n) 𝕜) : ℝ :=
  ‖a‖

open scoped Matrix.Norms.Frobenius in
/-- The Frobenius norm of a finite matrix. -/
def frobeniusNorm {m n : ℕ} {𝕜 : Type*} [RCLike 𝕜] (a : Matrix (Fin m) (Fin n) 𝕜) : ℝ :=
  ‖a‖

/-- Identity of the indicated size. -/
def identity (n : ℕ) {𝕜 : Type*} [RCLike 𝕜] : Matrix (Fin n) (Fin n) 𝕜 := 1

/-- Real transpose. -/
def transpose {m n : ℕ} (a : Matrix (Fin m) (Fin n) ℝ) : Matrix (Fin n) (Fin m) ℝ :=
  a.transpose

/-- Complex conjugate transpose. -/
def adjoint {m n : ℕ} (a : Matrix (Fin m) (Fin n) ℂ) : Matrix (Fin n) (Fin m) ℂ :=
  a.conjTranspose

/-- Imaginary part as a Hermitian-matrix expression. -/
def imaginaryPart {n : ℕ} (a : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  (2 * Complex.I : ℂ)⁻¹ • (a - adjoint a)

/-- Both log and log₂ denote the base-two logarithm. -/
def binaryLog (x : ℝ) : ℝ :=
  Real.logb 2 x

/-- The natural logarithm. -/
def naturalLog (x : ℝ) : ℝ :=
  Real.log x

end

end NumStability.CertifiedTridiagonalEigenpairs.ArithmeticNotation
