import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus

namespace NumStability.ComplexHermitianL1

open scoped BigOperators ComplexOrder

/-- Trace of the positive square root of the right Gram matrix. -/
noncomputable def complexNuclearNorm {n : ℕ} (D : Matrix (Fin n) (Fin n) ℂ) : ℝ :=
  Complex.re ((Matrix.isHermitian_conjTranspose_mul_self D).cfc Real.sqrt).trace

/-- The full decreasing eigenvalue list of a complex Hermitian matrix. -/
noncomputable def complexOrderedEigenvalue {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ}
    (hA : A.IsHermitian) : Fin n → ℝ :=
  (Matrix.isHermitian_iff_isSymmetric.mp hA).eigenvalues finrank_euclideanSpace_fin

end NumStability.ComplexHermitianL1
