import ComputationalMathematics.Analysis.OperatorNorms.RealMatrix

/-! The ordered common SVD witness with the source's quantitative bounds. -/

namespace NumStability.CertifiedTridiagonalEigenpairs

/-- One full ordered SVD of a single nearby matrix, with the reported
labels at their prescribed ranks and the source's factor and matrix bounds. -/
def HasIndexedSVDWitness {n k : ℕ} (B : Matrix (Fin n) (Fin n) ℝ) (I : Fin k → Fin n)
    (Uhat Vhat : Matrix (Fin n) (Fin k) ℝ) (s : Fin k → ℝ) (u : ℝ) : Prop :=
  ∃ (U V E : Matrix (Fin n) (Fin n) ℝ) (d : Fin n → ℝ),
    U.transpose * U = 1 ∧ U * U.transpose = 1 ∧
    V.transpose * V = 1 ∧ V * V.transpose = 1 ∧
    Monotone d ∧ (∀ i, 0 ≤ d i) ∧ (∀ j, d (I j) = s j) ∧
    B + E = U * Matrix.diagonal d * V.transpose ∧
    realMatrixOperatorNorm E ≤ 1952 * (k : ℝ) * u * realMatrixOperatorNorm B ∧
    max (realMatrixOperatorNorm (Uhat - U.submatrix id I))
      (realMatrixOperatorNorm (Vhat - V.submatrix id I)) ≤ 4 * Real.sqrt (k : ℝ) * u

end NumStability.CertifiedTridiagonalEigenpairs
