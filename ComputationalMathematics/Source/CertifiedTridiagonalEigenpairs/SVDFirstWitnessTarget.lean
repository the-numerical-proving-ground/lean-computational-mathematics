import ComputationalMathematics.Analysis.FloatingPointArithmetic.UnboundedBinary.Basic
import ComputationalMathematics.Analysis.MatrixInequalities.ThinPolar.Defs
import ComputationalMathematics.Analysis.MatrixNorms.Nuclear.Basic
import ComputationalMathematics.Algorithms.LinearSystems.QR.GramSchmidtPolar
import Mathlib.Data.Matrix.ColumnRowPartitioned

/-!
# First paired singular witness from the computed arrays
-/

namespace NumStability.CertifiedTridiagonalEigenpairs.ClaimTargets

open FloatingPointFormat.UnboundedBinary

/-- The thin polar factors and the nuclear budget for the source's first
perturbation, before placement of the reported pairs at the prescribed ranks. -/
def svdFirstWitness : Prop :=
  ∀ (n k p : ℕ), 1 ≤ k → k ≤ n →
    ∀ (B : Matrix (Fin n) (Fin n) ℝ)
      (Uhat Vhat : Matrix (Fin n) (Fin k) ℝ) (s : Fin k → ℝ),
      let u := unitRoundoff p
      let z := Real.sqrt (k : ℝ) * u
      let S := Matrix.diagonal s
      let HU : Matrix (Fin k) (Fin k) ℝ := rectRightGramPolarH Uhat
      let HV : Matrix (Fin k) (Fin k) ℝ := rectRightGramPolarH Vhat
      let R₁ := B * Vhat - Uhat * S
      let R₂ := B.transpose * Uhat - Vhat * S
      z ≤ 1 / 128 →
      realMatrixOperatorNorm (Uhat.transpose * Uhat - 1) ≤ 7 * z →
      realMatrixOperatorNorm (Vhat.transpose * Vhat - 1) ≤ 7 * z →
      (∀ j, max (vecNorm2 (fun i => R₁ i j)) (vecNorm2 (fun i => R₂ i j)) ≤
        160 * u * realMatrixOperatorNorm B) →
      realMatrixNuclearNorm R₁ ≤ 160 * (k : ℝ) * u * realMatrixOperatorNorm B ∧
      realMatrixNuclearNorm R₂ ≤ 160 * (k : ℝ) * u * realMatrixOperatorNorm B ∧
      ∃ (Q P : Matrix (Fin n) (Fin k) ℝ)
        (Qperp Pperp : Matrix (Fin n) (Fin (n - k)) ℝ),
        let D := Q.transpose * B * P - S
        let C₀ := Qperp.transpose * B * Pperp
        let B₀ := Q * S * P.transpose + Qperp * C₀ * Pperp.transpose
        let E₀ := B₀ - B
        MatrixPolar.IsThinPolarFactorization Uhat Q HU ∧
        MatrixPolar.IsThinPolarFactorization Vhat P HV ∧
        (∀ x, (Real.sqrt 2)⁻¹ * vecNorm2Sq x ≤ finiteQuadraticForm HU x) ∧
        (∀ x, (Real.sqrt 2)⁻¹ * vecNorm2Sq x ≤ finiteQuadraticForm HV x) ∧
        (Matrix.fromCols Q Qperp).transpose * Matrix.fromCols Q Qperp = 1 ∧
        (Matrix.fromCols P Pperp).transpose * Matrix.fromCols P Pperp = 1 ∧
        max (realMatrixOperatorNorm (HU - 1)) (realMatrixOperatorNorm (HV - 1)) ≤
          (7 * z) / (1 + Real.sqrt (1 - 7 / 128)) ∧
        max (realMatrixOperatorNorm (Uhat - Q)) (realMatrixOperatorNorm (Vhat - P)) ≤
          (7 * z) / (1 + Real.sqrt (1 - 7 / 128)) ∧
        (7 * z) / (1 + Real.sqrt (1 - 7 / 128)) < 4 * z ∧
        HU * D + D * HV = Q.transpose * R₁ + R₂.transpose * P ∧
        realMatrixNuclearNorm D ≤
          (Real.sqrt 2)⁻¹ * (realMatrixNuclearNorm R₁ + realMatrixNuclearNorm R₂) ∧
        Qperp.transpose * B * P = Qperp.transpose * R₁ * HV⁻¹ ∧
        Q.transpose * B * Pperp = HU⁻¹ * R₂.transpose * Pperp ∧
        B + E₀ = B₀ ∧ B₀ * P = Q * S ∧ B₀.transpose * Q = P * S ∧
        realMatrixNuclearNorm E₀ ≤ 3 * (realMatrixNuclearNorm R₁ + realMatrixNuclearNorm R₂) ∧
        3 * (realMatrixNuclearNorm R₁ + realMatrixNuclearNorm R₂) ≤
          960 * (k : ℝ) * u * realMatrixOperatorNorm B

end NumStability.CertifiedTridiagonalEigenpairs.ClaimTargets
