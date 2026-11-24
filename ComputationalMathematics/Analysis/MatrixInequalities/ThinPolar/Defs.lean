import ComputationalMathematics.Analysis.OperatorNorms.RealMatrix
import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# Exact thin-polar predicates and column controls

Pure real-matrix definitions for Gram perturbations, source-style column
controls and exact thin-polar witnesses. Matrix norm conclusions using this API
refer to `realMatrixOperatorNorm`, the subordinate Euclidean operator norm.
-/

namespace NumStability.MatrixPolar

open scoped BigOperators

noncomputable section

/-- The genuine real Gram defect of a rectangular matrix. -/
def gramDefect {n k : ℕ} (X : Matrix (Fin n) (Fin k) ℝ) :
    Matrix (Fin k) (Fin k) ℝ :=
  X.transpose * X - 1

/-- Pairwise unequal-column inner-product control. The diagonal is not
assumed here; it must be derived separately from column norm control. -/
def PairwiseGramBound {n k : ℕ}
    (X : Matrix (Fin n) (Fin k) ℝ) (cO rho : ℝ) : Prop :=
  ∀ j h : Fin k, j ≠ h → |(X.transpose * X) j h| ≤ cO * rho

/-- Deviation of each Euclidean column norm from one. This is not a
squared-norm hypothesis or an assumed operator Gram-defect bound. -/
def ColumnNormDeviationBound {n k : ℕ}
    (X : Matrix (Fin n) (Fin k) ℝ) (cN rho : ℝ) : Prop :=
  ∀ j : Fin k, |vecNorm2 (fun i => X i j) - 1| ≤ cN * rho

/-- Uniform coefficient for the diagonal and off-diagonal Gram estimates. -/
noncomputable def gramControlConstant (cO cN : ℝ) : ℝ :=
  max 1 (max cO (2 * cN + cN ^ 2))

/-- Real quadratic-form order `H >= a I`, without the default pointwise
matrix order. The vector square sum is its Euclidean norm squared. -/
def HasQuadraticLowerBound {k : ℕ}
    (H : Matrix (Fin k) (Fin k) ℝ) (a : ℝ) : Prop :=
  ∀ v : Fin k → ℝ,
    a * (∑ j : Fin k, v j ^ 2) ≤
      ∑ i : Fin k, ∑ j : Fin k, v i * H i j * v j

/-- Exact real thin polar factorization, with genuine matrix PSD rather than
entrywise positivity. A positive lower floor can be asserted separately. -/
def IsThinPolarFactorization {n k : ℕ}
    (X Q : Matrix (Fin n) (Fin k) ℝ) (H : Matrix (Fin k) (Fin k) ℝ) : Prop :=
  X = Q * H ∧
    Q.transpose * Q = 1 ∧
    H.transpose = H ∧
    H.PosSemidef

end

end NumStability.MatrixPolar
