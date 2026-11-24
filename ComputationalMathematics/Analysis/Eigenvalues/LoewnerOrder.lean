import ComputationalMathematics.Analysis.Eigenvalues.CourantFischer
import Mathlib.Analysis.InnerProductSpace.Trace
import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# Ordered Hermitian eigenvalues and a common upper bound

The tracked Courant--Fischer witness gives monotonicity of the actual ordered
Hermitian eigenvalues under Rayleigh, quadratic-form, or positive-semidefinite
order. A common Hermitian upper bound then controls the sum of absolute
ordered eigenvalue differences by a trace expression. No nuclear-norm
identification, nonempty-dimension premise, or spectral gap is required.
-/

namespace NumStability

open scoped BigOperators RealInnerProductSpace

/-- A unit-vector Rayleigh comparison orders values represented by actual
Courant--Fischer max--min witnesses at the same index. -/
theorem IsCourantFischerMaxMin.value_le_of_unit_rayleigh_le {n : ℕ}
    {A B : Matrix (Fin n) (Fin n) ℝ} {a b : Fin n → ℝ} {i : Fin n}
    (hA : IsCourantFischerMaxMin A a i)
    (hB : IsCourantFischerMaxMin B b i)
    (hAB : ∀ x : EuclideanSpace ℝ (Fin n), ‖x‖ = 1 →
      matrixRayleighForm A x ≤ matrixRayleighForm B x) :
    a i ≤ b i := by
  obtain ⟨E, hE, hmin, _, _⟩ := hA
  obtain ⟨_, _, _, _, hmax⟩ := hB
  obtain ⟨x, hx, hunit, hupper⟩ := hmax E hE
  exact (hmin x hx hunit).trans ((hAB x hunit).trans hupper)

/-- The canonical decreasing Hermitian eigenvalues are monotone under
unit-vector Rayleigh comparison, with multiplicities retained. -/
theorem hermitianOrderedEigenvalue_le_of_unit_rayleigh_le {n : ℕ}
    {A B : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.IsHermitian) (hB : B.IsHermitian)
    (hAB : ∀ x : EuclideanSpace ℝ (Fin n), ‖x‖ = 1 →
      matrixRayleighForm A x ≤ matrixRayleighForm B x) (i : Fin n) :
    hermitianOrderedEigenvalue hA i ≤ hermitianOrderedEigenvalue hB i :=
  (hermitian_courantFischer_maxMin A hA i).value_le_of_unit_rayleigh_le
    (hermitian_courantFischer_maxMin B hB i) hAB

/-- Rayleigh comparison for all vectors orders each actual Hermitian eigenvalue. -/
theorem hermitianOrderedEigenvalue_le_of_rayleigh_le {n : ℕ}
    {A B : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.IsHermitian) (hB : B.IsHermitian)
    (hAB : ∀ x : EuclideanSpace ℝ (Fin n),
      matrixRayleighForm A x ≤ matrixRayleighForm B x) (i : Fin n) :
    hermitianOrderedEigenvalue hA i ≤ hermitianOrderedEigenvalue hB i :=
  hermitianOrderedEigenvalue_le_of_unit_rayleigh_le hA hB (fun x _ => hAB x) i

/-- The Euclidean Rayleigh form is the repository's finite quadratic form. -/
theorem matrixRayleighForm_eq_finiteQuadraticForm {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    matrixRayleighForm A x = finiteQuadraticForm A (WithLp.ofLp x) := by
  simp only [matrixRayleighForm, Matrix.toLpLin_apply, PiLp.inner_apply]
  change (∑ i, (∑ j, A i j * x j) * x i) =
    ∑ i, x i * ∑ j, A i j * x j
  apply Finset.sum_congr rfl
  intro i _
  exact mul_comm _ _

/-- Quadratic-form Loewner order orders the full Hermitian eigenvalue list. -/
theorem hermitianOrderedEigenvalue_le_of_finiteLoewnerLe {n : ℕ}
    {A B : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.IsHermitian) (hB : B.IsHermitian)
    (hAB : finiteLoewnerLe A B) (i : Fin n) :
    hermitianOrderedEigenvalue hA i ≤ hermitianOrderedEigenvalue hB i := by
  apply hermitianOrderedEigenvalue_le_of_rayleigh_le hA hB _ i
  intro x
  simpa only [matrixRayleighForm_eq_finiteQuadraticForm] using hAB (WithLp.ofLp x)

/-- A positive-semidefinite difference gives Rayleigh order. -/
theorem matrixRayleighForm_le_of_posSemidef_sub {n : ℕ}
    {A B : Matrix (Fin n) (Fin n) ℝ} (hAB : (B - A).PosSemidef)
    (x : EuclideanSpace ℝ (Fin n)) :
    matrixRayleighForm A x ≤ matrixRayleighForm B x := by
  have h := hAB.dotProduct_mulVec_nonneg (WithLp.ofLp x)
  have hnonneg : 0 ≤ matrixRayleighForm (B - A) x := by
    rw [matrixRayleighForm_eq_finiteQuadraticForm]
    simpa [finiteQuadraticForm, finiteMatVec, Matrix.mulVec, dotProduct] using h
  have hsub : matrixRayleighForm (B - A) x =
      matrixRayleighForm B x - matrixRayleighForm A x := by
    simp only [matrixRayleighForm, map_sub, LinearMap.sub_apply, inner_sub_right]
  rw [hsub] at hnonneg
  exact sub_nonneg.mp hnonneg

/-- A positive-semidefinite difference orders the actual Hermitian eigenvalues. -/
theorem hermitianOrderedEigenvalue_le_of_posSemidef_sub {n : ℕ}
    {A B : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.IsHermitian) (hB : B.IsHermitian)
    (hAB : (B - A).PosSemidef) (i : Fin n) :
    hermitianOrderedEigenvalue hA i ≤ hermitianOrderedEigenvalue hB i :=
  hermitianOrderedEigenvalue_le_of_rayleigh_le hA hB
    (matrixRayleighForm_le_of_posSemidef_sub hAB) i

/-- Summing the canonical ordered Hermitian eigenvalues gives the matrix trace,
including the empty matrix. -/
theorem sum_hermitianOrderedEigenvalue_eq_trace {n : ℕ}
    {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsHermitian) :
    ∑ i, hermitianOrderedEigenvalue hA i = A.trace := by
  have htrace := (Matrix.isHermitian_iff_isSymmetric.mp hA).trace_eq_sum_eigenvalues
    finrank_euclideanSpace_fin
  change A.toEuclideanLin.trace ℝ (EuclideanSpace ℝ (Fin n)) =
    ∑ i, hermitianOrderedEigenvalue hA i at htrace
  rw [← htrace, LinearMap.trace_eq_matrix_trace ℝ
    (EuclideanSpace.basisFun (Fin n) ℝ).toBasis,
    Matrix.toEuclideanLin_eq_toLin_orthonormal, LinearMap.toMatrix_toLin]

/-- A common Hermitian Rayleigh upper bound controls the full ordered l1
spectral discrepancy by its exact trace excess. -/
theorem sum_abs_sub_hermitianOrderedEigenvalue_le_trace_of_rayleigh_upper {n : ℕ}
    {A C H : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.IsHermitian) (hC : C.IsHermitian) (hH : H.IsHermitian)
    (hAH : ∀ x : EuclideanSpace ℝ (Fin n),
      matrixRayleighForm A x ≤ matrixRayleighForm H x)
    (hCH : ∀ x : EuclideanSpace ℝ (Fin n),
      matrixRayleighForm C x ≤ matrixRayleighForm H x) :
    (∑ i, |hermitianOrderedEigenvalue hA i - hermitianOrderedEigenvalue hC i|) ≤
      2 * H.trace - A.trace - C.trace := by
  calc
    _ ≤ ∑ i, (2 * hermitianOrderedEigenvalue hH i -
        hermitianOrderedEigenvalue hA i - hermitianOrderedEigenvalue hC i) := by
      apply Finset.sum_le_sum
      intro i _
      have hAi := hermitianOrderedEigenvalue_le_of_rayleigh_le hA hH hAH i
      have hCi := hermitianOrderedEigenvalue_le_of_rayleigh_le hC hH hCH i
      rw [abs_le]
      constructor <;> linarith
    _ = _ := by
      rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
        sum_hermitianOrderedEigenvalue_eq_trace hH,
        sum_hermitianOrderedEigenvalue_eq_trace hA,
        sum_hermitianOrderedEigenvalue_eq_trace hC]

/-- Common quadratic-form upper bounds imply the exact trace-excess l1 bound. -/
theorem sum_abs_sub_hermitianOrderedEigenvalue_le_trace_of_finiteLoewner_upper {n : ℕ}
    {A C H : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.IsHermitian) (hC : C.IsHermitian) (hH : H.IsHermitian)
    (hAH : finiteLoewnerLe A H) (hCH : finiteLoewnerLe C H) :
    (∑ i, |hermitianOrderedEigenvalue hA i - hermitianOrderedEigenvalue hC i|) ≤
      2 * H.trace - A.trace - C.trace := by
  apply sum_abs_sub_hermitianOrderedEigenvalue_le_trace_of_rayleigh_upper hA hC hH
  · intro x
    simpa only [matrixRayleighForm_eq_finiteQuadraticForm] using hAH (WithLp.ofLp x)
  · intro x
    simpa only [matrixRayleighForm_eq_finiteQuadraticForm] using hCH (WithLp.ofLp x)

/-- Common positive-semidefinite upper differences imply the trace-excess l1
bound. This is the Hermitian comparison step before a nuclear-norm bridge. -/
theorem sum_abs_sub_hermitianOrderedEigenvalue_le_trace_of_posSemidef_upper {n : ℕ}
    {A C H : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.IsHermitian) (hC : C.IsHermitian) (hH : H.IsHermitian)
    (hAH : (H - A).PosSemidef) (hCH : (H - C).PosSemidef) :
    (∑ i, |hermitianOrderedEigenvalue hA i - hermitianOrderedEigenvalue hC i|) ≤
      2 * H.trace - A.trace - C.trace :=
  sum_abs_sub_hermitianOrderedEigenvalue_le_trace_of_rayleigh_upper hA hC hH
    (matrixRayleighForm_le_of_posSemidef_sub hAH)
    (matrixRayleighForm_le_of_posSemidef_sub hCH)

end NumStability
