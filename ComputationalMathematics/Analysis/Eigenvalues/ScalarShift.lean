import ComputationalMathematics.Analysis.Eigenvalues.StrictSpectralCount

/-!
# Ordered eigenvalues under scalar shifts

The actual retained Courant--Fischer variational characterization proves the
ordered shift identity at every index. Reversing the retained decreasing
indices then gives the strict count correspondence used by native Sturm.
-/

namespace NumStability.ScalarShift

noncomputable section
open scoped RealInnerProductSpace
open Classical

/-- Subtract the real scalar identity. -/
def shifted {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (x : ℝ) :=
  A - x • (1 : Matrix (Fin n) (Fin n) ℝ)

theorem shifted_isHermitian {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.IsHermitian) (x : ℝ) : (shifted A x).IsHermitian := by
  apply hA.sub
  unfold Matrix.IsHermitian
  simp

/-- The exact Rayleigh-form shift, without a unit-vector restriction. -/
theorem rayleigh_shifted {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (x : ℝ)
    (v : EuclideanSpace ℝ (Fin n)) :
    matrixRayleighForm (shifted A x) v = matrixRayleighForm A v - x * ‖v‖ ^ 2 := by
  unfold matrixRayleighForm shifted
  rw [map_sub, map_smul, Matrix.toLpLin_one]
  simp only [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply,
    inner_sub_right, real_inner_smul_right, real_inner_self_eq_norm_sq]

/-- Every decreasingly ordered eigenvalue shifts by exactly the scalar.
The proof uses the genuine variational API in both directions. -/
theorem hermitianOrderedEigenvalue_shifted {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.IsHermitian) (x : ℝ) (i : Fin n) :
    hermitianOrderedEigenvalue (shifted_isHermitian A hA x) i =
      hermitianOrderedEigenvalue hA i - x := by
  let S := shifted A x
  let hS := shifted_isHermitian A hA x
  apply le_antisymm
  · obtain ⟨E, hErank, hSlower, _hSattain, _hSall⟩ :=
      hermitian_courantFischer_maxMin S hS i
    obtain ⟨_F, _hFrank, _hAlower, _hAattain, hAall⟩ :=
      hermitian_courantFischer_maxMin A hA i
    obtain ⟨v, hvE, hvnorm, hAv⟩ := hAall E hErank
    have hSv := hSlower v hvE hvnorm
    change hermitianOrderedEigenvalue hS i ≤ matrixRayleighForm (shifted A x) v at hSv
    rw [rayleigh_shifted, hvnorm, one_pow, mul_one] at hSv
    linarith
  · obtain ⟨E, hErank, hAlower, _hAattain, _hAall⟩ :=
      hermitian_courantFischer_maxMin A hA i
    obtain ⟨_F, _hFrank, _hSlower, _hSattain, hSall⟩ :=
      hermitian_courantFischer_maxMin S hS i
    obtain ⟨v, hvE, hvnorm, hSv⟩ := hSall E hErank
    have hAv := hAlower v hvE hvnorm
    change matrixRayleighForm (shifted A x) v ≤ hermitianOrderedEigenvalue hS i at hSv
    rw [rayleigh_shifted, hvnorm, one_pow, mul_one] at hSv
    linarith

/-- The same exact shift at the explicitly reversed ascending index. -/
theorem ascendingEigenvalue_shifted {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.IsHermitian) (x : ℝ) (i : Fin n) :
    NoisyRankCertificate.ascendingEigenvalue (shifted_isHermitian A hA x) i =
      NoisyRankCertificate.ascendingEigenvalue hA i - x :=
  hermitianOrderedEigenvalue_shifted A hA x i.rev

/-- Strictly negative ascending eigenvalues of the shifted matrix correspond
exactly to ascending eigenvalues strictly below the unshifted trial. Repeated
and zero eigenvalues, and exact eigenvalue trials, require no exception. -/
theorem negative_shifted_count_eq_strictBelowCount {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsHermitian) (x : ℝ) :
    Finset.card {i : Fin n |
      hermitianOrderedEigenvalue (shifted_isHermitian A hA x) i.rev < 0} =
      NoisyRankCertificate.strictBelowCount (NoisyRankCertificate.ascendingEigenvalue hA) x := by
  have hsets :
      (Finset.univ.filter fun i : Fin n =>
        hermitianOrderedEigenvalue (shifted_isHermitian A hA x) i.rev < 0) =
      (Finset.univ.filter fun i : Fin n => NoisyRankCertificate.ascendingEigenvalue hA i < x) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      NoisyRankCertificate.ascendingEigenvalue]
    rw [hermitianOrderedEigenvalue_shifted]
    exact sub_lt_zero
  exact congrArg Finset.card hsets

end
end NumStability.ScalarShift
