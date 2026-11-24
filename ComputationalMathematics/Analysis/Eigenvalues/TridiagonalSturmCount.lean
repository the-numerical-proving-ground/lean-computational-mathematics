import ComputationalMathematics.Analysis.MatrixStructure.TridiagonalLDL
import ComputationalMathematics.Analysis.Eigenvalues.CongruenceInertia
import ComputationalMathematics.Analysis.Eigenvalues.ScalarShift
import ComputationalMathematics.Analysis.Eigenvalues.NoisyRankCertificate

/-!
# Exact strict Sturm counts for symmetric tridiagonal matrices
-/

namespace NumStability

open scoped BigOperators Matrix
open Classical
noncomputable section

/-- A shifted LDLᵀ factorization identifies the strict-below count. -/
theorem pivotSignCount_eq_strictBelowCount_of_ldl {m : ℕ}
    (A L : Matrix (Fin m) (Fin m) ℝ) (hA : A.IsHermitian) (hL : IsUnit L)
    (d : Fin m → ℝ) (x : ℝ)
    (hfactor : A - x • 1 = L * Matrix.diagonal d * L.transpose) :
    Finset.card {i : Fin m | d i < 0} =
      NoisyRankCertificate.strictBelowCount (NoisyRankCertificate.ascendingEigenvalue hA) x := by
  obtain ⟨u, rfl⟩ := hL
  have hcount := CongruenceInertia.card_negative_ascending_eigenvalue_eq_card_negative_diagonal
    (ScalarShift.shifted_isHermitian A hA x) u d hfactor
  exact hcount.symm.trans (ScalarShift.negative_shifted_count_eq_strictBelowCount A hA x)


/-- The exact shifted recurrence counts eigenvalues of its specified
tridiagonal matrix strictly below the shift. -/
theorem sturmBackwardRecurrence_strictBelowCount {n : ℕ}
    (d a : Fin (n + 1) → ℝ) (b : Fin n → ℝ) (x : ℝ)
    (hd : ∀ i, d i ≠ 0) (hrec : IsSturmBackwardRecurrence d a b x) :
    Finset.card {i : Fin (n + 1) | d i < 0} =
      NoisyRankCertificate.strictBelowCount
        (NoisyRankCertificate.ascendingEigenvalue (sturmTridiagonal_isHermitian a b)) x :=
  pivotSignCount_eq_strictBelowCount_of_ldl _ _
    (sturmTridiagonal_isHermitian a b) (tridiagonalLDLLower_isUnit _ _) d x
    (sturmBackwardRecurrence_ldl d a b x hd hrec)

/-- A witness to the exact pivot recurrence and entrywise perturbation bounds
gives the padded strict-below count bracket for the original tridiagonal. -/
theorem sturmBackwardRecurrence_count_bracket {n : ℕ}
    (d a a' : Fin (n + 1) → ℝ) (b b' : Fin n → ℝ) (x : ℝ)
    (hd : ∀ i, d i ≠ 0) (hrec : IsSturmBackwardRecurrence d a' b' x)
    {D E ε : ℝ} (hD : 0 ≤ D) (hE : 0 ≤ E)
    (ha : ∀ i, |a' i - a i| ≤ D) (hb : ∀ i, |b' i - b i| ≤ E)
    (hbudget : D + 2 * E ≤ ε) :
    NoisyRankCertificate.strictBelowCount
        (NoisyRankCertificate.ascendingEigenvalue (sturmTridiagonal_isHermitian a b)) (x - ε) ≤
      Finset.card {i : Fin (n + 1) | d i < 0} ∧
    Finset.card {i : Fin (n + 1) | d i < 0} ≤
      NoisyRankCertificate.strictBelowCount
        (NoisyRankCertificate.ascendingEigenvalue (sturmTridiagonal_isHermitian a b)) (x + ε) := by
  rw [sturmBackwardRecurrence_strictBelowCount d a' b' x hd hrec]
  apply NoisyRankCertificate.strictBelowCount_bracket_of_operatorNorm
  rw [← sturmTridiagonal_sub]
  exact (sturmTridiagonal_operatorNorm_le (a' - a) (b' - b) hD hE ha hb).trans hbudget

end
end NumStability
