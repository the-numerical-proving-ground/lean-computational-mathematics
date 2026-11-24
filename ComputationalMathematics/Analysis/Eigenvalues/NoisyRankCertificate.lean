import ComputationalMathematics.Analysis.Eigenvalues.StrictSpectralCount
import ComputationalMathematics.HDP.Matrix.Weyl

/-!
# Strict-count estimates under Hermitian perturbations

Weyl's inequality bounds the displacement of each ordered eigenvalue and
therefore gives padded strict-below counts and rank implications.
-/

namespace NumStability.NoisyRankCertificate

noncomputable section
open Classical

/-- The existing Weyl result, at the explicitly reversed index, gives the
pointwise ascending eigenvalue error. Its proof is reused unchanged. -/
theorem ascendingEigenvalue_add_error {n : ℕ}
    (T F : Matrix (Fin n) (Fin n) ℝ) (hT : T.IsHermitian) (hF : F.IsHermitian)
    {ε : ℝ} (hbound : realMatrixOperatorNorm F ≤ ε) (i : Fin n) :
    |ascendingEigenvalue (hT.add hF) i - ascendingEigenvalue hT i| ≤ ε := by
  have h := HDP.Matrix.abs_hermitianOrderedEigenvalue_sub_le_operatorNorm
    (T + F) T (hT.add hF) hT i.rev
  have hd : T + F - T = F := by abel
  rw [hd] at h
  exact h.trans hbound

/-- Strict-count transport for one arbitrary Hermitian perturbation. The
weak conclusions retain the source conventions at repeated eigenvalues and
exact eigenvalue trials. The norm bound itself implies `0 ≤ ε`. -/
theorem noisy_rank_implications {n : ℕ}
    (T F : Matrix (Fin n) (Fin n) ℝ) (hT : T.IsHermitian) (hF : F.IsHermitian)
    {ε : ℝ} (hbound : realMatrixOperatorNorm F ≤ ε)
    (x : ℝ) (i : Fin n) :
    (strictBelowCount (ascendingEigenvalue (hT.add hF)) x ≤ i.val →
      x - ε ≤ ascendingEigenvalue hT i) ∧
    (i.val < strictBelowCount (ascendingEigenvalue (hT.add hF)) x →
      ascendingEigenvalue hT i ≤ x + ε) := by
  have he := abs_le.mp (ascendingEigenvalue_add_error T F hT hF hbound i)
  have hmono := ascendingEigenvalue_monotone (hT.add hF)
  constructor
  · intro hc
    have hv := le_of_strictBelowCount_le hmono x i hc
    linarith
  · intro hc
    have hv := lt_of_lt_strictBelowCount hmono x i hc
    linarith

/-- A bound on ordered eigenvalue movement gives a padded strict-count bracket. -/
theorem strictBelowCount_bracket_of_operatorNorm {n : ℕ}
    (A B : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsHermitian) (hB : B.IsHermitian)
    {ε : ℝ} (hbound : realMatrixOperatorNorm (B - A) ≤ ε) (x : ℝ) :
    strictBelowCount (ascendingEigenvalue hA) (x - ε) ≤
      strictBelowCount (ascendingEigenvalue hB) x ∧
    strictBelowCount (ascendingEigenvalue hB) x ≤
      strictBelowCount (ascendingEigenvalue hA) (x + ε) := by
  have error (i : Fin n) :
      |ascendingEigenvalue hB i - ascendingEigenvalue hA i| ≤ ε :=
    (HDP.Matrix.abs_hermitianOrderedEigenvalue_sub_le_operatorNorm B A hB hA i.rev).trans hbound
  constructor <;> apply Finset.card_le_card <;> intro i hi
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    linarith [(abs_le.mp (error i)).2]
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    linarith [(abs_le.mp (error i)).1]

end
end NumStability.NoisyRankCertificate
