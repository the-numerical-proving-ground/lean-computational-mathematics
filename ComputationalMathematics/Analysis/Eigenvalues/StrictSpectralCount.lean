import ComputationalMathematics.Analysis.Eigenvalues.CourantFischer
import Mathlib.Order.Interval.Finset.Fin

/-!
# Ascending Hermitian eigenvalues and strict-below counts

The ascending index reverses the decreasing index of the Hermitian spectrum.
Strict-below counts on a monotone list determine where a trial lies relative
to its indexed value, including at repeated values.
-/

namespace NumStability.NoisyRankCertificate

noncomputable section
open Classical

/-- Number of positions of a finite real list strictly below the trial. -/
def strictBelowCount {n : ℕ} (f : Fin n → ℝ) (x : ℝ) : ℕ :=
  (Finset.univ.filter fun j => f j < x).card

/-- A strict-below count at most the zero-based index forces the trial below
or equal to the value at that index. Equal and repeated values are allowed. -/
theorem le_of_strictBelowCount_le {n : ℕ} {f : Fin n → ℝ}
    (hf : Monotone f) (x : ℝ) (i : Fin n)
    (hcount : strictBelowCount f x ≤ i.val) : x ≤ f i := by
  by_contra h
  have hfi : f i < x := lt_of_not_ge h
  have hsub : Finset.Iic i ⊆ Finset.univ.filter (fun j => f j < x) := by
    intro j hj
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      (hf (Finset.mem_Iic.mp hj)).trans_lt hfi⟩
  have hc := Finset.card_le_card hsub
  have : i.val + 1 ≤ strictBelowCount f x := by
    simpa [strictBelowCount] using hc
  omega

/-- More strict-below positions than the zero-based index forces the value
at that index strictly below the trial. -/
theorem lt_of_lt_strictBelowCount {n : ℕ} {f : Fin n → ℝ}
    (hf : Monotone f) (x : ℝ) (i : Fin n)
    (hcount : i.val < strictBelowCount f x) : f i < x := by
  by_contra h
  have hfi : x ≤ f i := le_of_not_gt h
  have hsub : Finset.univ.filter (fun j => f j < x) ⊆ Finset.Iio i := by
    intro j hj
    have hjx := (Finset.mem_filter.mp hj).2
    apply Finset.mem_Iio.mpr
    by_contra hji
    have hij : i ≤ j := le_of_not_gt hji
    exact (not_lt_of_ge (hfi.trans (hf hij))) hjx
  have hc := Finset.card_le_card hsub
  have : strictBelowCount f x ≤ i.val := by
    simpa [strictBelowCount] using hc
  omega

/-- Ascending position `i` is position `i.rev` in the actual decreasing
Hermitian eigenvalue API. -/
def ascendingEigenvalue {n : ℕ} {T : Matrix (Fin n) (Fin n) ℝ}
    (hT : T.IsHermitian) (i : Fin n) : ℝ :=
  hermitianOrderedEigenvalue hT i.rev

theorem ascendingEigenvalue_monotone {n : ℕ} {T : Matrix (Fin n) (Fin n) ℝ}
    (hT : T.IsHermitian) : Monotone (ascendingEigenvalue hT) := by
  intro i j hij
  exact hermitianOrderedEigenvalue_antitone hT (Fin.rev_anti hij)

end
end NumStability.NoisyRankCertificate
