import Mathlib.Analysis.Matrix.Spectrum

/-! Real diagonal perturbations of complex Hermitian matrices and their adjacent gap events. -/

namespace Matrix

/-- Add a real vector of shifts to the diagonal of a complex matrix. -/
def diagonalPerturbation {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (v : Fin n → ℝ) :
    Matrix (Fin n) (Fin n) ℂ :=
  A + diagonal (fun i => (v i : ℂ))

namespace IsHermitian

theorem diagonalPerturbation {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ}
    (hA : A.IsHermitian) (v : Fin n → ℝ) : (A.diagonalPerturbation v).IsHermitian := by
  apply hA.add
  rw [isHermitian_diagonal_iff]
  intro i
  exact Complex.conj_ofReal (v i)

/-- The event that the gap starting at zero-based increasing rank `j` is at most `g`.
Mathlib's eigenvalues are decreasing, so the adjacent ranks are reversed. -/
noncomputable def specifiedAdjacentGapEvent {n : ℕ}
    {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    (hA : A.IsHermitian) (j : Fin n) (g : ℝ) : Set (Fin (n + 1) → ℝ) :=
  {v |
    let eig := (isHermitian_iff_isSymmetric.mp (hA.diagonalPerturbation v)).eigenvalues
      finrank_euclideanSpace_fin
    eig j.rev.castSucc - eig j.rev.succ ≤ g}

end IsHermitian
end Matrix
