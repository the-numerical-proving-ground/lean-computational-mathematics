import ComputationalMathematics.Analysis.MatrixStructure.TridiagonalNorm
import Mathlib.Data.Matrix.Basis
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Abel

/-!
# Real symmetric tridiagonal matrices with consecutive edges
-/

namespace NumStability

open scoped BigOperators Matrix
noncomputable section

/-- Symmetric tridiagonal with specified diagonal and consecutive edges. -/
def sturmTridiagonal {n : ℕ} (e : Fin (n + 1) → ℝ) (s : Fin n → ℝ) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  Matrix.diagonal e + ∑ i : Fin n,
    (Matrix.single i.castSucc i.succ (s i) + Matrix.single i.succ i.castSucc (s i))

theorem sturmTridiagonal_isHermitian {n : ℕ} (e : Fin (n + 1) → ℝ) (s : Fin n → ℝ) :
    (sturmTridiagonal e s).IsHermitian := by
  unfold Matrix.IsHermitian sturmTridiagonal
  simp only [Matrix.conjTranspose_add, Matrix.conjTranspose_sum, Matrix.diagonal_conjTranspose,
    Matrix.conjTranspose_single, star_trivial]
  congr 1
  apply Finset.sum_congr rfl
  intro i _hi
  exact add_comm _ _

/-- Every entry outside the diagonal and its two neighbors is zero. -/
theorem sturmTridiagonal_support {n : ℕ} (e : Fin (n + 1) → ℝ) (s : Fin n → ℝ)
    (i j : Fin (n + 1)) (hij : i ≠ j)
    (hupper : i.val + 1 ≠ j.val) (hlower : j.val + 1 ≠ i.val) :
    sturmTridiagonal e s i j = 0 := by
  classical
  simp only [sturmTridiagonal, Matrix.add_apply, Matrix.diagonal_apply_ne _ hij]
  have hz : ∀ k : Fin n,
      (Matrix.single k.castSucc k.succ (s k) +
        Matrix.single k.succ k.castSucc (s k)) i j = 0 := by
    intro k
    have hu : ¬(k.castSucc = i ∧ k.succ = j) := by
      rintro ⟨rfl, rfl⟩
      exact hupper rfl
    have hl : ¬(k.succ = i ∧ k.castSucc = j) := by
      rintro ⟨rfl, rfl⟩
      exact hlower rfl
    simp [hu, hl]
  simp [Matrix.sum_apply, hz]

theorem sturmTridiagonal_diagonal {n : ℕ} (e : Fin (n + 1) → ℝ) (s : Fin n → ℝ)
    (i : Fin (n + 1)) : sturmTridiagonal e s i i = e i := by
  classical
  have hz : ∀ k : Fin n,
      (Matrix.single k.castSucc k.succ (s k) +
        Matrix.single k.succ k.castSucc (s k)) i i = 0 := by
    intro k
    have hu : ¬(k.castSucc = i ∧ k.succ = i) := by
      rintro ⟨h1, h2⟩
      have hv1 := congr_arg Fin.val h1
      have hv2 := congr_arg Fin.val h2
      simp only [Fin.val_castSucc, Fin.val_succ] at hv1 hv2
      omega
    have hl : ¬(k.succ = i ∧ k.castSucc = i) := by
      exact fun h => hu ⟨h.2, h.1⟩
    simp [hu, hl]
  simp [sturmTridiagonal, Matrix.sum_apply, hz]

/-- Taking the image of a coordinate unit vector bounds each matrix entry. -/
theorem abs_matrix_entry_le_realMatrixOperatorNorm {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (i : Fin m) (j : Fin n) :
    |A i j| ≤ realMatrixOperatorNorm A := by
  let u := EuclideanSpace.single j (1 : ℝ)
  let v := realMatrixContinuousLinearMap A u
  have hv : v i = A i j := by
    change (A *ᵥ Pi.single j 1) i = A i j
    rw [Matrix.mulVec_single_one]
    rfl
  have hcoord : |v i| ≤ ‖v‖ := by
    simpa only [Real.norm_eq_abs] using
      (PiLp.norm_apply_le (p := (2 : ENNReal)) v i)
  have hop : ‖v‖ ≤ realMatrixOperatorNorm A := by
    simpa [u, v, realMatrixOperatorNorm] using
      ContinuousLinearMap.le_opNorm (realMatrixContinuousLinearMap A) u
  rw [← hv]
  exact hcoord.trans hop

/-- In particular, the operator bound controls every diagonal entry. -/
theorem sturmTridiagonal_abs_diagonal_le_operatorNorm {n : ℕ}
    (a : Fin (n + 1) → ℝ) (b : Fin n → ℝ) (i : Fin (n + 1)) :
    |a i| ≤ realMatrixOperatorNorm (sturmTridiagonal a b) := by
  rw [← sturmTridiagonal_diagonal a b i]
  exact abs_matrix_entry_le_realMatrixOperatorNorm _ i i

theorem sturmTridiagonal_upper {n : ℕ} (e : Fin (n + 1) → ℝ) (s : Fin n → ℝ)
    (k : Fin n) : sturmTridiagonal e s k.castSucc k.succ = s k := by
  classical
  have hne : k.castSucc ≠ k.succ := by
    intro h
    have hv := congr_arg Fin.val h
    simp only [Fin.val_castSucc, Fin.val_succ] at hv
    omega
  have hterm : ∀ j : Fin n,
      (Matrix.single j.castSucc j.succ (s j) +
        Matrix.single j.succ j.castSucc (s j)) k.castSucc k.succ =
          if j = k then s k else 0 := by
    intro j
    have hl : ¬(j.succ = k.castSucc ∧ j.castSucc = k.succ) := by
      rintro ⟨h1, h2⟩
      have hv1 := congr_arg Fin.val h1
      have hv2 := congr_arg Fin.val h2
      simp only [Fin.val_castSucc, Fin.val_succ] at hv1 hv2
      omega
    by_cases hj : j = k
    · subst j
      simp [hl]
    · have hu : ¬(j.castSucc = k.castSucc ∧ j.succ = k.succ) := by
        exact fun h => hj (Fin.castSucc_inj.mp h.1)
      simp [hl, hj]
  simp only [sturmTridiagonal, Matrix.add_apply, Matrix.diagonal_apply_ne _ hne]
  simp [Matrix.sum_apply, hterm]

theorem sturmTridiagonal_lower {n : ℕ} (e : Fin (n + 1) → ℝ) (s : Fin n → ℝ)
    (k : Fin n) : sturmTridiagonal e s k.succ k.castSucc = s k := by
  have h := congr_arg (fun A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ =>
    A k.castSucc k.succ) (sturmTridiagonal_isHermitian e s)
  simpa only [Matrix.conjTranspose_apply, star_trivial, sturmTridiagonal_upper] using h

/-- Entrywise addition is compatible with the transparent tridiagonal builder. -/
theorem sturmTridiagonal_add {n : ℕ} (e f : Fin (n + 1) → ℝ) (s t : Fin n → ℝ) :
    sturmTridiagonal (e + f) (s + t) = sturmTridiagonal e s + sturmTridiagonal f t := by
  have hdiag : Matrix.diagonal (e + f) = Matrix.diagonal e + Matrix.diagonal f := by
    ext i j
    by_cases h : i = j <;> simp [h]
  simp only [sturmTridiagonal, hdiag, Pi.add_apply,
    Matrix.single_add, Finset.sum_add_distrib]
  abel

/-- Subtracting two tridiagonal matrices subtracts their diagonals and edges. -/
theorem sturmTridiagonal_sub {n : ℕ} (a c : Fin (n + 1) → ℝ) (b e : Fin n → ℝ) :
    sturmTridiagonal (a - c) (b - e) = sturmTridiagonal a b - sturmTridiagonal c e := by
  apply eq_sub_iff_add_eq.mpr
  rw [← sturmTridiagonal_add, sub_add_cancel, sub_add_cancel]

theorem sturmTridiagonal_band {n : ℕ} (e : Fin (n + 1) → ℝ) (s : Fin n → ℝ)
    (i j : Fin (n + 1)) (hij : i.val + 1 < j.val ∨ j.val + 1 < i.val) :
    sturmTridiagonal e s i j = 0 := by
  apply sturmTridiagonal_support e s i j
  · intro h
    have hv := congr_arg Fin.val h
    omega
  · omega
  · omega

/-- Both adjacent bands inherit the bounds on the given edge vector. -/
theorem sturmTridiagonal_adjacent_bound {n : ℕ} (e : Fin (n + 1) → ℝ) (s : Fin n → ℝ)
    {E : ℝ} (hs : ∀ k, |s k| ≤ E) (i j : Fin (n + 1))
    (hij : i.val + 1 = j.val ∨ j.val + 1 = i.val) :
    |sturmTridiagonal e s i j| ≤ E := by
  rcases hij with hu | hl
  · let k : Fin n := ⟨i.val, by have hj := j.isLt; omega⟩
    have hki : k.castSucc = i := Fin.ext rfl
    have hkj : k.succ = j := Fin.ext hu
    rw [← hki, ← hkj, sturmTridiagonal_upper]
    exact hs k
  · let k : Fin n := ⟨j.val, by have hi := i.isLt; omega⟩
    have hkj : k.castSucc = j := Fin.ext rfl
    have hki : k.succ = i := Fin.ext hl
    rw [← hki, ← hkj, sturmTridiagonal_lower]
    exact hs k

/-- The diagonal and two adjacent bands, rather than dimension, control the
operator norm of this finite tridiagonal builder. -/
theorem sturmTridiagonal_operatorNorm_le {n : ℕ}
    (e : Fin (n + 1) → ℝ) (s : Fin n → ℝ) {D E : ℝ}
    (hD : 0 ≤ D) (hE : 0 ≤ E) (he : ∀ i, |e i| ≤ D) (hs : ∀ i, |s i| ≤ E) :
    realMatrixOperatorNorm (sturmTridiagonal e s) ≤ D + 2 * E := by
  apply realMatrixOperatorNorm_le_of_tridiagonal (sturmTridiagonal e s) hD hE
  · exact sturmTridiagonal_band e s
  · intro i
    simpa only [sturmTridiagonal_diagonal] using he i
  · exact sturmTridiagonal_adjacent_bound e s hs

end
end NumStability
