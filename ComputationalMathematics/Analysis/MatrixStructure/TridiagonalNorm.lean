import ComputationalMathematics.Analysis.OperatorNorms.RealMatrix
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# Euclidean norm bound for a tridiagonal matrix

Absolute row and column sums give a dimension-free Euclidean operator bound.
For a tridiagonal matrix with diagonal entries bounded by `d` and both adjacent
bands bounded by `e`, this yields `d + 2*e`. No symmetry, sign, rank, or positive
dimension hypothesis is needed. The support premise is the transparent form
of the existing `IsTridiagonal` predicate, without an analysis-to-algorithm import.
-/

namespace NumStability

open scoped BigOperators
noncomputable section

/-- Equal nonnegative absolute row/column sum bounds control the Euclidean
vector action, including empty row or column index sets. -/
theorem rectOpNorm2Le_of_row_col_abs_sum_le {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) {C : ℝ} (hC : 0 ≤ C)
    (hrow : ∀ i, ∑ j, |A i j| ≤ C)
    (hcol : ∀ j, ∑ i, |A i j| ≤ C) : rectOpNorm2Le A C := by
  intro x
  have hrowSq (i : Fin m) :
      (∑ j, A i j * x j) ^ 2 ≤ C * ∑ j, |A i j| * x j ^ 2 := by
    have hcs := Finset.sum_sq_le_sum_mul_sum_of_sq_eq_mul
      (Finset.univ : Finset (Fin n))
      (r := fun j => A i j * x j)
      (f := fun j => |A i j|) (g := fun j => |A i j| * x j ^ 2)
      (fun j _ => abs_nonneg (A i j))
      (fun j _ => mul_nonneg (abs_nonneg _) (sq_nonneg _))
      (fun j _ => by rw [mul_pow, ← sq_abs (A i j)]; ring)
    exact hcs.trans (mul_le_mul_of_nonneg_right (hrow i)
      (Finset.sum_nonneg (fun j _ => mul_nonneg (abs_nonneg _) (sq_nonneg _))))
  have hsq : (∑ i, (∑ j, A i j * x j) ^ 2) ≤ C ^ 2 * ∑ j, x j ^ 2 := by
    calc
      (∑ i, (∑ j, A i j * x j) ^ 2)
          ≤ ∑ i, C * ∑ j, |A i j| * x j ^ 2 :=
            Finset.sum_le_sum (fun i _ => hrowSq i)
      _ = C * ∑ j, (∑ i, |A i j|) * x j ^ 2 := by
        rw [← Finset.mul_sum, Finset.sum_comm]
        congr 1
        apply Finset.sum_congr rfl
        intro j _
        rw [Finset.sum_mul]
      _ ≤ C * ∑ j, C * x j ^ 2 := by
        apply mul_le_mul_of_nonneg_left _ hC
        exact Finset.sum_le_sum (fun j _ =>
          mul_le_mul_of_nonneg_right (hcol j) (sq_nonneg _))
      _ = C ^ 2 * ∑ j, x j ^ 2 := by rw [← Finset.mul_sum]; ring
  have hnormsq : vecNorm2 (rectMatMulVec A x) ^ 2 ≤ (C * vecNorm2 x) ^ 2 := by
    simpa only [vecNorm2_sq, vecNorm2Sq, rectMatMulVec, mul_pow] using hsq
  have habs := (sq_le_sq).mp hnormsq
  simpa only [abs_of_nonneg (vecNorm2_nonneg _),
    abs_of_nonneg (mul_nonneg hC (vecNorm2_nonneg x))] using habs

/-- Source-independent Schur bound for the actual induced Euclidean norm. -/
theorem realMatrixOperatorNorm_le_of_row_col_abs_sum_le {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) {C : ℝ} (hC : 0 ≤ C)
    (hrow : ∀ i, ∑ j, |A i j| ≤ C)
    (hcol : ∀ j, ∑ i, |A i j| ≤ C) : realMatrixOperatorNorm A ≤ C := by
  have hA := rectOpNorm2Le_of_row_col_abs_sum_le A hC hrow hcol
  unfold realMatrixOperatorNorm
  apply ContinuousLinearMap.opNorm_le_bound (realMatrixContinuousLinearMap A) hC
  intro x
  have hnorm {d : ℕ} (z : Fin d → ℝ) :
      ‖WithLp.toLp 2 z‖ = vecNorm2 z := by
    rw [EuclideanSpace.norm_eq]
    simp only [Real.norm_eq_abs, sq_abs]
    rw [show ∑ i, z i ^ 2 = vecNorm2 z ^ 2 by exact (vecNorm2_sq z).symm]
    exact Real.sqrt_sq (vecNorm2_nonneg z)
  have hxnorm : ‖x‖ = vecNorm2 (WithLp.ofLp x) := by
    rw [← hnorm (WithLp.ofLp x)]
  have haction : ‖realMatrixContinuousLinearMap A x‖ =
      vecNorm2 (rectMatMulVec A (WithLp.ofLp x)) := by
    rw [← hnorm]
    rfl
  rw [haction, hxnorm]
  exact hA (WithLp.ofLp x)

private theorem sum_indicator_le_of_injective {ι κ : Type*} [Fintype ι]
    [DecidableEq κ] (f : ι → κ) (hf : Function.Injective f) (k : κ)
    {e : ℝ} (he : 0 ≤ e) :
    (∑ i, if f i = k then e else 0) ≤ e := by
  classical
  by_cases hex : ∃ j, f j = k
  · obtain ⟨j, hj⟩ := hex
    have heq (i : ι) : (f i = k) ↔ i = j := by
      rw [← hj]
      exact hf.eq_iff
    simp only [heq]
    simp
  · have hne (i : ι) : f i ≠ k := by
      intro hi
      exact hex ⟨i, hi⟩
    simpa only [hne, if_false, Finset.sum_const_zero] using he

/-- Each absolute row sum of a tridiagonal matrix is at most `d+2e`.
The support premise is precisely the existing tridiagonal sparsity condition. -/
theorem tridiagonal_abs_row_sum_le {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) {d e : ℝ} (he : 0 ≤ e)
    (hband : ∀ i j, (i.val + 1 < j.val ∨ j.val + 1 < i.val) → A i j = 0)
    (hdiag : ∀ i, |A i i| ≤ d)
    (hoff : ∀ i j, (i.val + 1 = j.val ∨ j.val + 1 = i.val) → |A i j| ≤ e)
    (i : Fin n) : ∑ j, |A i j| ≤ d + 2 * e := by
  classical
  have hentry (j : Fin n) : |A i j| ≤
      (if j = i then d else 0) +
      (if j.val + 1 = i.val then e else 0) +
      (if i.val + 1 = j.val then e else 0) := by
    by_cases hji : j = i
    · subst j
      have hne : ¬ i.val + 1 = i.val := by omega
      simpa only [if_pos rfl, if_neg hne, add_zero] using hdiag i
    · by_cases hlo : j.val + 1 = i.val
      · have hup : ¬ i.val + 1 = j.val := by omega
        simpa only [if_neg hji, if_pos hlo, if_neg hup, zero_add, add_zero] using
          hoff i j (Or.inr hlo)
      · by_cases hup : i.val + 1 = j.val
        · simpa only [if_neg hji, if_neg hlo, if_pos hup, zero_add] using
            hoff i j (Or.inl hup)
        · have hzero : A i j = 0 := hband i j (by
            have hv : i.val ≠ j.val := by
              intro h
              exact hji (Fin.ext h.symm)
            omega)
          simp only [hzero, abs_zero, if_neg hji, if_neg hlo, if_neg hup, add_zero, le_refl]
  have hlo := sum_indicator_le_of_injective
    (fun j : Fin n => j.val + 1) (by intro a b h; apply Fin.ext; dsimp at h; omega) i.val he
  have hup := sum_indicator_le_of_injective
    (fun j : Fin n => j.val) Fin.val_injective (i.val + 1) he
  have hup' : (∑ j : Fin n, if i.val + 1 = j.val then e else 0) ≤ e := by
    simpa only [eq_comm] using hup
  calc
    (∑ j, |A i j|) ≤ ∑ j,
        ((if j = i then d else 0) +
        (if j.val + 1 = i.val then e else 0) +
        (if i.val + 1 = j.val then e else 0)) :=
          Finset.sum_le_sum (fun j _ => hentry j)
    _ = d + (∑ j : Fin n, if j.val + 1 = i.val then e else 0) +
        (∑ j : Fin n, if i.val + 1 = j.val then e else 0) := by
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
      simp
    _ ≤ d + 2 * e := by linarith

/-- A tridiagonal matrix with diagonal bound `d` and both adjacent-band bounds
`e` has induced Euclidean norm at most `d+2e`, with no dimension factor. This
includes dimensions zero and one, and does not require symmetry or signs. -/
theorem realMatrixOperatorNorm_le_of_tridiagonal {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) {d e : ℝ} (hd : 0 ≤ d) (he : 0 ≤ e)
    (hband : ∀ i j, (i.val + 1 < j.val ∨ j.val + 1 < i.val) → A i j = 0)
    (hdiag : ∀ i, |A i i| ≤ d)
    (hoff : ∀ i j, (i.val + 1 = j.val ∨ j.val + 1 = i.val) → |A i j| ≤ e) :
    realMatrixOperatorNorm A ≤ d + 2 * e := by
  apply realMatrixOperatorNorm_le_of_row_col_abs_sum_le A (by positivity)
  · exact tridiagonal_abs_row_sum_le A he hband hdiag hoff
  · apply tridiagonal_abs_row_sum_le (fun i j => A j i) he
    · intro i j hij
      exact hband j i hij.symm
    · exact hdiag
    · intro i j hij
      exact hoff j i hij.symm

end
end NumStability
