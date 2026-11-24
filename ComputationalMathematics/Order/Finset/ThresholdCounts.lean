import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.NormNum

/-!
# Raw threshold counts of ascending finite real lists

Counts retain multiplicities and are real-valued before subtraction. Neither
nonempty lists nor strict value ordering are required. This file has no
integration, matrix, or probability-normalization dependencies.
-/

namespace NumStability.OrderStatistics

noncomputable section

/-- Raw count, with occurrences indexed by Fin n, including repeated values. -/
def countLE {n : ℕ} (a : Fin n → ℝ) (x : ℝ) : ℝ :=
  ∑ i, if a i ≤ x then 1 else 0

theorem countLE_eq_card {n : ℕ} (a : Fin n → ℝ) (x : ℝ) :
    countLE a x = ((Finset.univ.filter (fun i => a i ≤ x)).card : ℝ) := by
  classical
  simp [countLE]

/-- Sublevel sets of monotone lists are initial segments. Comparing their
cardinalities compares each coordinate's threshold indicator. -/
theorem indicator_le_of_countLE_le {n : ℕ} (a b : Fin n → ℝ)
    (ha : Monotone a) (hb : Monotone b) (x : ℝ) (hc : countLE a x ≤ countLE b x)
    (i : Fin n) : (if a i ≤ x then (1 : ℝ) else 0) ≤ (if b i ≤ x then 1 else 0) := by
  classical
  rw [countLE_eq_card, countLE_eq_card] at hc
  have hcard : (Finset.univ.filter (fun j => a j ≤ x)).card ≤
      (Finset.univ.filter (fun j => b j ≤ x)).card := by exact_mod_cast hc
  by_cases hai : a i ≤ x
  · have hi : i.val < (Finset.univ.filter (fun j => a j ≤ x)).card :=
      (Tuple.lt_card_le_iff_apply_le_of_monotone ha).mpr hai
    have hbi : b i ≤ x := (Tuple.lt_card_le_iff_apply_le_of_monotone hb).mp
      (hi.trans_le hcard)
    simp [hai, hbi]
  · split_ifs <;> norm_num

private theorem abs_countLE_sub_eq_sum_of_le {n : ℕ} (a b : Fin n → ℝ)
    (ha : Monotone a) (hb : Monotone b) (x : ℝ) (hc : countLE a x ≤ countLE b x) :
    |countLE a x - countLE b x| =
      ∑ i, |(if a i ≤ x then (1 : ℝ) else 0) - (if b i ≤ x then 1 else 0)| := by
  classical
  rw [abs_of_nonpos (sub_nonpos.mpr hc), neg_sub]
  calc
    countLE b x - countLE a x =
        ∑ i, ((if b i ≤ x then (1 : ℝ) else 0) - (if a i ≤ x then 1 else 0)) := by
      simp only [countLE, Finset.sum_sub_distrib]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      rw [abs_of_nonpos (sub_nonpos.mpr (indicator_le_of_countLE_le a b ha hb x hc i)), neg_sub]

/-- Equal-length monotone matching has no cancellation between threshold
indicator differences, pointwise at every x, including endpoint ties. -/
theorem abs_countLE_sub_eq_sum {n : ℕ} (a b : Fin n → ℝ)
    (ha : Monotone a) (hb : Monotone b) (x : ℝ) :
    |countLE a x - countLE b x| =
      ∑ i, |(if a i ≤ x then (1 : ℝ) else 0) - (if b i ≤ x then 1 else 0)| := by
  classical
  rcases le_total (countLE a x) (countLE b x) with h | h
  · exact abs_countLE_sub_eq_sum_of_le a b ha hb x h
  · rw [abs_sub_comm, abs_countLE_sub_eq_sum_of_le b a hb ha x h]
    exact Finset.sum_congr rfl (fun i _ => abs_sub_comm _ _)

end
end NumStability.OrderStatistics
