import ComputationalMathematics.Order.Finset.ThresholdCounts
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic.Linarith

/-!
# Finite-list L1 matching through raw count differences

Only differences of equal-cardinality raw counts are integrated. Individual
nonempty-list count functions have a nonzero right tail and are not integrable
on the real line. Weak monotonicity allows ties and Fin 0 throughout.
-/

namespace NumStability.OrderStatistics

noncomputable section

open MeasureTheory

/-- The threshold convention a≤x makes the exact interval [a,b), including
its left endpoint and excluding its right endpoint. -/
theorem threshold_sub_eq_indicator_of_le {a b : ℝ} (hab : a ≤ b) (x : ℝ) :
    (if a ≤ x then (1 : ℝ) else 0) - (if b ≤ x then 1 else 0) =
      (Set.Ico a b).indicator (fun _ : ℝ => (1 : ℝ)) x := by
  by_cases ha : a ≤ x
  · by_cases hb : b ≤ x
    · simp [ha, hb, Set.mem_Ico, not_lt.mpr hb]
    · simp [ha, hb, Set.mem_Ico, lt_of_not_ge hb]
  · have hb : ¬ b ≤ x := fun h => ha (hab.trans h)
    simp [ha, hb, Set.mem_Ico]

theorem integrable_Ico_one (a b : ℝ) :
    Integrable ((Set.Ico a b).indicator (fun _ : ℝ => (1 : ℝ))) := by
  have h : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Set.Ico a b) :=
    integrableOn_const (by simp [Real.volume_Ico])
  exact h.integrable_indicator measurableSet_Ico

/-- Signed threshold differences are integrable for arbitrary endpoints,
including equal endpoints. The individual half-line indicators are not used
as separately integrable functions. -/
theorem integrable_threshold_sub (a b : ℝ) :
    Integrable (fun x : ℝ =>
      (if a ≤ x then (1 : ℝ) else 0) - (if b ≤ x then 1 else 0)) := by
  rcases le_total a b with hab | hba
  · simpa only [threshold_sub_eq_indicator_of_le hab] using integrable_Ico_one a b
  · have heq : (fun x : ℝ =>
        (if a ≤ x then (1 : ℝ) else 0) - (if b ≤ x then 1 else 0)) =
        fun x => -(Set.Ico b a).indicator (fun _ : ℝ => (1 : ℝ)) x := by
      funext x
      rw [← threshold_sub_eq_indicator_of_le hba x]
      ring
    rw [heq]
    exact (integrable_Ico_one b a).neg

private theorem integral_abs_threshold_sub_of_le {a b : ℝ} (hab : a ≤ b) :
    (∫ x : ℝ, |(if a ≤ x then (1 : ℝ) else 0) - (if b ≤ x then 1 else 0)|) =
      |a - b| := by
  have heq : (fun x : ℝ =>
      |(if a ≤ x then (1 : ℝ) else 0) - (if b ≤ x then 1 else 0)|) =
      (Set.Ico a b).indicator (fun _ : ℝ => (1 : ℝ)) := by
    funext x
    rw [threshold_sub_eq_indicator_of_le hab x]
    apply abs_of_nonneg
    exact Set.indicator_nonneg (fun _ _ => by norm_num) _
  rw [heq, integral_indicator_const (1 : ℝ) measurableSet_Ico,
    Real.volume_real_Ico_of_le hab]
  simp only [smul_eq_mul, mul_one, abs_of_nonpos (sub_nonpos.mpr hab), neg_sub]

/-- Exact scalar contribution to the count-difference integral. -/
theorem integral_abs_threshold_sub (a b : ℝ) :
    (∫ x : ℝ, |(if a ≤ x then (1 : ℝ) else 0) - (if b ≤ x then 1 else 0)|) =
      |a - b| := by
  rcases le_total a b with hab | hba
  · exact integral_abs_threshold_sub_of_le hab
  · calc
      _ = ∫ x : ℝ, |(if b ≤ x then (1 : ℝ) else 0) - (if a ≤ x then 1 else 0)| := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall (fun _ => abs_sub_comm _ _)
      _ = |b - a| := integral_abs_threshold_sub_of_le hba
      _ = _ := abs_sub_comm _ _

/-- Equal-length count DIFFERENCES are integrable, without requiring the
lists to be sorted, nonnegative, nonempty, or distinct-valued. -/
theorem integrable_countLE_sub {n : ℕ} (a b : Fin n → ℝ) :
    Integrable (fun x : ℝ => countLE a x - countLE b x) := by
  classical
  have h := integrable_finset_sum Finset.univ (fun i _ => integrable_threshold_sub (a i) (b i))
  simpa only [countLE, Finset.sum_sub_distrib] using h

/-- Raw finite-list L1/CDF identity, preserving multiplicities and Fin 0. -/
theorem sum_abs_sub_eq_integral_countLE {n : ℕ} (a b : Fin n → ℝ)
    (ha : Monotone a) (hb : Monotone b) :
    (∑ i, |a i - b i|) = ∫ x : ℝ, |countLE a x - countLE b x| := by
  classical
  calc
    _ = ∑ i, ∫ x : ℝ,
        |(if a i ≤ x then (1 : ℝ) else 0) - (if b i ≤ x then 1 else 0)| := by
      exact Finset.sum_congr rfl (fun i _ => (integral_abs_threshold_sub (a i) (b i)).symm)
    _ = ∫ x : ℝ, ∑ i,
        |(if a i ≤ x then (1 : ℝ) else 0) - (if b i ≤ x then 1 else 0)| := by
      exact (integral_finset_sum Finset.univ
        (fun i _ => (integrable_threshold_sub (a i) (b i)).abs)).symm
    _ = _ := integral_congr_ae (Filter.Eventually.of_forall
      (fun x => (abs_countLE_sub_eq_sum a b ha hb x).symm))

/-- Matching distance between equally long ordered lists; no normalization. -/
def matchingL1 {n : ℕ} (a b : Fin n → ℝ) : ℝ := ∑ i, |a i - b i|

theorem matchingL1_eq_integral_countLE {n : ℕ} (a b : Fin n → ℝ)
    (ha : Monotone a) (hb : Monotone b) :
    matchingL1 a b = ∫ x : ℝ, |countLE a x - countLE b x| :=
  sum_abs_sub_eq_integral_countLE a b ha hb

/-- Exact six-list deletion/cancellation inequality from actual count splits.
The split hypotheses express multiset unions, not a matching-error conclusion.
Pairwise equal cardinalities supply all integrability premises. -/
theorem matchingL1_cancel_splits {n k m : ℕ}
    (w lambda : Fin n → ℝ) (s u : Fin k → ℝ) (t v : Fin m → ℝ)
    (hw : Monotone w) (hlambda : Monotone lambda) (hs : Monotone s)
    (hu : Monotone u) (ht : Monotone t) (hv : Monotone v)
    (hsplitw : ∀ x, countLE w x = countLE s x + countLE t x)
    (hsplitlambda : ∀ x, countLE lambda x = countLE u x + countLE v x) :
    matchingL1 t v ≤ matchingL1 w lambda + matchingL1 s u := by
  rw [matchingL1_eq_integral_countLE t v ht hv,
    matchingL1_eq_integral_countLE w lambda hw hlambda,
    matchingL1_eq_integral_countLE s u hs hu]
  have hwint := (integrable_countLE_sub w lambda).abs
  have hsint := (integrable_countLE_sub s u).abs
  calc
    _ ≤ ∫ x : ℝ, (|countLE w x - countLE lambda x| + |countLE s x - countLE u x|) := by
      apply integral_mono (integrable_countLE_sub t v).abs (hwint.add hsint)
      intro x
      have heq : countLE t x - countLE v x =
          (countLE w x - countLE lambda x) - (countLE s x - countLE u x) := by
        rw [hsplitw x, hsplitlambda x]
        ring
      change |countLE t x - countLE v x| ≤
        |countLE w x - countLE lambda x| + |countLE s x - countLE u x|
      rw [heq]
      simpa only [sub_zero, zero_sub, abs_neg] using abs_sub_le (countLE w x - countLE lambda x) 0 (countLE s x - countLE u x)
    _ = _ := integral_add hwint hsint

end
end NumStability.OrderStatistics
