import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.Probability.ProductMeasure

/-!
# Independent repetition until acceptance

For a fixed rejection set, each coordinate of the countable product law represents a
fresh trial. Counting one attempt for every prefix consisting entirely of rejections
includes the first successful attempt and represents an infinite run by `∞`.
-/

open MeasureTheory Set
open scoped ENNReal

namespace NumStability.IndependentRetry

variable {α : Type*}

/-- Streams whose first `m` trials all reject. -/
def rejectionPrefix (reject : Set α) (m : ℕ) : Set (ℕ → α) :=
  (↑(Finset.range m) : Set ℕ).pi (fun _ => reject)

@[simp] theorem mem_rejectionPrefix {reject : Set α} {m : ℕ} {x : ℕ → α} :
    x ∈ rejectionPrefix reject m ↔ ∀ j < m, x j ∈ reject := by
  simp [rejectionPrefix, Set.mem_pi]

/-- Number of trials through the first acceptance, including it. -/
noncomputable def retryCount (reject : Set α) (x : ℕ → α) : ℝ≥0∞ :=
  ∑' m : ℕ, (rejectionPrefix reject m).indicator (fun _ => 1) x

theorem retryCount_eq_of_first_accept {reject : Set α} {x : ℕ → α} {j : ℕ}
    (hreject : x ∈ rejectionPrefix reject j) (haccept : x j ∉ reject) :
    retryCount reject x = (j : ℝ≥0∞) + 1 := by
  classical
  unfold retryCount
  rw [tsum_eq_sum (s := Finset.range (j + 1))]
  · rw [Finset.sum_congr rfl (g := fun _ => (1 : ℝ≥0∞))]
    · simp
    · intro i hi
      apply Set.indicator_of_mem
      rw [mem_rejectionPrefix] at hreject ⊢
      exact fun k hk => hreject k (by have := Finset.mem_range.mp hi; omega)
  · intro i hi
    apply Set.indicator_of_notMem
    intro hx
    exact haccept (mem_rejectionPrefix.mp hx j (by simpa using hi))

theorem retryCount_tail_event (reject : Set α) (m : ℕ) :
    {x | (m : ℝ≥0∞) < retryCount reject x} = rejectionPrefix reject m := by
  classical
  ext x
  change (m : ℝ≥0∞) < retryCount reject x ↔ x ∈ rejectionPrefix reject m
  constructor
  · intro h
    by_contra hprefix
    have hExists : ∃ i : ℕ, x i ∉ reject := by
      by_contra hnone
      push_neg at hnone
      exact hprefix (mem_rejectionPrefix.mpr fun i _ => hnone i)
    have hfirst : x ∈ rejectionPrefix reject (Nat.find hExists) := by
      rw [mem_rejectionPrefix]
      exact fun i hi => not_not.mp (Nat.find_min hExists hi)
    have hj : Nat.find hExists < m := by
      by_contra! hj
      apply hprefix
      exact mem_rejectionPrefix.mpr fun i hi => mem_rejectionPrefix.mp hfirst i (hi.trans_le hj)
    rw [retryCount_eq_of_first_accept hfirst (Nat.find_spec hExists), ← Nat.cast_one,
      ← Nat.cast_add] at h
    exact (not_lt_of_ge (Nat.cast_le.mpr (Nat.succ_le_of_lt hj))) h
  · intro hx
    unfold retryCount
    have hsum : ∑ i ∈ Finset.range (m + 1), (rejectionPrefix reject i).indicator (fun _ => 1) x =
        (m : ℝ≥0∞) + 1 := by
      rw [Finset.sum_congr rfl (g := fun _ => (1 : ℝ≥0∞))]
      · simp
      · intro i hi
        apply Set.indicator_of_mem
        apply mem_rejectionPrefix.mpr
        exact fun j hj => mem_rejectionPrefix.mp hx j (by have := Finset.mem_range.mp hi; omega)
    have hle := ENNReal.sum_le_tsum (f := fun i =>
      (rejectionPrefix reject i).indicator (fun _ => 1) x) (Finset.range (m + 1))
    rw [hsum] at hle
    exact lt_of_lt_of_le (by norm_cast; omega) hle

/-- A stream has infinite length exactly when every trial rejects. -/
theorem retryCount_eq_top_iff {reject : Set α} {x : ℕ → α} :
    retryCount reject x = ⊤ ↔ ∀ j : ℕ, x j ∈ reject := by
  constructor
  · intro h j
    have hj : x ∈ {x | ((j + 1 : ℕ) : ℝ≥0∞) < retryCount reject x} := by simp [h]
    rw [retryCount_tail_event] at hj
    exact mem_rejectionPrefix.mp hj j (Nat.lt_succ_self j)
  · intro h
    by_contra hne
    obtain ⟨m, hm⟩ := ENNReal.exists_nat_gt hne
    have hx : x ∈ rejectionPrefix reject m := mem_rejectionPrefix.mpr fun j _ => h j
    rw [← retryCount_tail_event] at hx
    exact (not_lt_of_ge hm.le) hx

variable [MeasurableSpace α]

theorem measurableSet_rejectionPrefix {reject : Set α} (hr : MeasurableSet reject) (m : ℕ) :
    MeasurableSet (rejectionPrefix reject m) :=
  MeasurableSet.pi (to_countable _) fun _ _ => hr

theorem measurable_retryCount {reject : Set α} (hr : MeasurableSet reject) :
    Measurable (retryCount reject) :=
  Measurable.ennreal_tsum fun m => measurable_const.indicator (measurableSet_rejectionPrefix hr m)

variable (μ : Measure α) [IsProbabilityMeasure μ]

/-- The law of the full sequence of fresh trials with common one-trial law `μ`. -/
noncomputable abbrev streamMeasure : Measure (ℕ → α) := Measure.infinitePi fun _ : ℕ => μ

theorem measure_rejectionPrefix {reject : Set α} (hr : MeasurableSet reject) (m : ℕ) :
    streamMeasure μ (rejectionPrefix reject m) = μ reject ^ m := by
  unfold rejectionPrefix streamMeasure
  rw [Measure.infinitePi_pi (fun _ : ℕ => μ) (s := Finset.range m)
    (t := fun _ => reject) (fun _ _ => hr)]
  simp

theorem measure_retryCount_tail {reject : Set α} (hr : MeasurableSet reject) (m : ℕ) :
    streamMeasure μ {x | (m : ℝ≥0∞) < retryCount reject x} = μ reject ^ m := by
  rw [retryCount_tail_event, measure_rejectionPrefix μ hr]

omit [IsProbabilityMeasure μ] in
theorem lintegral_retryCount_eq_tsum_tails {reject : Set α} (hr : MeasurableSet reject) :
    ∫⁻ x, retryCount reject x ∂streamMeasure μ =
      ∑' m : ℕ, streamMeasure μ {x | (m : ℝ≥0∞) < retryCount reject x} := by
  simp_rw [retryCount_tail_event]
  unfold retryCount
  rw [lintegral_tsum]
  · exact tsum_congr fun m => lintegral_indicator_one (measurableSet_rejectionPrefix hr m)
  · exact fun m => (measurable_const.indicator (measurableSet_rejectionPrefix hr m)).aemeasurable

theorem lintegral_retryCount {reject : Set α} (hr : MeasurableSet reject) :
    ∫⁻ x, retryCount reject x ∂streamMeasure μ = (1 - μ reject)⁻¹ := by
  rw [lintegral_retryCount_eq_tsum_tails μ hr]
  simp only [measure_retryCount_tail μ hr, ENNReal.tsum_geometric]

theorem ae_exists_accept {reject : Set α} (hr : MeasurableSet reject)
    (hp : μ reject < 1) :
    ∀ᵐ x ∂streamMeasure μ, ∃ j : ℕ, x j ∉ reject := by
  rw [ae_iff]
  apply nonpos_iff_eq_zero.mp
  apply le_of_tendsto_of_tendsto' tendsto_const_nhds
    (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hp)
  intro m
  rw [← measure_rejectionPrefix μ hr m]
  apply measure_mono
  intro x hx
  have hnone : ¬ ∃ i : ℕ, x i ∉ reject := hx
  exact mem_rejectionPrefix.mpr fun j _ => Classical.not_exists_not.mp hnone j

/-- An affine pathwise work bound transfers retry tails to total work. -/
theorem measure_work_tail_le {reject : Set α} (hr : MeasurableSet reject)
    {work : (ℕ → α) → ℝ≥0∞} {scale : ℝ≥0∞} {β : ℝ≥0∞}
    (hwork : ∀ x, work x ≤ scale * (retryCount reject x + 1))
    (hβ : μ reject ≤ β) (m : ℕ) :
    streamMeasure μ {x | scale * ((m : ℝ≥0∞) + 1) < work x} ≤ β ^ m := by
  calc
    _ ≤ streamMeasure μ {x | (m : ℝ≥0∞) < retryCount reject x} := by
      apply measure_mono
      intro x hx
      change scale * ((m : ℝ≥0∞) + 1) < work x at hx
      change (m : ℝ≥0∞) < retryCount reject x
      by_contra! hm
      exact (not_lt_of_ge ((hwork x).trans (by gcongr))) hx
    _ = μ reject ^ m := measure_retryCount_tail μ hr m
    _ ≤ β ^ m := by gcongr

theorem lintegral_work_le {reject : Set α} (hr : MeasurableSet reject)
    {work : (ℕ → α) → ℝ≥0∞} {scale : ℝ≥0∞}
    (hwork : ∀ x, work x ≤ scale * (retryCount reject x + 1)) :
    ∫⁻ x, work x ∂streamMeasure μ ≤ scale * ((1 - μ reject)⁻¹ + 1) := by
  have hmeas := measurable_retryCount hr
  calc
    _ ≤ ∫⁻ x, scale * (retryCount reject x + 1) ∂streamMeasure μ := lintegral_mono hwork
    _ = _ := by
      rw [lintegral_const_mul _ (hmeas.add_const _), lintegral_add_left hmeas,
        lintegral_retryCount μ hr, lintegral_const, measure_univ, mul_one]

end NumStability.IndependentRetry
