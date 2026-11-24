import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Data.Real.Sign
import Mathlib.Probability.Distributions.Cauchy

/-! The Poisson kernel for the upper half-plane and its integral formulas. -/

open Filter MeasureTheory
open scoped NNReal Topology

namespace NumStability

/-- The unnormalized Poisson kernel of height `y` centered at `c`. -/
noncomputable def poissonKernel (y c x : ℝ) : ℝ :=
  y / ((x - c) ^ 2 + y ^ 2)

theorem poissonKernel_nonneg {y : ℝ} (hy : 0 ≤ y) (c x : ℝ) :
    0 ≤ poissonKernel y c x :=
  div_nonneg hy (by positivity)

theorem continuous_poissonKernel {y : ℝ} (hy : y ≠ 0) (c : ℝ) :
    Continuous (poissonKernel y c) := by
  unfold poissonKernel
  apply continuous_const.div (by fun_prop)
  intro x
  exact ne_of_gt (add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_ne_zero hy))

/-- The imaginary part of a reciprocal with a pole at `z` is a Poisson kernel. -/
theorem im_inv_ofReal_sub_eq_poissonKernel (z : ℂ) (x : ℝ) :
    (((x : ℂ) - z)⁻¹).im = poissonKernel z.im z.re x := by
  simp [Complex.inv_im, Complex.normSq_apply, Complex.sub_re, Complex.sub_im, poissonKernel, pow_two]

/-- The Poisson kernel has integral `π` on the real line at every positive height. -/
theorem integral_poissonKernel (c : ℝ) {y : ℝ} (hy : 0 < y) :
    ∫ x : ℝ, poissonKernel y c x = Real.pi := by
  let γ : ℝ≥0 := ⟨y, hy.le⟩
  have hγ : γ ≠ 0 := fun h => hy.ne' (congrArg NNReal.toReal h)
  have h (x : ℝ) : poissonKernel y c x = Real.pi * Probability.cauchyPDFReal c γ x := by
    rw [poissonKernel, Probability.cauchyPDFReal_def, div_eq_mul_inv]
    change _ = Real.pi * (Real.pi⁻¹ * y * _)
    rw [← mul_assoc, ← mul_assoc, mul_inv_cancel₀ Real.pi_ne_zero, one_mul]
    rfl
  simp only [h, integral_const_mul, Probability.integral_cauchyPDFReal c hγ, mul_one]

/-- On an interval, the integral is a difference of arctangents. -/
theorem intervalIntegral_poissonKernel (c a b : ℝ) {y : ℝ} (hy : y ≠ 0) :
    ∫ x in a..b, poissonKernel y c x =
      Real.arctan ((b - c) / y) - Real.arctan ((a - c) / y) := by
  simp only [poissonKernel, div_eq_mul_inv]
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_comp_sub_right (f := fun x => (x ^ 2 + y ^ 2)⁻¹)]
  simp_rw [add_comm _ (y ^ 2)]
  rw [integral_inv_sq_add_sq hy, ← mul_assoc, mul_inv_cancel₀ hy, one_mul]
  simp only [div_eq_mul_inv]

private theorem tendsto_arctan_const_div (d : ℝ) :
    Tendsto (fun y : ℝ => Real.arctan (d / y)) (𝓝[>] 0)
      (𝓝 (Real.sign d * (Real.pi / 2))) := by
  rcases lt_trichotomy d 0 with hd | rfl | hd
  · simpa only [Real.sign_of_neg hd, neg_one_mul, div_eq_mul_inv] using
      (tendsto_nhds_of_tendsto_nhdsWithin Real.tendsto_arctan_atBot).comp
        ((tendsto_inv_nhdsGT_zero (𝕜 := ℝ)).const_mul_atTop_of_neg hd)
  · simp
  · simpa only [Real.sign_of_pos hd, one_mul, div_eq_mul_inv] using
      (tendsto_nhds_of_tendsto_nhdsWithin Real.tendsto_arctan_atTop).comp
        ((tendsto_inv_nhdsGT_zero (𝕜 := ℝ)).const_mul_atTop hd)

/-- As the height decreases to zero, an interval captures full mass at an
interior center and half mass at a boundary center. -/
theorem tendsto_intervalIntegral_poissonKernel (c a b : ℝ) :
    Tendsto (fun y : ℝ => ∫ x in a..b, poissonKernel y c x) (𝓝[>] 0)
      (𝓝 ((Real.sign (b - c) - Real.sign (a - c)) * (Real.pi / 2))) := by
  rw [sub_mul]
  refine ((tendsto_arctan_const_div (b - c)).sub
    (tendsto_arctan_const_div (a - c))).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with y hy
  exact (intervalIntegral_poissonKernel c a b (Set.mem_Ioi.mp hy).ne').symm

/-- The Poisson kernel limit passes through a finite weighted sum. -/
theorem tendsto_intervalIntegral_sum_poissonKernel
    {ι : Type*} [Fintype ι] (c w : ι → ℝ) (a b : ℝ) :
    Tendsto (fun y : ℝ => ∫ x in a..b, ∑ j, w j * poissonKernel y (c j) x)
      (𝓝[>] 0) (𝓝 (∑ j, w j *
        ((Real.sign (b - c j) - Real.sign (a - c j)) * (Real.pi / 2)))) := by
  have hlim := tendsto_finset_sum Finset.univ (fun j _ =>
    (tendsto_intervalIntegral_poissonKernel (c j) a b).const_mul (w j))
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with y hy
  have hy' := (Set.mem_Ioi.mp hy).ne'
  symm
  rw [intervalIntegral.integral_finset_sum]
  · simp only [intervalIntegral.integral_const_mul]
  · intro j _
    exact ((continuous_poissonKernel hy' (c j)).const_mul _).intervalIntegrable _ _

/-- Every center strictly inside the integration interval contributes full
mass in the limit. The estimate applies to any smaller interval, including
its endpoints when they are interior to the integration interval. -/
theorem exists_tendsto_intervalIntegral_sum_poissonKernel
    {ι : Type*} [Fintype ι] (c w : ι → ℝ) (hw : ∀ j, 0 ≤ w j)
    {a b : ℝ} (hab : a ≤ b) {s : Set ℝ} (hs : s ⊆ Set.Ioo a b) :
    ∃ L : ℝ,
      Tendsto (fun y : ℝ => ∫ x in a..b, ∑ j, w j * poissonKernel y (c j) x)
        (𝓝[>] 0) (𝓝 L) ∧
      Real.pi * (∑ j, s.indicator (fun _ => w j) (c j)) ≤ L := by
  classical
  let mass (j : ι) := (Real.sign (b - c j) - Real.sign (a - c j)) * (Real.pi / 2)
  have hmass (j : ι) :
      Tendsto (fun y : ℝ => ∫ x in a..b, poissonKernel y (c j) x)
        (𝓝[>] 0) (𝓝 (mass j)) :=
    tendsto_intervalIntegral_poissonKernel (c j) a b
  refine ⟨∑ j, w j * mass j, tendsto_intervalIntegral_sum_poissonKernel c w a b, ?_⟩
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _
  by_cases hj : c j ∈ s
  · obtain ⟨haj, hjb⟩ := hs hj
    simp only [Set.indicator_of_mem hj, mass, Real.sign_of_pos (sub_pos.mpr hjb),
      Real.sign_of_neg (sub_neg.mpr haj)]
    apply le_of_eq
    ring
  · rw [Set.indicator_of_notMem hj, mul_zero]
    apply mul_nonneg (hw j)
    apply ge_of_tendsto (hmass j)
    filter_upwards [self_mem_nhdsWithin] with y hy
    exact intervalIntegral.integral_nonneg_of_forall hab
      (poissonKernel_nonneg (Set.mem_Ioi.mp hy).le (c j))

end NumStability
