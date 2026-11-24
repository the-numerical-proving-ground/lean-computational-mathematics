import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Probability.Independence.Basic

/-! The uniform distribution on a real symmetric interval and independent copies of it. -/

namespace NumStability

open MeasureTheory
open scoped ENNReal

/-- Normalized Lebesgue measure on the closed interval from `-δ` to `δ`. -/
noncomputable def symmetricUniform (δ : ℝ) : Measure ℝ :=
  ProbabilityTheory.cond volume (Set.Icc (-δ) δ)

/-- A Lebesgue density of the uniform distribution on the symmetric interval. -/
noncomputable def symmetricUniformDensity (δ : ℝ) : ℝ → ℝ≥0∞ :=
  (Set.Icc (-δ) δ).indicator fun _ => ENNReal.ofReal (1 / (2 * δ))

theorem measurable_symmetricUniformDensity (δ : ℝ) : Measurable (symmetricUniformDensity δ) :=
  measurable_const.indicator measurableSet_Icc

theorem symmetricUniformDensity_le (δ : ℝ) (x : ℝ) :
    symmetricUniformDensity δ x ≤ ENNReal.ofReal (1 / (2 * δ)) := by
  classical
  by_cases h : x ∈ Set.Icc (-δ) δ <;> simp [symmetricUniformDensity, h]

theorem symmetricUniform_eq_withDensity {δ : ℝ} (hδ : 0 < δ) :
    symmetricUniform δ = (volume : Measure ℝ).withDensity (symmetricUniformDensity δ) := by
  rw [symmetricUniformDensity, withDensity_indicator measurableSet_Icc, withDensity_const]
  rw [symmetricUniform, ProbabilityTheory.cond, Real.volume_Icc,
    show δ - -δ = 2 * δ by ring, ENNReal.ofReal_div_of_pos (by positivity)]
  simp

theorem isProbabilityMeasure_symmetricUniform {δ : ℝ} (hδ : 0 < δ) :
    IsProbabilityMeasure (symmetricUniform δ) := by
  apply ProbabilityTheory.cond_isProbabilityMeasure_of_finite
  · rw [Real.volume_Icc]
    exact (ENNReal.ofReal_pos.mpr (by linarith)).ne'
  · rw [Real.volume_Icc]
    exact ENNReal.ofReal_ne_top

/-- The joint law of independent coordinates, each uniform on `[-δ, δ]`. -/
noncomputable def symmetricUniformProduct (n : ℕ) (δ : ℝ) : Measure (Fin n → ℝ) :=
  Measure.pi fun _ => symmetricUniform δ

theorem isProbabilityMeasure_symmetricUniformProduct (n : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    IsProbabilityMeasure (symmetricUniformProduct n δ) := by
  unfold symmetricUniformProduct
  letI (i : Fin n) : IsProbabilityMeasure ((fun _ : Fin n => symmetricUniform δ) i) :=
    isProbabilityMeasure_symmetricUniform hδ
  infer_instance

theorem measurePreserving_eval_symmetricUniformProduct {n : ℕ} {δ : ℝ} (hδ : 0 < δ)
    (i : Fin n) :
    MeasurePreserving (fun v : Fin n → ℝ => v i)
      (symmetricUniformProduct n δ) (symmetricUniform δ) := by
  let hprob : ∀ _ : Fin n, IsProbabilityMeasure (symmetricUniform δ) :=
    fun _ => isProbabilityMeasure_symmetricUniform hδ
  exact @measurePreserving_eval (Fin n) (fun _ => ℝ) _ _ (fun _ => symmetricUniform δ) hprob i

theorem iIndepFun_symmetricUniformProduct {n : ℕ} {δ : ℝ} (hδ : 0 < δ) :
    ProbabilityTheory.iIndepFun (fun (i : Fin n) (v : Fin n → ℝ) => v i)
      (symmetricUniformProduct n δ) := by
  let hprob : ∀ _ : Fin n, IsProbabilityMeasure (symmetricUniform δ) :=
    fun _ => isProbabilityMeasure_symmetricUniform hδ
  exact @ProbabilityTheory.iIndepFun_pi (Fin n) _ (fun _ => ℝ) _ _ hprob
    (fun _ => ℝ) _ (fun _ => id) (fun _ => aemeasurable_id)

/-- Any family of independent random variables with these marginals has this joint law. -/
theorem map_eq_symmetricUniformProduct {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {n : ℕ} {δ : ℝ} {V : Fin n → Ω → ℝ}
    (hV : ∀ i, AEMeasurable (V i) μ) (hindep : ProbabilityTheory.iIndepFun V μ)
    (hlaw : ∀ i, μ.map (V i) = symmetricUniform δ) :
    μ.map (fun ω i => V i ω) = symmetricUniformProduct n δ := by
  rw [(ProbabilityTheory.iIndepFun_iff_map_fun_eq_pi_map hV).1 hindep, symmetricUniformProduct]
  simp_rw [hlaw]

end NumStability
