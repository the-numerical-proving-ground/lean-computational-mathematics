import ComputationalMathematics.Source.CertifiedTridiagonalEigenpairs.FiniteSampler
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.MeasureTheory.Measure.Prod

/-!
# Continuous coupling for the finite diagonal sampler

The probability proof of `rand:trial` adds independent uniform offsets to
the sampled cell centers. The offsets are used only in the analysis.
-/

namespace NumStability.CertifiedTridiagonalEigenpairs

open MeasureTheory Set
open scoped ENNReal

noncomputable section

/-- The half-open version of the cell centered at the given draw. -/
def samplingCell (δ : ℝ) (b : ℕ) (r : Fin (2 ^ b)) : Set ℝ :=
  Ico (cellCenter δ b r - cellRadius δ b) (cellCenter δ b r + cellRadius δ b)

/-- The closed cell is the support of the perturbation conditional on its draw. -/
def closedSamplingCell (δ : ℝ) (b : ℕ) (r : Fin (2 ^ b)) : Set ℝ :=
  Icc (cellCenter δ b r - cellRadius δ b) (cellCenter δ b r + cellRadius δ b)

private theorem cellRadius_mul_grid (δ : ℝ) (b : ℕ) :
    cellRadius δ b * 2 ^ b = δ :=
  div_mul_cancel₀ δ (by positivity)

private theorem cellEndpoints (δ : ℝ) (b : ℕ) (r : Fin (2 ^ b)) :
    cellCenter δ b r - cellRadius δ b = 2 * cellRadius δ b * (r.val : ℝ) - δ ∧
    cellCenter δ b r + cellRadius δ b = 2 * cellRadius δ b * ((r.val : ℝ) + 1) - δ := by
  have h := cellRadius_mul_grid δ b
  rw [cellCenter_as_radius]
  constructor <;> linarith only [h, mul_comm ((2 : ℝ) ^ b) (cellRadius δ b)]

theorem samplingCell_disjoint {δ : ℝ} (hδ : 0 < δ) (b : ℕ) :
    Pairwise (fun r s => Disjoint (samplingCell δ b r) (samplingCell δ b s)) := by
  have hρ : 0 ≤ 2 * cellRadius δ b := by unfold cellRadius; positivity
  have ordered {r s : Fin (2 ^ b)} (hrs : r < s) :
      Disjoint (samplingCell δ b r) (samplingCell δ b s) := by
    rw [samplingCell, samplingCell, (cellEndpoints δ b r).2, (cellEndpoints δ b s).1]
    apply Set.disjoint_left.2
    intro x hx hy
    have hrs' : (r.val : ℝ) + 1 ≤ s.val := by exact_mod_cast hrs
    have hle := mul_le_mul_of_nonneg_left hrs' hρ
    exact (not_le_of_gt hx.2) ((sub_le_sub_right hle δ).trans hy.1)
  intro r s hrs
  rcases lt_or_gt_of_ne hrs with h | h
  · exact ordered h
  · exact (ordered h).symm

theorem iUnion_samplingCell {δ : ℝ} (hδ : 0 < δ) (b : ℕ) :
    (⋃ r : Fin (2 ^ b), samplingCell δ b r) = Ico (-δ) δ := by
  let w := 2 * cellRadius δ b
  have hw : 0 < w := by dsimp [w, cellRadius]; positivity
  have hwN : w * (2 : ℝ) ^ b = 2 * δ := by
    change 2 * cellRadius δ b * (2 : ℝ) ^ b = 2 * δ
    rw [mul_assoc, cellRadius_mul_grid]
  ext x
  simp only [Set.mem_iUnion, samplingCell, Set.mem_Ico]
  constructor
  · rintro ⟨r, hlo, hhi⟩
    rw [(cellEndpoints δ b r).1] at hlo
    rw [(cellEndpoints δ b r).2] at hhi
    have hlo' : 0 ≤ w * (r.val : ℝ) := by positivity
    have hr : (r.val : ℝ) + 1 ≤ (2 : ℝ) ^ b := by exact_mod_cast r.isLt
    have hhi' := mul_le_mul_of_nonneg_left hr hw.le
    exact ⟨by linarith, by linarith⟩
  · rintro ⟨hlo, hhi⟩
    let y := (x + δ) / w
    have hy : 0 ≤ y := div_nonneg (by linarith) hw.le
    have hyN : y < ((2 ^ b : ℕ) : ℝ) := by
      apply (div_lt_iff₀ hw).2
      push_cast
      rw [mul_comm, hwN]
      linarith
    let r : Fin (2 ^ b) := ⟨⌊y⌋₊, (Nat.floor_lt hy).2 hyN⟩
    refine ⟨r, ?_, ?_⟩
    · rw [(cellEndpoints δ b r).1]
      have h := (le_div_iff₀ hw).1 (Nat.floor_le hy)
      change (r.val : ℝ) * w ≤ x + δ at h
      linarith only [h, mul_comm w (r.val : ℝ)]
    · rw [(cellEndpoints δ b r).2]
      have h := (div_lt_iff₀ hw).1 (Nat.lt_floor_add_one y)
      change x + δ < ((r.val : ℝ) + 1) * w at h
      linarith only [h, mul_comm w ((r.val : ℝ) + 1)]

/-- The closed cells cover the entire perturbation interval, including the
right endpoint of the last cell. -/
theorem iUnion_closedSamplingCell {δ : ℝ} (hδ : 0 < δ) (b : ℕ) :
    (⋃ r : Fin (2 ^ b), closedSamplingCell δ b r) = Icc (-δ) δ := by
  have hρ : 0 ≤ 2 * cellRadius δ b := by unfold cellRadius; positivity
  have hwN : 2 * cellRadius δ b * (2 : ℝ) ^ b = 2 * δ := by
    rw [mul_assoc, cellRadius_mul_grid]
  ext x
  simp only [Set.mem_iUnion, closedSamplingCell, Set.mem_Icc]
  constructor
  · rintro ⟨r, hlo, hhi⟩
    rw [(cellEndpoints δ b r).1] at hlo
    rw [(cellEndpoints δ b r).2] at hhi
    have hlo' : 0 ≤ 2 * cellRadius δ b * (r.val : ℝ) := by positivity
    have hr : (r.val : ℝ) + 1 ≤ (2 : ℝ) ^ b := by exact_mod_cast r.isLt
    have hhi' := mul_le_mul_of_nonneg_left hr hρ
    exact ⟨by linarith, by linarith⟩
  · rintro ⟨hlo, hhi⟩
    rcases hhi.lt_or_eq with hlt | heq
    · have hx : x ∈ ⋃ r : Fin (2 ^ b), samplingCell δ b r := by
        rw [iUnion_samplingCell hδ]
        exact ⟨hlo, hlt⟩
      obtain ⟨r, hr⟩ := Set.mem_iUnion.1 hx
      exact ⟨r, hr.1, hr.2.le⟩
    · subst x
      have hN : 0 < (2 : ℕ) ^ b := by positivity
      let r : Fin (2 ^ b) := ⟨2 ^ b - 1, Nat.sub_lt hN (by decide)⟩
      have hr : (r.val : ℝ) + 1 = (2 : ℝ) ^ b := by
        exact_mod_cast Nat.sub_add_cancel hN
      have h : cellCenter δ b r + cellRadius δ b = δ := by
        rw [(cellEndpoints δ b r).2, hr, hwN]
        ring
      exact ⟨r, by linarith [show 0 ≤ cellRadius δ b by unfold cellRadius; positivity], h.ge⟩

/-- Pointwise coupling bound for any draw and any point in its closed cell. -/
theorem abs_sub_cellCenter_le {δ : ℝ} {b : ℕ} {r : Fin (2 ^ b)} {x : ℝ}
    (hx : x ∈ closedSamplingCell δ b r) : |x - cellCenter δ b r| ≤ cellRadius δ b := by
  exact abs_le.2 ⟨by linarith only [hx.1], by linarith only [hx.2]⟩

/-- The uniform law on the finite grid, as a measure. -/
def gridUniform (b : ℕ) : Measure (Fin (2 ^ b)) :=
  (((2 : ℝ≥0∞) ^ b)⁻¹) • Measure.count

/-- The independent continuous offset in the analysis. -/
def offsetUniform (δ : ℝ) (b : ℕ) : Measure ℝ :=
  ProbabilityTheory.cond volume (Icc (-cellRadius δ b) (cellRadius δ b))

/-- The coordinate coupling draws the grid index and offset independently. -/
def coordinateCoupling (δ : ℝ) (b : ℕ) : Measure (Fin (2 ^ b) × ℝ) :=
  (gridUniform b).prod (offsetUniform δ b)

/-- The coupled continuous coordinate obtained by shifting the center. -/
def coupledCoordinate (δ : ℝ) (b : ℕ) (pair : Fin (2 ^ b) × ℝ) : ℝ :=
  cellCenter δ b pair.1 + pair.2

theorem measurable_coupledCoordinate (δ : ℝ) (b : ℕ) :
    Measurable (coupledCoordinate δ b) := by
  have hc : Measurable (cellCenter δ b) := Measurable.of_discrete
  exact (hc.comp measurable_fst).add measurable_snd

private theorem offsetMass (δ : ℝ) (b : ℕ) :
    volume (Icc (-cellRadius δ b) (cellRadius δ b)) =
      ENNReal.ofReal (2 * cellRadius δ b) := by
  rw [Real.volume_Icc]
  congr 1
  ring

private theorem intervalMass (δ : ℝ) :
    volume (Icc (-δ) δ) = ENNReal.ofReal (2 * δ) := by
  rw [Real.volume_Icc]
  congr 1
  ring

private theorem massMul (δ : ℝ) (b : ℕ) :
    (2 : ℝ≥0∞) ^ b * ENNReal.ofReal (2 * cellRadius δ b) =
      ENNReal.ofReal (2 * δ) := by
  have h : (2 : ℝ) ^ b * (2 * cellRadius δ b) = 2 * δ := by
    calc
      _ = 2 * (cellRadius δ b * 2 ^ b) := by ring
      _ = _ := by rw [cellRadius_mul_grid]
  rw [← h, ENNReal.ofReal_mul (by positivity : 0 ≤ (2 : ℝ) ^ b)]
  congr 1
  have hc := ENNReal.ofReal_natCast ((2 : ℕ) ^ b)
  push_cast at hc
  exact hc.symm

private theorem map_offsetVolume (δ : ℝ) (b : ℕ) (r : Fin (2 ^ b)) :
    Measure.map (fun x => cellCenter δ b r + x)
      (volume.restrict (Icc (-cellRadius δ b) (cellRadius δ b))) =
        volume.restrict (samplingCell δ b r) := by
  have hpre :
      (fun x => cellCenter δ b r + x) ⁻¹' samplingCell δ b r =
        Ico (-cellRadius δ b) (cellRadius δ b) := by
    ext x
    simp only [Set.mem_preimage, samplingCell, Set.mem_Ico]
    constructor <;> rintro ⟨h₁, h₂⟩ <;> exact ⟨by linarith, by linarith⟩
  have hf : Measurable (fun x => cellCenter δ b r + x) := measurable_const.add measurable_id
  have hs : MeasurableSet (samplingCell δ b r) := measurableSet_Ico
  rw [← restrict_Ico_eq_restrict_Icc, ← hpre, ← Measure.restrict_map hf hs,
    map_add_left_eq_self]

theorem offsetUniform_probability {δ : ℝ} (hδ : 0 < δ) (b : ℕ) :
    IsProbabilityMeasure (offsetUniform δ b) := by
  apply ProbabilityTheory.cond_isProbabilityMeasure_of_finite
  · rw [offsetMass]
    apply ENNReal.ofReal_ne_zero_iff.2
    unfold cellRadius
    positivity
  · rw [offsetMass]
    exact ENNReal.ofReal_ne_top

private theorem map_offsetUniform_apply (δ : ℝ) (b : ℕ) (r : Fin (2 ^ b))
    {A : Set ℝ} (hA : MeasurableSet A) :
    offsetUniform δ b ((fun x => cellCenter δ b r + x) ⁻¹' A) =
      (ENNReal.ofReal (2 * cellRadius δ b))⁻¹ * volume.restrict (samplingCell δ b r) A := by
  have hf : Measurable (fun x => cellCenter δ b r + x) := measurable_const.add measurable_id
  rw [← Measure.map_apply hf hA, offsetUniform, ProbabilityTheory.cond, Measure.map_smul, map_offsetVolume,
    Measure.smul_apply, smul_eq_mul, offsetMass]

/-- Adding a uniform offset to an independent uniform grid index gives the
uniform law on the entire perturbation interval. -/
theorem coupledCoordinate_uniform {δ : ℝ} (hδ : 0 < δ) (b : ℕ) :
    Measure.map (coupledCoordinate δ b) (coordinateCoupling δ b) =
      ProbabilityTheory.cond volume (Icc (-δ) δ) := by
  letI := offsetUniform_probability hδ b
  ext A hA : 1
  rw [Measure.map_apply (measurable_coupledCoordinate δ b) hA, coordinateCoupling,
    Measure.prod_apply ((measurable_coupledCoordinate δ b) hA), gridUniform,
    lintegral_smul_measure, lintegral_count, smul_eq_mul]
  change ((2 : ℝ≥0∞) ^ b)⁻¹ *
    (∑' r : Fin (2 ^ b), offsetUniform δ b ((fun x => cellCenter δ b r + x) ⁻¹' A)) = _
  simp_rw [map_offsetUniform_apply δ b _ hA]
  rw [ENNReal.tsum_mul_left, ← mul_assoc,
    ← ENNReal.mul_inv (Or.inl (by positivity)) (Or.inl (by finiteness)),
    massMul, ProbabilityTheory.cond, intervalMass, Measure.smul_apply,
    smul_eq_mul, ← restrict_Ico_eq_restrict_Icc, ← iUnion_samplingCell hδ b,
    Measure.restrict_iUnion_apply (samplingCell_disjoint hδ b)
      (fun _ => measurableSet_Ico) hA]

theorem gridUniform_singleton (b : ℕ) (r : Fin (2 ^ b)) :
    gridUniform b {r} = (((2 : ℝ≥0∞) ^ b)⁻¹) := by
  rw [gridUniform, Measure.smul_apply, smul_eq_mul, Measure.count_singleton, mul_one]

instance gridUniform_probability (b : ℕ) : IsProbabilityMeasure (gridUniform b) := by
  refine ⟨?_⟩
  rw [gridUniform, Measure.smul_apply, smul_eq_mul, ← Finset.coe_univ,
    Measure.count_apply_finset, Finset.card_univ, Fintype.card_fin, Nat.cast_pow, Nat.cast_ofNat]
  exact ENNReal.inv_mul_cancel (by positivity) (by finiteness)

theorem coordinateCoupling_probability {δ : ℝ} (hδ : 0 < δ) (b : ℕ) :
    IsProbabilityMeasure (coordinateCoupling δ b) := by
  letI := offsetUniform_probability hδ b
  unfold coordinateCoupling
  infer_instance

theorem coordinateCoupling_fst {δ : ℝ} (hδ : 0 < δ) (b : ℕ) :
    Measure.map Prod.fst (coordinateCoupling δ b) = gridUniform b := by
  letI := offsetUniform_probability hδ b
  exact (measurePreserving_fst (μ := gridUniform b) (ν := offsetUniform δ b)).map_eq

theorem coordinateCoupling_snd {δ : ℝ} (hδ : 0 < δ) (b : ℕ) :
    Measure.map Prod.snd (coordinateCoupling δ b) = offsetUniform δ b := by
  letI := offsetUniform_probability hδ b
  exact (measurePreserving_snd (μ := gridUniform b) (ν := offsetUniform δ b)).map_eq

private theorem coordinateCoupling_offset_ae {δ : ℝ} (hδ : 0 < δ) (b : ℕ) :
    ∀ᵐ z ∂coordinateCoupling δ b, z.2 ∈ Icc (-cellRadius δ b) (cellRadius δ b) := by
  letI := offsetUniform_probability hδ b
  apply (measurePreserving_snd (μ := gridUniform b)
    (ν := offsetUniform δ b)).quasiMeasurePreserving.ae
  unfold offsetUniform ProbabilityTheory.cond
  exact (Measure.absolutelyContinuous_of_le_smul le_rfl).ae_le
    (ae_restrict_mem measurableSet_Icc)

private theorem realUniform_probability {δ : ℝ} (hδ : 0 < δ) :
    IsProbabilityMeasure (ProbabilityTheory.cond volume (Icc (-δ) δ)) := by
  apply ProbabilityTheory.cond_isProbabilityMeasure_of_finite
  · rw [intervalMass]
    exact ENNReal.ofReal_ne_zero_iff.2 (by positivity)
  · rw [intervalMass]
    exact ENNReal.ofReal_ne_top

/-- The enlarged probability space uses an independent draw-offset pair at
each matrix coordinate. -/
def vectorCoupling (n : ℕ) (δ : ℝ) (b : ℕ) :
    Measure (Fin n → Fin (2 ^ b) × ℝ) :=
  Measure.pi fun _ => coordinateCoupling δ b

theorem vectorCoupling_probability (n : ℕ) {δ : ℝ} (hδ : 0 < δ) (b : ℕ) :
    IsProbabilityMeasure (vectorCoupling n δ b) := by
  letI : ∀ _ : Fin n, IsProbabilityMeasure (coordinateCoupling δ b) :=
    fun _ => coordinateCoupling_probability hδ b
  unfold vectorCoupling
  infer_instance

/-- The finite marginal of the enlarged experiment is exactly the law of
the decoded fair bits. -/
theorem vectorCoupling_draws (n k : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    (vectorCoupling n δ (rngBits n k)).map (fun batch i => (batch i).1) =
      ((trialBitLaw n k).map (trialDraws n k)).toMeasure := by
  let b := rngBits n k
  have hfst : Measure.map Prod.fst (coordinateCoupling δ b) = gridUniform b :=
    coordinateCoupling_fst hδ b
  have hσ : SigmaFinite (Measure.map Prod.fst (coordinateCoupling δ b)) := by
    rw [hfst]
    infer_instance
  unfold vectorCoupling
  rw [Measure.pi_map_pi (f := fun _ : Fin n => Prod.fst) (hμ := fun _ => hσ)
    (fun _ => measurable_fst.aemeasurable)]
  simp_rw [hfst]
  apply Measure.ext_of_singleton
  intro draw
  rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _), trialDraws_law_apply,
    ← Set.univ_pi_singleton, Measure.pi_pi]
  simp only [gridUniform_singleton, Finset.prod_const, Finset.card_univ, Fintype.card_fin, b]

/-- The continuous perturbation vector has independent uniform coordinates
on the full interval, by a product of the coordinate pushforwards. -/
theorem vectorCoupling_values (n : ℕ) {δ : ℝ} (hδ : 0 < δ) (b : ℕ) :
    (vectorCoupling n δ b).map (fun batch i => coupledCoordinate δ b (batch i)) =
      Measure.pi (fun _ : Fin n => ProbabilityTheory.cond volume (Icc (-δ) δ)) := by
  letI := realUniform_probability hδ
  have hmap := coupledCoordinate_uniform hδ b
  have hσ : SigmaFinite (Measure.map (coupledCoordinate δ b) (coordinateCoupling δ b)) := by
    rw [hmap]
    infer_instance
  unfold vectorCoupling
  rw [Measure.pi_map_pi (f := fun _ : Fin n => coupledCoordinate δ b) (hμ := fun _ => hσ)
    (fun _ => (measurable_coupledCoordinate δ b).aemeasurable)]
  simp_rw [hmap]

theorem vectorCoupling_close (n : ℕ) {δ : ℝ} (hδ : 0 < δ) (b : ℕ) :
    ∀ᵐ batch ∂vectorCoupling n δ b, ∀ i,
      |coupledCoordinate δ b (batch i) - cellCenter δ b (batch i).1| ≤ cellRadius δ b := by
  letI : IsProbabilityMeasure (coordinateCoupling δ b) := coordinateCoupling_probability hδ b
  rw [ae_all_iff]
  intro i
  have hp : ∀ _ : Fin n, IsProbabilityMeasure (coordinateCoupling δ b) := fun _ => inferInstance
  have heval := @measurePreserving_eval (Fin n) (fun _ => Fin (2 ^ b) × ℝ) _ _
    (fun _ => coordinateCoupling δ b) hp i
  have hoffset := heval.quasiMeasurePreserving.ae (coordinateCoupling_offset_ae hδ b)
  filter_upwards [hoffset] with batch hb
  rw [coupledCoordinate, add_sub_cancel_left]
  exact abs_le.2 hb

/-- Recover the actual finite input bit words on the enlarged space. -/
def couplingWords (n k : ℕ) (batch : Fin n → Fin (2 ^ rngBits n k) × ℝ) :
    Fin n → FairBitWord (rngBits n k) :=
  (trialDraws n k).symm (fun i => (batch i).1)

theorem vectorCoupling_words (n k : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    (vectorCoupling n δ (rngBits n k)).map (couplingWords n k) = (trialBitLaw n k).toMeasure := by
  let decode := trialDraws n k
  have hfst : Measurable (fun (batch : Fin n → Fin (2 ^ rngBits n k) × ℝ) i =>
      (batch i).1) := measurable_pi_lambda _ (fun i => measurable_fst.comp (measurable_pi_apply i))
  have hdecode : Measurable decode := Measurable.of_discrete
  have hencode : Measurable decode.symm := Measurable.of_discrete
  unfold couplingWords
  change Measure.map (decode.symm ∘ _) _ = _
  rw [← Measure.map_map hencode hfst, vectorCoupling_draws n k hδ,
    ← PMF.toMeasure_map decode _ hdecode, Measure.map_map hencode hdecode]
  have hinv : decode.symm ∘ decode = id := funext decode.symm_apply_apply
  rw [hinv, Measure.map_id]

/-- The coupled diagonal differs from the actual draw by at most `g / 64`
simultaneously at every coordinate. -/
theorem vectorCoupling_trial_close (n k p : ℕ) :
    ∀ᵐ batch ∂vectorCoupling n (perturbationScale p) (rngBits n k), ∀ i,
      |coupledCoordinate (perturbationScale p) (rngBits n k) (batch i) -
        cellCenter (perturbationScale p) (rngBits n k)
          (trialDraws n k (couplingWords n k batch) i)| ≤ gapLabelError n k p := by
  have hδ : 0 < perturbationScale p :=
    div_pos (FloatingPointFormat.UnboundedBinary.unitRoundoff_pos p) (by norm_num)
  simpa only [couplingWords, Equiv.apply_symm_apply, trialCellRadius_eq] using
    vectorCoupling_close n hδ (rngBits n k)

/-- The uniform perturbation density used by spectral averaging. -/
def perturbationDensity (δ : ℝ) : ℝ → ℝ≥0∞ :=
  (Icc (-δ) δ).indicator fun _ => ENNReal.ofReal (2 * δ)⁻¹

theorem measurable_perturbationDensity (δ : ℝ) : Measurable (perturbationDensity δ) :=
  measurable_const.indicator measurableSet_Icc

theorem perturbationDensity_le (δ x : ℝ) :
    perturbationDensity δ x ≤ ENNReal.ofReal (2 * δ)⁻¹ := by
  unfold perturbationDensity
  by_cases hx : x ∈ Icc (-δ) δ <;> simp [hx]

theorem perturbationLaw_withDensity {δ : ℝ} (hδ : 0 < δ) :
    ProbabilityTheory.cond volume (Icc (-δ) δ) = volume.withDensity (perturbationDensity δ) := by
  rw [perturbationDensity, withDensity_indicator measurableSet_Icc, withDensity_const,
    ProbabilityTheory.cond, intervalMass, ENNReal.ofReal_inv_of_pos (by positivity)]

end

end NumStability.CertifiedTridiagonalEigenpairs
