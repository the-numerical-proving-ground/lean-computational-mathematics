import ComputationalMathematics.Source.CertifiedTridiagonalEigenpairs.Section06.InversePath.CompleteTarget
import ComputationalMathematics.Source.CertifiedTridiagonalEigenpairs.Section06.InversePath.Proof

namespace NumStability.CertifiedTridiagonalEigenpairs

open FloatingPointFormat.UnboundedBinary

theorem vectorInverseRecurrenceComplete : SourceTargets.vectorInverseRecurrenceComplete := by
  constructor
  · intro q hq n a b η r
    obtain ⟨hroot, hscore, hstep, hzero⟩ := vectorInverseRecurrence q hq n a b η r
    refine ⟨hroot, hscore, ?_, ?_, hzero, ?_⟩
    · intro i j hij hir
      obtain ⟨hne, hparent⟩ := (vectorParent_eq_iff r j i).2 (Or.inl ⟨hij, hir⟩)
      simpa [roundedInverseStep, vectorOutwardEdge, hir, show i < r from hir, hparent,
        roundedEdgeQuotient, roundedComplexProduct, vectorSquaredModulus] using hstep i hne
    · intro i j hij hrj
      obtain ⟨hne, hparent⟩ := (vectorParent_eq_iff r i j).2 (Or.inr ⟨hij, hrj⟩)
      have hnlt : ¬ j < r := by omega
      have hi : j.val - 1 = i.val := by omega
      simpa [roundedInverseStep, vectorOutwardEdge, hnlt,
        show ¬ j.val < r.val from hnlt, hparent, hi, roundedEdgeQuotient,
        roundedComplexProduct, vectorSquaredModulus] using hstep j hne
    · intro hη hpivots hγ
      refine ⟨vectorSquaredModulus_pos q hq _ _ (hη.trans_le hγ), ?_⟩
      intro i _
      by_cases hi : i < r
      · simpa [vectorOutwardEdge, hi, show i.val < r.val from hi] using
          vectorSquaredModulus_pos q hq _ _ (hη.trans_le (hpivots i).1)
      · simpa [vectorOutwardEdge, hi, show ¬ i.val < r.val from hi] using
          vectorSquaredModulus_pos q hq _ _ (hη.trans_le (hpivots i).2)
  · intro q hq n hn A shift η i
    change ((vectorComputedImaginaryArray hq hn A shift η)[i.val]).value = _
    rw [vectorComputedImaginaryArray, Vector.getElem_ofFn]
    simp only [vectorImaginaryWords_value, vectorCachedExecution_column_get, vectorCachedExecution_root]

private theorem roundedModulus_component_factors (q : ℕ) (hq : 2 ≤ q)
    (hω : unitRoundoff q ≤ 1 / 128) (x y t : ℝ) (hy : 0 < y) :
    let ω := unitRoundoff q
    let R := roundToEven q hq
    let s := vectorSquaredModulus q hq x y
    let S := x ^ 2 + y ^ 2
    (∃ c : ℝ, (1 - ω) / (1 + ω) ^ 2 ≤ c ∧ c ≤ (1 + ω) / (1 - ω) ^ 2 ∧
      R (t / s) = c * (t / S)) ∧
    (∃ c : ℝ, (1 - ω) ^ 2 / (1 + ω) ^ 2 ≤ c ∧ c ≤ (1 + ω) ^ 2 / (1 - ω) ^ 2 ∧
      R (R t / s) = c * (t / S)) := by
  let ω := unitRoundoff q
  let R := roundToEven q hq
  let s := vectorSquaredModulus q hq x y
  let S := x ^ 2 + y ^ 2
  let d := s / S
  have hω₀ : 0 < ω := unitRoundoff_pos q
  have hlow : 0 < 1 - ω := by linarith
  have hs : 0 < s := vectorSquaredModulus_pos q hq x y hy
  have hS : 0 < S := by dsimp [S]; positivity
  have hd : 0 < d := div_pos hs hS
  obtain ⟨hdl, hdu⟩ := vectorSquaredModulus_bounds q hq x y
  have hdlo : (1 - ω) ^ 2 ≤ d := (le_div_iff₀ hS).mpr hdl
  have hdhi : d ≤ (1 + ω) ^ 2 := (div_le_iff₀ hS).mpr hdu
  have round_factor (z : ℝ) : ∃ f : ℝ, 1 - ω ≤ f ∧ f ≤ 1 + ω ∧ R z = z * f := by
    obtain ⟨δ, hδ, hround⟩ := roundToEven_signedRelErrorWitness q hq z
    exact ⟨1 + δ, by linarith [(abs_le.mp hδ).1], by linarith [(abs_le.mp hδ).2], hround⟩
  have ratio {f lo hi : ℝ} (hl : 0 ≤ lo) (hlo : lo ≤ f) (hhi : f ≤ hi) :
      lo / (1 + ω) ^ 2 ≤ f / d ∧ f / d ≤ hi / (1 - ω) ^ 2 := by
    have hhi₀ : 0 ≤ hi := hl.trans (hlo.trans hhi)
    constructor
    · calc
        _ ≤ lo / d := div_le_div_of_nonneg_left hl hd hdhi
        _ ≤ _ := div_le_div_of_nonneg_right hlo hd.le
    · calc
        _ ≤ hi / d := div_le_div_of_nonneg_right hhi hd.le
        _ ≤ _ := div_le_div_of_nonneg_left hhi₀ (by positivity) hdlo
  obtain ⟨a, hal, hau, ha⟩ := round_factor (t / s)
  obtain ⟨b, hbl, hbu, hb⟩ := round_factor t
  obtain ⟨c, hcl, hcu, hc⟩ := round_factor (R t / s)
  obtain ⟨haratio, haratio'⟩ := ratio hlow.le hal hau
  have hbc₀ : (1 - ω) ^ 2 ≤ b * c := by
    rw [pow_two]
    exact mul_le_mul hbl hcl hlow.le (hlow.le.trans hbl)
  have hbc₁ : b * c ≤ (1 + ω) ^ 2 := by
    rw [pow_two]
    exact mul_le_mul hbu hcu (hlow.le.trans hcl) (by positivity)
  obtain ⟨hbcratio, hbcratio'⟩ := ratio (sq_nonneg _) hbc₀ hbc₁
  change (∃ _, _ ∧ _ ∧ R (t / s) = _) ∧ (∃ _, _ ∧ _ ∧ R (R t / s) = _)
  refine ⟨⟨a / d, haratio, haratio', ?_⟩, ⟨b * c / d, hbcratio, hbcratio', ?_⟩⟩
  · rw [ha]
    dsimp [d]
    field_simp [hs.ne', hS.ne']
    rfl
  · rw [hc, hb]
    dsimp [d]
    field_simp [hs.ne', hS.ne']
    rfl

private theorem substitutedEdge_ratio {ω : ℝ} (hω₀ : 0 ≤ ω) (hω : ω ≤ 1 / 128)
    (b : ℝ) (β : ℂ) (hb : b ≠ 0) (hrel : ‖β / (b : ℂ) - 1‖ ≤ 11 * ω) :
    β ≠ 0 ∧ ‖(b : ℂ) / β - 1‖ ≤ 11 * ω / (1 - 11 * ω) ∧
      11 * ω / (1 - 11 * ω) ≤ 13 * ω := by
  have hd : 0 < 1 - 11 * ω := by linarith
  have hc : (b : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hb
  have hnorm : 0 < ‖(b : ℂ)‖ := norm_pos_iff.mpr hc
  have herr : ‖β - (b : ℂ)‖ ≤ (11 * ω) * ‖(b : ℂ)‖ := by
    rw [← div_self hc, ← sub_div, norm_div] at hrel
    exact (div_le_iff₀ hnorm).mp hrel
  have hlower : (1 - 11 * ω) * ‖(b : ℂ)‖ ≤ ‖β‖ := by
    have h := norm_le_norm_add_norm_sub β (b : ℂ)
    linarith
  have hnβ := (mul_pos hd hnorm).trans_le hlower
  have hβ := norm_pos_iff.mp hnβ
  refine ⟨hβ, ?_, ?_⟩
  · rw [← div_self hβ, ← sub_div, norm_div, norm_sub_rev]
    apply (div_le_iff₀ hnβ).mpr
    refine herr.trans ?_
    have hnonneg : 0 ≤ 11 * ω / (1 - 11 * ω) := by positivity
    have h := mul_le_mul_of_nonneg_left hlower hnonneg
    convert h using 1
    field_simp
  · apply (div_le_iff₀ hd).mpr
    nlinarith [mul_nonneg hω₀ (sub_nonneg.mpr hω)]

private theorem roundedPropagation_error (q : ℕ) (hq : 2 ≤ q)
    (hω : unitRoundoff q ≤ 1 / 128) (edge : InversePathEdge) (v : ℂ)
    (hy : 0 < edge.pivotNegIm) :
    let ω := unitRoundoff q
    let p := -((edge.original : ℂ) / edge.pivot) * v
    ‖roundedInverseStep q hq edge v - p‖ ≤ (6 * ω + 3 * ω * (1 + 6 * ω)) * ‖p‖ ∧
    6 * ω + 3 * ω * (1 + 6 * ω) ≤ 10 * ω := by
  let ω := unitRoundoff q
  change _ ∧ 6 * ω + 3 * ω * (1 + 6 * ω) ≤ 10 * ω
  have hω₀ : 0 ≤ ω := (unitRoundoff_pos q).le
  refine ⟨?_, by nlinarith [mul_nonneg hω₀ (sub_nonneg.mpr hω)]⟩
  by_cases hz : edge.original = 0
  · simp [roundedInverseStep, hz]
  let a := -((edge.original : ℂ) / edge.pivot)
  let A := -roundedEdgeQuotient q hq edge.original edge.pivotRe edge.pivotNegIm
  rw [roundedInverseStep, if_neg hz]
  change ‖roundedComplexProduct q hq A v - a * v‖ ≤
    (6 * ω + 3 * ω * (1 + 6 * ω)) * ‖a * v‖
  have hA : ‖A - a‖ ≤ 6 * ω * ‖a‖ := by
    simpa only [A, a, InversePathEdge.pivot, neg_sub_neg, norm_neg, norm_sub_rev]
      using roundedEdgeQuotient_error q hq hω edge.original edge.pivotRe edge.pivotNegIm hy
  have hnorm : ‖A‖ ≤ (1 + 6 * ω) * ‖a‖ := by
    have h := norm_le_norm_add_norm_sub a A
    rw [norm_sub_rev a A] at h
    linarith
  have hmul := roundedComplexProduct_error q hq hω A v
  have hquot : ‖A * v - a * v‖ ≤ (6 * ω * ‖a‖) * ‖v‖ := by
    rw [← sub_mul, norm_mul]
    exact mul_le_mul_of_nonneg_right hA (norm_nonneg _)
  calc
    _ ≤ ‖roundedComplexProduct q hq A v - A * v‖ + ‖A * v - a * v‖ := by
      simpa only [dist_eq_norm] using dist_triangle (roundedComplexProduct q hq A v) (A * v) (a * v)
    _ ≤ 3 * ω * (((1 + 6 * ω) * ‖a‖) * ‖v‖) + (6 * ω * ‖a‖) * ‖v‖ :=
      add_le_add (hmul.trans (by gcongr)) hquot
    _ = _ := by rw [norm_mul]; ring

private theorem exactPath_zero_of_mem (x y : ℝ) (path : List InversePathEdge)
    (edge : InversePathEdge) (hmem : edge ∈ path) (hz : edge.absorbed = 0) :
    exactInversePath x y path = 0 := by
  induction path with
  | nil => simp at hmem
  | cons e path ih =>
    rcases List.mem_cons.mp hmem with rfl | hmem
    · simp [exactInversePath, exactInverseStep, hz]
    · simp [exactInversePath, exactInverseStep, ih hmem]

private theorem roundedPath_product_cap {n : ℕ} (hn : 2 ≤ n) {ω : ℝ} (hω : 0 < ω)
    (hnω : (n : ℝ) * ω ≤ 1 / 128) :
    (1 + 4 * ω) * (1 + 13 * ω) ^ n * (1 + 10 * ω) ^ n - 1 ≤
      Real.exp (25 * (n : ℝ) * ω) - 1 ∧
    Real.exp (25 * (n : ℝ) * ω) - 1 ≤ 64 * (n : ℝ) * ω := by
  have hn₂ : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hsum : 4 * ω + (n : ℝ) * (13 * ω) + (n : ℝ) * (10 * ω) ≤ 25 * (n : ℝ) * ω := by
    nlinarith only [mul_le_mul_of_nonneg_right hn₂ hω.le]
  constructor
  · apply sub_le_sub_right
    calc
      _ ≤ Real.exp (4 * ω) * Real.exp (13 * ω) ^ n * Real.exp (10 * ω) ^ n := by
        have h (a : ℝ) : 1 + a ≤ Real.exp a := by simpa [add_comm] using Real.add_one_le_exp a
        gcongr <;> apply h
      _ = Real.exp (4 * ω + (n : ℝ) * (13 * ω) + (n : ℝ) * (10 * ω)) := by
        rw [Real.exp_add, Real.exp_add, Real.exp_nat_mul, Real.exp_nat_mul]
      _ ≤ _ := Real.exp_le_exp.mpr hsum
  · have hsmall : 25 * (n : ℝ) * ω < 1 / 4 := by linarith
    have hpos : 0 < 25 * (n : ℝ) * ω := by positivity
    have h := real_exp_sub_one_lt_div_one_sub_half_of_pos_of_lt_two hpos
      (show 25 * (n : ℝ) * ω < 2 by linarith)
    refine h.le.trans ((div_le_iff₀ (by linarith)).mpr ?_)
    have hden : (1 / 2 : ℝ) ≤ 1 - (25 * (n : ℝ) * ω) / 2 := by linarith
    calc
      _ ≤ 64 * (n : ℝ) * ω * (1 / 2) := by linarith
      _ ≤ _ := mul_le_mul_of_nonneg_left hden (by positivity)

theorem vectorRoundedPathComplete : SourceTargets.vectorRoundedPathComplete := by
  refine ⟨?_, ?_, vectorRoundedPath⟩
  · intro q hq ω hω
    refine ⟨?_, roundedModulus_component_factors q hq hω,
      substitutedEdge_ratio (unitRoundoff_pos q).le hω,
      fun b x y hy => roundedEdgeQuotient_error q hq hω b x y hy,
      roundedComplexProduct_error q hq hω, roundedPropagation_error q hq hω⟩
    intro x y hy
    have hγ : ‖(⟨x, -y⟩ : ℂ)‖ ^ 2 = x ^ 2 + y ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      ring
    refine ⟨vectorSquaredModulus_pos q hq x y hy, ?_, ?_,
      roundedTwistReciprocal_error q hq hω x y hy⟩
    · simpa only [hγ] using (vectorSquaredModulus_bounds q hq x y).1
    · simpa only [hγ] using (vectorSquaredModulus_bounds q hq x y).2
  · intro q hq n hn ω hnω x y hy path hlen hpivot hedge
    have hω₀ : 0 < ω := unitRoundoff_pos q
    have hn₁ : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
    have hω : ω ≤ 1 / 128 := by
      linarith only [mul_le_mul_of_nonneg_right hn₁ hω₀.le, hnω]
    obtain ⟨hcap, hexp⟩ := roundedPath_product_cap hn hω₀ hnω
    refine ⟨roundedInversePath_factorization q hq hω x y hy path hpivot hedge,
      ?_, hcap, hexp, ?_⟩
    · obtain ⟨ζ, hζ, hrel⟩ := roundedInversePath_factor q hq hω x y hy path hpivot hedge
      have hpow :
          (1 + 4 * ω) * (1 + 13 * ω) ^ path.length * (1 + 10 * ω) ^ path.length ≤
            (1 + 4 * ω) * (1 + 13 * ω) ^ n * (1 + 10 * ω) ^ n := by
        gcongr <;> linarith [hω₀.le]
      rw [hζ, ← mul_sub_one, norm_mul, mul_comm]
      exact mul_le_mul_of_nonneg_right (hrel.trans (sub_le_sub_right hpow 1)) (norm_nonneg _)
    · intro edge he hz
      have hzβ := hedge edge he
      simp only [hz, Complex.ofReal_zero, sub_zero, norm_zero, mul_zero, norm_le_zero_iff] at hzβ
      exact ⟨exactPath_zero_of_mem x y path edge he hzβ,
        roundedInversePath_zero_of_mem q hq x y path edge he hz⟩

end NumStability.CertifiedTridiagonalEigenpairs
