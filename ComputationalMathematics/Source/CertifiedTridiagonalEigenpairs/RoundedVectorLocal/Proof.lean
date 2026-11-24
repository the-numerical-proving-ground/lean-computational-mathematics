import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Tactic
import ComputationalMathematics.Analysis.FloatingPointArithmetic.UnboundedBinary.Basic

namespace NumStability.CertifiedTridiagonalEigenpairs

private theorem complex_norm_mk_le_scale
    {x y c₁ c₂ ε : ℝ} (hε : 0 ≤ ε) (h₁ : |c₁| ≤ ε) (h₂ : |c₂| ≤ ε) :
    ‖(⟨c₁ * x, c₂ * y⟩ : ℂ)‖ ≤ ε * ‖(⟨x, -y⟩ : ℂ)‖ := by
  refine le_of_sq_le_sq ?_ (by positivity)
  rw [mul_pow, ← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq]
  have h₁sq : c₁ ^ 2 ≤ ε ^ 2 := by rwa [sq_le_sq, abs_of_nonneg hε]
  have h₂sq : c₂ ^ 2 ≤ ε ^ 2 := by rwa [sq_le_sq, abs_of_nonneg hε]
  change c₁ * x * (c₁ * x) + c₂ * y * (c₂ * y) ≤ ε ^ 2 * (x * x + -y * -y)
  nlinarith [mul_le_mul_of_nonneg_right h₁sq (sq_nonneg x),
    mul_le_mul_of_nonneg_right h₂sq (sq_nonneg y)]

private theorem exists_complex_sq_eq_norm_sub_one_le {χ : ℂ} (hχ : ‖χ - 1‖ < 1) :
    ∃ z : ℂ, 0 < z.re ∧ z ^ 2 = χ ∧ ‖z - 1‖ ≤ ‖χ - 1‖ := by
  have hre : 0 < χ.re := by
    have h := (Complex.abs_re_le_norm (χ - 1)).trans_lt hχ
    rw [Complex.sub_re, Complex.one_re] at h
    linarith [(abs_lt.mp h).1]
  obtain ⟨w, hw⟩ := IsAlgClosed.exists_pow_nat_eq χ (by decide : 0 < (2 : ℕ))
  have hwne : w.re ≠ 0 := by
    intro hr
    have h := congrArg Complex.re hw
    rw [pow_two, Complex.mul_re, hr, zero_mul, zero_sub] at h
    nlinarith [sq_nonneg w.im]
  have hfinish (z : ℂ) (hz : 0 < z.re) (hzw : z ^ 2 = χ) :
      ∃ z : ℂ, 0 < z.re ∧ z ^ 2 = χ ∧ ‖z - 1‖ ≤ ‖χ - 1‖ := by
    refine ⟨z, hz, hzw, ?_⟩
    have hz₁ : 1 ≤ ‖z + 1‖ := by
      have h := Complex.abs_re_le_norm (z + 1)
      rw [Complex.add_re, Complex.one_re, abs_of_nonneg (by positivity)] at h
      linarith
    have hfactor : (z - 1) * (z + 1) = χ - 1 := by rw [← hzw]; ring
    rw [← hfactor, norm_mul]
    exact le_mul_of_one_le_right (norm_nonneg _) hz₁
  rcases lt_or_gt_of_ne hwne with hneg | hpos
  · exact hfinish (-w) (by simpa using hneg) (by simpa using hw)
  · exact hfinish w hpos hw

/-- The componentwise correction in the rounded tridiagonal factorization can be
written as an exact Schur-complement correction with a perturbed symmetric edge.
This is the absorption step in the proof of vec:local. -/
theorem exists_absorbed_correction (b x y cₓ cᵧ ω : ℝ)
    (hy : 0 < y) (hω₀ : 0 ≤ ω) (hω : ω ≤ 1 / 128)
    (hcₓ : |cₓ - 1| ≤ 11 * ω) (hcᵧ : |cᵧ - 1| ≤ 11 * ω) :
    ∃ β : ℂ,
      ((b ^ 2 / (x ^ 2 + y ^ 2) : ℝ) : ℂ) * ⟨cₓ * x, cᵧ * y⟩ =
        β ^ 2 / (⟨x, -y⟩ : ℂ) ∧
      (b = 0 → β = 0) ∧
      (b ≠ 0 → ‖β / (b : ℂ) - 1‖ ≤ 11 * ω) := by
  let d : ℂ := ⟨x, -y⟩
  let S : ℝ := x ^ 2 + y ^ 2
  let u : ℂ := ⟨cₓ * x, cᵧ * y⟩
  let χ : ℂ := u * d / (S : ℂ)
  have hS : 0 < S := by dsimp [S]; positivity
  have hd : d ≠ 0 := by
    intro h
    have him : -y = 0 := congrArg Complex.im h
    linarith
  have hSS : (S : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hS.ne'
  have hdS : Complex.normSq d = S := by
    change x * x + -y * -y = x ^ 2 + y ^ 2
    ring
  have hprod : (⟨x, y⟩ : ℂ) * d = (S : ℂ) := by
    apply Complex.ext <;> dsimp [d, S, Complex.mul_re, Complex.mul_im] <;> ring
  have hdiff : u - (⟨x, y⟩ : ℂ) = ⟨(cₓ - 1) * x, (cᵧ - 1) * y⟩ := by
    apply Complex.ext <;> dsimp [u] <;> ring
  have hχeq : χ - 1 = (u - (⟨x, y⟩ : ℂ)) * d / (S : ℂ) := by
    dsimp [χ]
    rw [sub_mul, hprod, sub_div, div_self hSS]
  have hχ : ‖χ - 1‖ ≤ 11 * ω := by
    rw [hχeq, norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hS.le]
    apply (div_le_iff₀ hS).2
    calc
      ‖u - (⟨x, y⟩ : ℂ)‖ * ‖d‖ ≤ (11 * ω * ‖d‖) * ‖d‖ := by
        gcongr
        rw [hdiff]
        exact complex_norm_mk_le_scale (by positivity) hcₓ hcᵧ
      _ = 11 * ω * S := by rw [mul_assoc, ← pow_two, ← Complex.normSq_eq_norm_sq, hdS]
  obtain ⟨z, _, hz, hzbound⟩ :=
    exists_complex_sq_eq_norm_sub_one_le (hχ.trans_lt (by linarith : 11 * ω < 1))
  refine ⟨(b : ℂ) * z, ?_, ?_, ?_⟩
  · change ((b ^ 2 / S : ℝ) : ℂ) * u = ((b : ℂ) * z) ^ 2 / d
    rw [Complex.ofReal_div, Complex.ofReal_pow, mul_pow, hz]
    dsimp [χ]
    field_simp
  · intro hb
    simp [hb]
  · intro hb
    rw [mul_comm, mul_div_cancel_right₀ _ (Complex.ofReal_ne_zero.mpr hb)]
    exact hzbound.trans hχ

open FloatingPointFormat.UnboundedBinary

/-- Rounded squared modulus used for corrections and scores. -/
noncomputable def vectorSquaredModulus (p : ℕ) (hp : 2 ≤ p) (x y : ℝ) : ℝ :=
  roundToEven p hp (roundToEven p hp (x ^ 2) + roundToEven p hp (y ^ 2))

/-- The actual two-component rounded correction, including its zero-edge branch. -/
noncomputable def vectorCorrection (p : ℕ) (hp : 2 ≤ p) (b x y : ℝ) : ℝ × ℝ :=
  if b = 0 then (0, 0)
  else
    let r := roundToEven p hp (roundToEven p hp (b ^ 2) / vectorSquaredModulus p hp x y)
    (roundToEven p hp (r * x), roundToEven p hp (r * y))

private theorem vector_round_model (p : ℕ) (hp : 2 ≤ p) (z : ℝ) :
    ∃ f : ℝ, |f - 1| ≤ unitRoundoff p ∧ roundToEven p hp z = z * f := by
  obtain ⟨δ, hδ, hz⟩ := roundToEven_signedRelErrorWitness p hp z
  refine ⟨1 + δ, ?_, hz⟩
  convert hδ using 2; ring

theorem vectorSquaredModulus_bounds (p : ℕ) (hp : 2 ≤ p) (x y : ℝ) :
    (1 - unitRoundoff p) ^ 2 * (x ^ 2 + y ^ 2) ≤ vectorSquaredModulus p hp x y ∧
      vectorSquaredModulus p hp x y ≤ (1 + unitRoundoff p) ^ 2 * (x ^ 2 + y ^ 2) := by
  obtain ⟨f, hf, ef⟩ := vector_round_model p hp (x ^ 2)
  obtain ⟨g, hg, eg⟩ := vector_round_model p hp (y ^ 2)
  obtain ⟨k, hk, ek⟩ := vector_round_model p hp
    (roundToEven p hp (x ^ 2) + roundToEven p hp (y ^ 2))
  have hsmall := unitRoundoff_le_quarter p hp
  have hlo : 0 ≤ 1 - unitRoundoff p := by linarith
  have hhi : 0 ≤ 1 + unitRoundoff p := by linarith [unitRoundoff_pos p]
  have hlow {a : ℝ} (ha : |a - 1| ≤ unitRoundoff p) : 1 - unitRoundoff p ≤ a := by
    linarith [(abs_le.mp ha).1]
  have hhigh {a : ℝ} (ha : |a - 1| ≤ unitRoundoff p) : a ≤ 1 + unitRoundoff p := by
    linarith [(abs_le.mp ha).2]
  have hf₀ := hlo.trans (hlow hf)
  have hg₀ := hlo.trans (hlow hg)
  unfold vectorSquaredModulus
  rw [ek, ef, eg]
  constructor
  · calc
      _ = (x ^ 2 * (1 - unitRoundoff p) + y ^ 2 * (1 - unitRoundoff p)) *
          (1 - unitRoundoff p) := by ring
      _ ≤ _ := by gcongr <;> first | positivity | exact hlow hf | exact hlow hg | exact hlow hk
  · calc
      _ ≤ (x ^ 2 * (1 + unitRoundoff p) + y ^ 2 * (1 + unitRoundoff p)) *
          (1 + unitRoundoff p) := by
        have hk₀ : 0 ≤ k := hlo.trans (hlow hk)
        gcongr <;> first | positivity | exact hhigh hf | exact hhigh hg | exact hhigh hk
      _ = _ := by ring

theorem vectorSquaredModulus_pos (p : ℕ) (hp : 2 ≤ p) (x y : ℝ) (hy : 0 < y) :
    0 < vectorSquaredModulus p hp x y := by
  have ho : unitRoundoff p ≤ 1 / 4 := unitRoundoff_le_quarter p hp
  have hf : 0 < 1 - unitRoundoff p := by linarith
  exact (show 0 < (1 - unitRoundoff p) ^ 2 * (x ^ 2 + y ^ 2) by positivity).trans_le
    (vectorSquaredModulus_bounds p hp x y).1

private theorem vector_factor_ratio_bound {ω q f g k : ℝ}
    (hω₀ : 0 ≤ ω) (hω : ω ≤ 1 / 128)
    (hq₁ : (1 - ω) ^ 2 ≤ q) (hq₂ : q ≤ (1 + ω) ^ 2)
    (hf : |f - 1| ≤ ω) (hg : |g - 1| ≤ ω) (hk : |k - 1| ≤ ω) :
    |f * g * k / q - 1| ≤ 8 * ω := by
  have hlo : 0 ≤ 1 - ω := by linarith
  have hhi : 0 ≤ 1 + ω := by linarith
  have hlower {a : ℝ} (ha : |a - 1| ≤ ω) : 1 - ω ≤ a := by linarith [(abs_le.mp ha).1]
  have hupper {a : ℝ} (ha : |a - 1| ≤ ω) : a ≤ 1 + ω := by linarith [(abs_le.mp ha).2]
  have hf₀ := hlo.trans (hlower hf)
  have hg₀ := hlo.trans (hlower hg)
  have hk₀ := hlo.trans (hlower hk)
  have hl : (1 - ω) ^ 3 ≤ f * g * k := by
    calc
      _ = (1 - ω) * (1 - ω) * (1 - ω) := by ring
      _ ≤ _ := by
        gcongr <;> first | exact hlower hf | exact hlower hg | exact hlower hk
  have hu : f * g * k ≤ (1 + ω) ^ 3 := by
    calc
      _ ≤ (1 + ω) * (1 + ω) * (1 + ω) := by
        gcongr <;> first | exact hupper hf | exact hupper hg | exact hupper hk
      _ = _ := by ring
  have hpow : ω ^ 2 ≤ (1 / 128) * ω := by
    nlinarith [mul_nonneg hω₀ (sub_nonneg.mpr hω)]
  have hcube : ω ^ 3 ≤ (1 / 128) ^ 2 * ω := by
    nlinarith [mul_nonneg hω₀ (sub_nonneg.mpr hpow)]
  have hq₀ : 0 < q :=
    (sq_pos_of_pos (show 0 < 1 - ω by linarith)).trans_le hq₁
  have hω₈ : 0 ≤ 1 - 8 * ω := by linarith
  apply abs_le.mpr
  constructor
  · have h := (le_div_iff₀ hq₀).2 (show (1 - 8 * ω) * q ≤ f * g * k from
      calc
        _ ≤ (1 - 8 * ω) * (1 + ω) ^ 2 := mul_le_mul_of_nonneg_left hq₂ hω₈
        _ ≤ (1 - ω) ^ 3 := by nlinarith [pow_nonneg hω₀ 3]
        _ ≤ _ := hl)
    linarith
  · have h := (div_le_iff₀ hq₀).2 (show f * g * k ≤ (1 + 8 * ω) * q from
      calc
        _ ≤ (1 + ω) ^ 3 := hu
        _ ≤ (1 + 8 * ω) * (1 - ω) ^ 2 := by nlinarith [pow_nonneg hω₀ 3]
        _ ≤ _ := mul_le_mul_of_nonneg_left hq₁ (by positivity))
    linarith

/-- Both components of the actual rounded correction have the factors from
the component-correction identity in the proof of vec:local. -/
theorem rounded_vectorCorrection_factors
    (p : ℕ) (hp : 2 ≤ p) (hω : unitRoundoff p ≤ 1 / 128) (b x y : ℝ) (hy : 0 < y) :
    ∃ κx κy : ℝ,
      |κx - 1| ≤ 8 * unitRoundoff p ∧ |κy - 1| ≤ 8 * unitRoundoff p ∧
      (vectorCorrection p hp b x y).1 = κx * (b ^ 2 * x / (x ^ 2 + y ^ 2)) ∧
      (vectorCorrection p hp b x y).2 = κy * (b ^ 2 * y / (x ^ 2 + y ^ 2)) := by
  have hω₀ := (unitRoundoff_pos p).le
  by_cases hb : b = 0
  · exact ⟨1, 1, by simp; positivity, by simp; positivity, by simp [hb, vectorCorrection]⟩
  let s := vectorSquaredModulus p hp x y
  let S := x ^ 2 + y ^ 2
  have hs := vectorSquaredModulus_pos p hp x y hy
  have hS : 0 < S := by dsimp [S]; positivity
  let r := roundToEven p hp (roundToEven p hp (b ^ 2) / s)
  obtain ⟨f, hf, ef⟩ := vector_round_model p hp (b ^ 2)
  obtain ⟨g, hg, eg⟩ := vector_round_model p hp (roundToEven p hp (b ^ 2) / s)
  obtain ⟨kx, hkx, ekx⟩ := vector_round_model p hp (r * x)
  obtain ⟨ky, hky, eky⟩ := vector_round_model p hp (r * y)
  obtain ⟨hlo, hhi⟩ := vectorSquaredModulus_bounds p hp x y
  have hlo' : (1 - unitRoundoff p) ^ 2 ≤ s / S := (le_div_iff₀ hS).2 hlo
  have hhi' : s / S ≤ (1 + unitRoundoff p) ^ 2 := (div_le_iff₀ hS).2 hhi
  have he (z k : ℝ) (hz : roundToEven p hp (r * z) = r * z * k) :
      roundToEven p hp (r * z) = (f * g * k / (s / S)) * (b ^ 2 * z / S) := by
    rw [hz]
    dsimp [r]
    rw [eg, ef]
    field_simp [hs.ne', hS.ne']
  refine ⟨f * g * kx / (s / S), f * g * ky / (s / S),
    vector_factor_ratio_bound hω₀ hω hlo' hhi' hf hg hkx,
    vector_factor_ratio_bound hω₀ hω hlo' hhi' hf hg hky, ?_, ?_⟩
  · simpa only [vectorCorrection, if_neg hb] using he x kx ekx
  · simpa only [vectorCorrection, if_neg hb] using he y ky eky

/-- The rounded directional update shared by the left and right sweeps. -/
noncomputable def vectorPivotStep (p : ℕ) (hp : 2 ≤ p)
    (h η b x y : ℝ) : ℝ × ℝ :=
  let c := vectorCorrection p hp b x y
  (roundToEven p hp (h - c.1), roundToEven p hp (η + c.2))

/-- The rounded twist takes the left contribution first, then the right.
A zero edge supplies the zero correction, including at either absent endpoint. -/
noncomputable def vectorTwist (p : ℕ) (hp : 2 ≤ p) (h η bL xL yL bR xR yR : ℝ) :
    ℝ × ℝ :=
  let left := vectorPivotStep p hp h η bL xL yL
  let right := vectorCorrection p hp bR xR yR
  (roundToEven p hp (left.1 - right.1), roundToEven p hp (left.2 + right.2))

private theorem vector_round_abs_le (p : ℕ) (hp : 2 ≤ p) (x : ℝ) :
    |roundToEven p hp x| ≤ (1 + unitRoundoff p) * |x| := by
  obtain ⟨f, hf, he⟩ := vector_round_model p hp x
  have hf₀ : 0 ≤ f := by linarith [(abs_le.mp hf).1, unitRoundoff_le_quarter p hp]
  have hf₁ : f ≤ 1 + unitRoundoff p := by linarith [(abs_le.mp hf).2]
  rw [he, abs_mul, abs_of_nonneg hf₀, mul_comm]
  exact mul_le_mul_of_nonneg_right hf₁ (abs_nonneg _)

private theorem vectorCorrection_im_nonneg
    (p : ℕ) (hp : 2 ≤ p) (hω : unitRoundoff p ≤ 1 / 128) (b x y : ℝ) (hy : 0 < y) :
    0 ≤ (vectorCorrection p hp b x y).2 := by
  obtain ⟨κx, κy, _, hκy, _, ey⟩ := rounded_vectorCorrection_factors p hp hω b x y hy
  have hκy₀ : 0 ≤ κy := by linarith [(abs_le.mp hκy).1]
  rw [ey]
  positivity

theorem vectorPivotStep_im_lower
    (p : ℕ) (hp : 2 ≤ p) (hω : unitRoundoff p ≤ 1 / 128)
    (h η b x y : ℝ) (hη : Native p hp η) (hy : 0 < y) :
    η ≤ (vectorPivotStep p hp h η b x y).2 := by
  have hmono := roundToEven_monotone p hp
  have hle : η ≤ η + (vectorCorrection p hp b x y).2 :=
    le_add_of_nonneg_right (vectorCorrection_im_nonneg p hp hω b x y hy)
  simpa only [vectorPivotStep, roundToEven_eq_self_of_native hη] using hmono hle

/-- Monotonic nearest-even rounding preserves the represented imaginary shift
through both twist additions. -/
theorem vectorTwist_im_lower
    (p : ℕ) (hp : 2 ≤ p) (hω : unitRoundoff p ≤ 1 / 128)
    (h η bL xL yL bR xR yR : ℝ) (hη : Native p hp η) (hyL : 0 < yL) (hyR : 0 < yR) :
    η ≤ (vectorTwist p hp h η bL xL yL bR xR yR).2 := by
  have hle : η ≤ (vectorPivotStep p hp h η bL xL yL).2 +
      (vectorCorrection p hp bR xR yR).2 :=
    (vectorPivotStep_im_lower p hp hω h η bL xL yL hη hyL).trans
      (le_add_of_nonneg_right (vectorCorrection_im_nonneg p hp hω bR xR yR hyR))
  simpa only [vectorTwist, roundToEven_eq_self_of_native hη] using
    (roundToEven_monotone p hp) hle

private theorem vectorCorrection_abs_bounds
    (p : ℕ) (hp : 2 ≤ p) (hω : unitRoundoff p ≤ 1 / 128)
    (η b x y : ℝ) (hη : 0 < η) (hy : η ≤ y) (hb : |b| ≤ 1) :
    |(vectorCorrection p hp b x y).1| ≤ (1 + 8 * unitRoundoff p) / (2 * η) ∧
    |(vectorCorrection p hp b x y).2| ≤ (1 + 8 * unitRoundoff p) / η := by
  have hy₀ := hη.trans_le hy
  have hS : 0 < x ^ 2 + y ^ 2 := by positivity
  have hb₂ : b ^ 2 ≤ 1 := by simpa using (sq_le_sq (a := b) (b := 1)).2 (by simpa using hb)
  have hratioX : |x| / (x ^ 2 + y ^ 2) ≤ (1 : ℝ) / (2 * η) := by
    apply (div_le_div_iff₀ hS (by positivity)).2
    have hsq : |x| ^ 2 = x ^ 2 := sq_abs x
    nlinarith [sq_nonneg (|x| - y), mul_nonneg (abs_nonneg x) (sub_nonneg.mpr hy)]
  have hratioY : y / (x ^ 2 + y ^ 2) ≤ (1 : ℝ) / η := by
    apply (div_le_div_iff₀ hS hη).2
    nlinarith [sq_nonneg x, mul_nonneg hy₀.le (sub_nonneg.mpr hy)]
  obtain ⟨κx, κy, hx, hκy, ex, ey⟩ := rounded_vectorCorrection_factors p hp hω b x y hy₀
  have hκ {f : ℝ} (hf : |f - 1| ≤ 8 * unitRoundoff p) :
      |f| ≤ 1 + 8 * unitRoundoff p := by
    have hf₀ : 0 ≤ f := by linarith [(abs_le.mp hf).1]
    rw [abs_of_nonneg hf₀]
    linarith [(abs_le.mp hf).2]
  have hfactor : 0 ≤ 1 + 8 * unitRoundoff p := by linarith [unitRoundoff_pos p]
  have hbound {f z t : ℝ} (hf : |f - 1| ≤ 8 * unitRoundoff p) (hz : 0 ≤ z)
      (ht : z / (x ^ 2 + y ^ 2) ≤ 1 / t) :
      |f| * (b ^ 2 * z / (x ^ 2 + y ^ 2)) ≤ (1 + 8 * unitRoundoff p) / t := by
    rw [mul_div_assoc, ← mul_one_div (1 + 8 * unitRoundoff p) t]
    refine mul_le_mul (hκ hf) ?_ (by positivity) hfactor
    exact (show b ^ 2 * (z / (x ^ 2 + y ^ 2)) ≤ z / (x ^ 2 + y ^ 2) from
      mul_le_of_le_one_left (by positivity) hb₂).trans ht
  constructor
  · rw [ex, abs_mul, abs_div, abs_mul, abs_of_nonneg (sq_nonneg b), abs_of_pos hS]
    exact hbound hx (abs_nonneg _) hratioX
  · rw [ey, abs_mul, abs_div, abs_mul, abs_of_nonneg (sq_nonneg b), abs_of_pos hy₀,
      abs_of_pos hS]
    exact hbound hκy hy₀.le hratioY

private theorem vectorPivot_norm_bound {x y η : ℝ}
    (hη : 0 < η) (hx : |x| ≤ 4 / η) (hy₀ : 0 ≤ y) (hy : y ≤ 2 / η) :
    ‖(⟨x, -y⟩ : ℂ)‖ ≤ 8 / η := by
  have he : (⟨x, -y⟩ : ℂ) = (x : ℂ) - (y : ℂ) * Complex.I := by
    apply Complex.ext <;> simp
  rw [he]
  calc
    _ ≤ ‖(x : ℂ)‖ + ‖(y : ℂ) * Complex.I‖ := norm_sub_le _ _
    _ = |x| + y := by simp [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hy₀]
    _ ≤ 4 / η + 2 / η := add_le_add hx hy
    _ ≤ _ := by
      rw [← add_div]
      gcongr
      norm_num

/-- The magnitude and imaginary lower bounds in vec:pivot-bounds for the initial
pivot at either endpoint. -/
theorem rounded_vector_initial_pivot_bounds
    (p : ℕ) (hp : 2 ≤ p) (hω : unitRoundoff p ≤ 1 / 128) (a η : ℝ)
    (ha : |a| ≤ 5) (hη : 0 < η) (hη₁ : η ≤ 1 / 2) :
    |roundToEven p hp a| ≤ 4 / η ∧ η ≤ 2 / η ∧
      ‖(⟨roundToEven p hp a, -η⟩ : ℂ)‖ ≤ 8 / η := by
  have hw₀ := (unitRoundoff_pos p).le
  have hreal : |roundToEven p hp a| ≤ 4 / η := by
    apply (le_div_iff₀ hη).2
    calc
      _ ≤ ((129 / 128) * 5) * (1 / 2) :=
        mul_le_mul (le_trans (vector_round_abs_le p hp a)
          (mul_le_mul (by linarith) ha (abs_nonneg a) (by norm_num))) hη₁ hη.le (by norm_num)
      _ ≤ _ := by norm_num
  have him : η ≤ 2 / η := (le_div_iff₀ hη).2 <| calc
    _ ≤ (1 / 2) * (1 / 2) := mul_le_mul hη₁ hη₁ hη.le (by norm_num)
    _ ≤ _ := by norm_num
  exact ⟨hreal, him, vectorPivot_norm_bound hη hreal hη.le him⟩

/-- The source magnitude and imaginary lower bounds for a directional pivot.
The old pivot needs only the lower bound on its imaginary component. -/
theorem rounded_vector_pivot_step_bounds
    (p : ℕ) (hp : 2 ≤ p) (hω : unitRoundoff p ≤ 1 / 128)
    (a η b x y : ℝ) (ha : |a| ≤ 5) (hb : |b| ≤ 1)
    (hη : 0 < η) (hη₁ : η ≤ 1 / 2) (hηn : Native p hp η) (hy : η ≤ y) :
    let next := vectorPivotStep p hp (roundToEven p hp a) η b x y
    |next.1| ≤ 4 / η ∧ η ≤ next.2 ∧ next.2 ≤ 2 / η ∧
      ‖(⟨next.1, -next.2⟩ : ℂ)‖ ≤ 8 / η := by
  let h := roundToEven p hp a
  let c := vectorCorrection p hp b x y
  let next := vectorPivotStep p hp h η b x y
  have hw₀ := (unitRoundoff_pos p).le
  have hround : 1 + unitRoundoff p ≤ (129 / 128 : ℝ) := by linarith
  have hc : 1 + 8 * unitRoundoff p ≤ (17 / 16 : ℝ) := by linarith
  obtain ⟨hcx, hcy⟩ := vectorCorrection_abs_bounds p hp hω η b x y hη hy hb
  have hh : |h| ≤ (129 / 128) * 5 :=
    (vector_round_abs_le p hp a).trans (mul_le_mul hround ha (abs_nonneg _) (by norm_num))
  have hcx' : |c.1| ≤ (17 / 16) / (2 * η) :=
    hcx.trans (div_le_div_of_nonneg_right hc (by positivity))
  have hcy' : |c.2| ≤ (17 / 16) / η :=
    hcy.trans (div_le_div_of_nonneg_right hc hη.le)
  have hreal : |next.1| ≤ 4 / η := by
    have hreal0 : |next.1| ≤ (129 / 128) * ((129 / 128) * 5 + (17 / 16) / (2 * η)) :=
      (vector_round_abs_le p hp _).trans
        (mul_le_mul hround ((abs_sub _ _).trans (add_le_add hh hcx')) (abs_nonneg _) (by norm_num))
    apply (le_div_iff₀ hη).2
    calc
      _ ≤ ((129 / 128) * ((129 / 128) * 5 + (17 / 16) / (2 * η))) * η :=
        mul_le_mul_of_nonneg_right hreal0 hη.le
      _ = (129 / 128) * ((129 / 128) * 5 * η + 17 / 32) := by
        field_simp [hη.ne']
        ring
      _ ≤ (129 / 128) * ((129 / 128) * 5 * (1 / 2) + 17 / 32) := by
        gcongr
      _ ≤ _ := by norm_num
  have him_low : η ≤ next.2 := vectorPivotStep_im_lower p hp hω h η b x y hηn (hη.trans_le hy)
  have him₀ : 0 ≤ next.2 := hη.le.trans him_low
  have him : next.2 ≤ 2 / η := by
    have him_abs : |next.2| ≤ (129 / 128) * (η + (17 / 16) / η) :=
      (vector_round_abs_le p hp _).trans
        (mul_le_mul hround ((abs_add_le _ _).trans
          (by simpa only [abs_of_pos hη] using add_le_add_right hcy' |η|))
          (abs_nonneg _) (by norm_num))
    rw [abs_of_nonneg him₀] at him_abs
    apply (le_div_iff₀ hη).2
    calc
      _ ≤ ((129 / 128) * (η + (17 / 16) / η)) * η :=
        mul_le_mul_of_nonneg_right him_abs hη.le
      _ = (129 / 128) * (η * η + 17 / 16) := by field_simp [hη.ne']
      _ ≤ (129 / 128) * ((1 / 2) * (1 / 2) + 17 / 16) := by
        gcongr
      _ ≤ _ := by norm_num
  exact ⟨hreal, him_low, him, vectorPivot_norm_bound hη hreal him₀ him⟩

private theorem vector_factor_mul_bound {ω f g : ℝ}
    (_hω₀ : 0 ≤ ω) (hω : ω ≤ 1 / 128) (hg : |g - 1| ≤ ω) :
    |f * g - 1| ≤ |f - 1| * (1 + ω) + ω := by
  have hg₀ : 0 ≤ g := by linarith [(abs_le.mp hg).1]
  have hg₁ : |g| ≤ 1 + ω := by rw [abs_of_nonneg hg₀]; linarith [(abs_le.mp hg).2]
  rw [show f * g - 1 = (f - 1) * g + (g - 1) by ring]
  calc
    _ ≤ |(f - 1) * g| + |g - 1| := abs_add_le _ _
    _ ≤ _ := by
      rw [abs_mul]
      exact add_le_add (mul_le_mul_of_nonneg_left hg₁ (abs_nonneg _)) hg

private theorem vector_factor_two {ω f g : ℝ}
    (hω₀ : 0 ≤ ω) (hω : ω ≤ 1 / 128) (hf : |f - 1| ≤ ω) (hg : |g - 1| ≤ ω) :
    |f * g - 1| ≤ 2 * ω + ω ^ 2 := by
  calc
    _ ≤ |f - 1| * (1 + ω) + ω := vector_factor_mul_bound hω₀ hω hg
    _ ≤ ω * (1 + ω) + ω := by gcongr
    _ = _ := by ring

private theorem vector_factor_three {ω f g k : ℝ}
    (hω₀ : 0 ≤ ω) (hω : ω ≤ 1 / 128)
    (hf : |f - 1| ≤ ω) (hg : |g - 1| ≤ ω) (hk : |k - 1| ≤ ω) :
    |f * g * k - 1| ≤ 3 * ω + 3 * ω ^ 2 + ω ^ 3 := by
  calc
    _ ≤ |f * g - 1| * (1 + ω) + ω := vector_factor_mul_bound hω₀ hω hk
    _ ≤ (2 * ω + ω ^ 2) * (1 + ω) + ω := by gcongr; exact vector_factor_two hω₀ hω hf hg
    _ = _ := by ring

private theorem vector_scaled_factor_two {ω f g : ℝ}
    (hω₀ : 0 ≤ ω) (hω : ω ≤ 1 / 128) (hf : |f - 1| ≤ 8 * ω) (hg : |g - 1| ≤ ω) :
    |f * g - 1| ≤ 9 * ω + 8 * ω ^ 2 := by
  calc
    _ ≤ |f - 1| * (1 + ω) + ω := vector_factor_mul_bound hω₀ hω hg
    _ ≤ 8 * ω * (1 + ω) + ω := by gcongr
    _ = _ := by ring

private theorem vector_scaled_factor_three {ω f g k : ℝ}
    (hω₀ : 0 ≤ ω) (hω : ω ≤ 1 / 128)
    (hf : |f - 1| ≤ 8 * ω) (hg : |g - 1| ≤ ω) (hk : |k - 1| ≤ ω) :
    |f * g * k - 1| ≤ 11 * ω := by
  have hpow : ω ^ 2 ≤ (1 / 128) * ω := by
    nlinarith [mul_nonneg hω₀ (sub_nonneg.mpr hω)]
  have hcube : ω ^ 3 ≤ (1 / 128) ^ 2 * ω := by
    nlinarith [mul_nonneg hω₀ (sub_nonneg.mpr hpow)]
  calc
    _ ≤ |f * g - 1| * (1 + ω) + ω := vector_factor_mul_bound hω₀ hω hk
    _ ≤ (9 * ω + 8 * ω ^ 2) * (1 + ω) + ω := by
      gcongr
      exact vector_scaled_factor_two hω₀ hω hf hg
    _ ≤ _ := by nlinarith

private theorem vector_scaled_factor_le_eleven {ω f g : ℝ}
    (hω₀ : 0 ≤ ω) (hω : ω ≤ 1 / 128) (hf : |f - 1| ≤ 8 * ω) (hg : |g - 1| ≤ ω) :
    |f * g - 1| ≤ 11 * ω := by
  simpa only [mul_one] using vector_scaled_factor_three (k := 1) hω₀ hω hf hg
    (by simpa using hω₀)

private theorem vector_diag_error_bound (a η f g : ℝ) :
    ‖(⟨a * f, -(η * g)⟩ : ℂ) - ⟨a, -η⟩‖ ≤ |a| * |f - 1| + |η| * |g - 1| := by
  have he : (⟨a * f, -(η * g)⟩ : ℂ) - ⟨a, -η⟩ =
      ((a * (f - 1) : ℝ) : ℂ) - ((η * (g - 1) : ℝ) : ℂ) * Complex.I := by
    apply Complex.ext <;> simp <;> ring
  rw [he]
  calc
    _ ≤ ‖((a * (f - 1) : ℝ) : ℂ)‖ + ‖((η * (g - 1) : ℝ) : ℂ) * Complex.I‖ := norm_sub_le _ _
    _ = _ := by rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul]

/-- The actual rounded directional update is an exact elimination step with a
perturbed diagonal and a perturbed symmetric edge. -/
theorem rounded_vector_pivot_step_backward
    (p : ℕ) (hp : 2 ≤ p) (hω : unitRoundoff p ≤ 1 / 128)
    (a η b x y : ℝ) (ha : |a| ≤ 5) (hη₀ : 0 ≤ η) (hη : η ≤ 1 / 2) (hy : 0 < y) :
    let next := vectorPivotStep p hp (roundToEven p hp a) η b x y
    ∃ D β : ℂ,
      (⟨next.1, -next.2⟩ : ℂ) = D - β ^ 2 / (⟨x, -y⟩ : ℂ) ∧
      ‖D - ⟨a, -η⟩‖ ≤ 11 * unitRoundoff p ∧
      (b = 0 → β = 0) ∧ (b ≠ 0 → ‖β / (b : ℂ) - 1‖ ≤ 11 * unitRoundoff p) := by
  let c := vectorCorrection p hp b x y
  have hw₀ := (unitRoundoff_pos p).le
  obtain ⟨κx, κy, hkx, hky, ex, ey⟩ := rounded_vectorCorrection_factors p hp hω b x y hy
  obtain ⟨fh, hfh, eh⟩ := vector_round_model p hp a
  obtain ⟨fx, hfx, efx⟩ := vector_round_model p hp (roundToEven p hp a - c.1)
  obtain ⟨fy, hfy, efy⟩ := vector_round_model p hp (η + c.2)
  obtain ⟨β, eβ, hβ₀, hβ⟩ := exists_absorbed_correction b x y (κx * fx) (κy * fy)
    (unitRoundoff p) hy hw₀ hω (vector_scaled_factor_le_eleven hw₀ hω hkx hfx)
    (vector_scaled_factor_le_eleven hw₀ hω hky hfy)
  let D : ℂ := ⟨a * (fh * fx), -(η * fy)⟩
  refine ⟨D, β, ?_, ?_, hβ₀, hβ⟩
  · dsimp only [vectorPivotStep]
    change (⟨roundToEven p hp (roundToEven p hp a - c.1),
      -roundToEven p hp (η + c.2)⟩ : ℂ) = D - β ^ 2 / ⟨x, -y⟩
    change c.1 = _ at ex
    change c.2 = _ at ey
    rw [efx, efy, eh, ex, ey, ← eβ]
    apply Complex.ext <;>
      simp only [D, Complex.sub_re, Complex.sub_im, Complex.re_ofReal_mul, Complex.im_ofReal_mul, div_eq_mul_inv] <;> ring
  · have hhx := vector_factor_two hw₀ hω hfh hfx
    have hpow : unitRoundoff p ^ 2 ≤ (1 / 128) * unitRoundoff p := by
      nlinarith [mul_nonneg hw₀ (sub_nonneg.mpr hω)]
    calc
      _ ≤ |a| * |fh * fx - 1| + |η| * |fy - 1| := vector_diag_error_bound a η _ _
      _ ≤ 5 * (2 * unitRoundoff p + unitRoundoff p ^ 2) + (1 / 2) * unitRoundoff p :=
        add_le_add (mul_le_mul ha hhx (abs_nonneg _) (by norm_num))
          (mul_le_mul (by simpa only [abs_of_nonneg hη₀] using hη) hfy
            (abs_nonneg _) (by norm_num))
      _ ≤ _ := by nlinarith

set_option maxHeartbeats 500000 in
/-- The actual rounded twist is exact with one locally perturbed diagonal and
two locally perturbed symmetric edges. -/
theorem rounded_vector_twist_backward
    (p : ℕ) (hp : 2 ≤ p) (hω : unitRoundoff p ≤ 1 / 128)
    (a η bL xL yL bR xR yR : ℝ) (ha : |a| ≤ 5) (hη₀ : 0 ≤ η) (hη : η ≤ 1 / 2)
    (hyL : 0 < yL) (hyR : 0 < yR) :
    let t := vectorTwist p hp (roundToEven p hp a) η bL xL yL bR xR yR
    ∃ D βL βR : ℂ,
      (⟨t.1, -t.2⟩ : ℂ) = D - βL ^ 2 / (⟨xL, -yL⟩ : ℂ) - βR ^ 2 / (⟨xR, -yR⟩ : ℂ) ∧
      ‖D - ⟨a, -η⟩‖ ≤ 17 * unitRoundoff p ∧
      (bL = 0 → βL = 0) ∧ (bL ≠ 0 → ‖βL / (bL : ℂ) - 1‖ ≤ 11 * unitRoundoff p) ∧
      (bR = 0 → βR = 0) ∧ (bR ≠ 0 → ‖βR / (bR : ℂ) - 1‖ ≤ 11 * unitRoundoff p) := by
  let cL := vectorCorrection p hp bL xL yL
  let cR := vectorCorrection p hp bR xR yR
  let h := roundToEven p hp a
  let left := vectorPivotStep p hp h η bL xL yL
  have hw₀ := (unitRoundoff_pos p).le
  obtain ⟨κxL, κyL, hkxL, hkyL, exL, eyL⟩ := rounded_vectorCorrection_factors p hp hω bL xL yL hyL
  obtain ⟨κxR, κyR, hkxR, hkyR, exR, eyR⟩ := rounded_vectorCorrection_factors p hp hω bR xR yR hyR
  obtain ⟨fh, hfh, eh⟩ := vector_round_model p hp a
  obtain ⟨fxL, hfxL, efxL⟩ := vector_round_model p hp (h - cL.1)
  obtain ⟨fyL, hfyL, efyL⟩ := vector_round_model p hp (η + cL.2)
  obtain ⟨fxR, hfxR, efxR⟩ := vector_round_model p hp (left.1 - cR.1)
  obtain ⟨fyR, hfyR, efyR⟩ := vector_round_model p hp (left.2 + cR.2)
  obtain ⟨βL, eβL, hβL₀, hβL⟩ := exists_absorbed_correction bL xL yL
    (κxL * fxL * fxR) (κyL * fyL * fyR) (unitRoundoff p) hyL hw₀ hω
    (vector_scaled_factor_three hw₀ hω hkxL hfxL hfxR)
    (vector_scaled_factor_three hw₀ hω hkyL hfyL hfyR)
  obtain ⟨βR, eβR, hβR₀, hβR⟩ := exists_absorbed_correction bR xR yR
    (κxR * fxR) (κyR * fyR) (unitRoundoff p) hyR hw₀ hω
    (vector_scaled_factor_le_eleven hw₀ hω hkxR hfxR)
    (vector_scaled_factor_le_eleven hw₀ hω hkyR hfyR)
  let D : ℂ := ⟨a * (fh * fxL * fxR), -(η * (fyL * fyR))⟩
  refine ⟨D, βL, βR, ?_, ?_, hβL₀, hβL, hβR₀, hβR⟩
  · change (⟨roundToEven p hp (left.1 - cR.1), -roundToEven p hp (left.2 + cR.2)⟩ : ℂ) =
      D - βL ^ 2 / ⟨xL, -yL⟩ - βR ^ 2 / ⟨xR, -yR⟩
    change cL.1 = _ at exL
    change cL.2 = _ at eyL
    change cR.1 = _ at exR
    change cR.2 = _ at eyR
    rw [efxR, efyR]
    change (⟨(roundToEven p hp (h - cL.1) - cR.1) * fxR,
      -((roundToEven p hp (η + cL.2) + cR.2) * fyR)⟩ : ℂ) =
      D - βL ^ 2 / ⟨xL, -yL⟩ - βR ^ 2 / ⟨xR, -yR⟩
    have eh' : h = a * fh := eh
    rw [efxL, efyL, eh', exL, eyL, exR, eyR, ← eβL, ← eβR]
    apply Complex.ext <;>
      simp only [D, Complex.sub_re, Complex.sub_im, Complex.re_ofReal_mul, Complex.im_ofReal_mul,
        div_eq_mul_inv] <;> ring
  · have hhh := vector_factor_three hw₀ hω hfh hfxL hfxR
    have hhy := vector_factor_two hw₀ hω hfyL hfyR
    have hpow : unitRoundoff p ^ 2 ≤ (1 / 128) * unitRoundoff p := by
      nlinarith [mul_nonneg hw₀ (sub_nonneg.mpr hω)]
    have hcube : unitRoundoff p ^ 3 ≤ (1 / 128) ^ 2 * unitRoundoff p := by
      nlinarith [mul_nonneg hw₀ (sub_nonneg.mpr hpow)]
    calc
      _ ≤ |a| * |fh * fxL * fxR - 1| + |η| * |fyL * fyR - 1| :=
        vector_diag_error_bound a η _ _
      _ ≤ 5 * (3 * unitRoundoff p + 3 * unitRoundoff p ^ 2 + unitRoundoff p ^ 3) +
          (1 / 2) * (2 * unitRoundoff p + unitRoundoff p ^ 2) :=
        add_le_add (mul_le_mul ha hhh (abs_nonneg _) (by norm_num))
          (mul_le_mul (by simpa only [abs_of_nonneg hη₀] using hη) hhy
            (abs_nonneg _) (by norm_num))
      _ ≤ _ := by nlinarith

/-- The actual stored score at a twist. -/
noncomputable def vectorScore (p : ℕ) (hp : 2 ≤ p) (twist : ℝ × ℝ) : ℝ :=
  roundToEven p hp (twist.2 / vectorSquaredModulus p hp twist.1 twist.2)

end NumStability.CertifiedTridiagonalEigenpairs
