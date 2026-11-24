import ComputationalMathematics.Analysis.Error.RoundingProducts.Core
import ComputationalMathematics.Source.CertifiedTridiagonalEigenpairs.RoundedVectorLocal.Proof
import Mathlib.Analysis.Normed.Lp.PiLp

namespace NumStability.CertifiedTridiagonalEigenpairs

open FloatingPointFormat.UnboundedBinary

/-- The two rounded component divisions for the reciprocal of the twist. -/
noncomputable def roundedTwistReciprocal (p : ℕ) (hp : 2 ≤ p) (x y : ℝ) : ℂ :=
  let s := vectorSquaredModulus p hp x y
  ⟨roundToEven p hp (x / s), roundToEven p hp (y / s)⟩

/-- The quotient of the original real edge by a pivot, computed using two
rounded real products and two rounded real divisions after the squared modulus. -/
noncomputable def roundedEdgeQuotient (p : ℕ) (hp : 2 ≤ p) (b x y : ℝ) : ℂ :=
  let s := vectorSquaredModulus p hp x y
  ⟨roundToEven p hp (roundToEven p hp (b * x) / s),
    roundToEven p hp (roundToEven p hp (b * y) / s)⟩

/-- Four rounded real products followed by the rounded real difference and sum. -/
noncomputable def roundedComplexProduct (p : ℕ) (hp : 2 ≤ p) (z v : ℂ) : ℂ :=
  let R := roundToEven p hp
  ⟨R (R (z.re * v.re) - R (z.im * v.im)),
    R (R (z.re * v.im) + R (z.im * v.re))⟩

private theorem norm_mk_le_mul {a b A B c : ℝ}
    (hc : 0 ≤ c) (ha : |a| ≤ c * |A|) (hb : |b| ≤ c * |B|) :
    ‖(⟨a, b⟩ : ℂ)‖ ≤ c * ‖(⟨A, B⟩ : ℂ)‖ := by
  apply le_of_sq_le_sq _ (by positivity)
  rw [mul_pow, Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]
  change a * a + b * b ≤ c ^ 2 * (A * A + B * B)
  have ha' := mul_le_mul ha ha (abs_nonneg a) (by positivity)
  have hb' := mul_le_mul hb hb (abs_nonneg b) (by positivity)
  rw [mul_mul_mul_comm, ← pow_two, ← pow_two, ← pow_two, sq_abs, sq_abs] at ha' hb'
  nlinarith only [ha', hb']

private theorem complex_sub_le_of_components {z v : ℂ} {c : ℝ} (hc : 0 ≤ c)
    (hre : |z.re - v.re| ≤ c * |v.re|) (him : |z.im - v.im| ≤ c * |v.im|) :
    ‖z - v‖ ≤ c * ‖v‖ := by
  convert norm_mk_le_mul hc hre him using 2

private theorem rounded_factor (p : ℕ) (hp : 2 ≤ p) (x : ℝ) :
    ∃ f : ℝ, 1 - unitRoundoff p ≤ f ∧ f ≤ 1 + unitRoundoff p ∧
      roundToEven p hp x = x * f := by
  obtain ⟨δ, hδ, h⟩ := roundToEven_signedRelErrorWitness p hp x
  exact ⟨1 + δ, by linarith [(abs_le.mp hδ).1], by linarith [(abs_le.mp hδ).2], h⟩

private theorem ratio_error {ω d f L U C : ℝ}
    (hω : 0 ≤ ω) (hCd : 0 ≤ 1 - C * ω) (hd : 0 < d)
    (hdl : (1 - ω) ^ 2 ≤ d) (hdu : d ≤ (1 + ω) ^ 2)
    (hfL : L ≤ f) (hfU : f ≤ U)
    (hL : (1 - C * ω) * (1 + ω) ^ 2 ≤ L)
    (hU : U ≤ (1 + C * ω) * (1 - ω) ^ 2) (hC : 0 ≤ C) :
    |f / d - 1| ≤ C * ω := by
  apply abs_le.mpr
  constructor
  · have h := (le_div_iff₀ hd).mpr
      ((mul_le_mul_of_nonneg_left hdu hCd).trans (hL.trans hfL))
    linarith
  · have h := (div_le_iff₀ hd).mpr
      (hfU.trans (hU.trans (mul_le_mul_of_nonneg_left hdl (by positivity))))
    linarith

private theorem reciprocal_factor_error {ω d f : ℝ}
    (hω₀ : 0 ≤ ω) (hω : ω ≤ 1 / 128) (hd : 0 < d)
    (hdl : (1 - ω) ^ 2 ≤ d) (hdu : d ≤ (1 + ω) ^ 2)
    (hfl : 1 - ω ≤ f) (hfu : f ≤ 1 + ω) :
    |f / d - 1| ≤ 4 * ω := by
  have hω₂ : ω ^ 2 ≤ ω / 128 := by nlinarith [mul_nonneg hω₀ (sub_nonneg.mpr hω)]
  apply ratio_error hω₀ (by linarith) hd hdl hdu hfl hfu _ _ (by norm_num)
  · nlinarith [pow_nonneg hω₀ 3]
  · nlinarith [pow_nonneg hω₀ 3]

private theorem quotient_factor_error {ω d f g : ℝ}
    (hω₀ : 0 ≤ ω) (hω : ω ≤ 1 / 128) (hd : 0 < d)
    (hdl : (1 - ω) ^ 2 ≤ d) (hdu : d ≤ (1 + ω) ^ 2)
    (hfl : 1 - ω ≤ f) (hfu : f ≤ 1 + ω) (hgl : 1 - ω ≤ g) (hgu : g ≤ 1 + ω) :
    |f * g / d - 1| ≤ 6 * ω := by
  have hω₂ : ω ^ 2 ≤ ω / 128 := by nlinarith [mul_nonneg hω₀ (sub_nonneg.mpr hω)]
  have hf₀ : 0 ≤ f := by linarith
  have hl : (1 - ω) ^ 2 ≤ f * g := by
    rw [pow_two]
    exact mul_le_mul hfl hgl (by linarith) hf₀
  have hu : f * g ≤ (1 + ω) ^ 2 := by
    rw [pow_two]
    exact mul_le_mul hfu hgu (by linarith) (by linarith)
  apply ratio_error hω₀ (by linarith) hd hdl hdu hl hu _ _ (by norm_num)
  · nlinarith [pow_nonneg hω₀ 3]
  · nlinarith [pow_nonneg hω₀ 3]

private theorem rounded_modulus_ratio (p : ℕ) (hp : 2 ≤ p) (x y : ℝ) (hy : 0 < y) :
    let d := vectorSquaredModulus p hp x y / (x ^ 2 + y ^ 2)
    0 < d ∧ (1 - unitRoundoff p) ^ 2 ≤ d ∧ d ≤ (1 + unitRoundoff p) ^ 2 := by
  dsimp
  have hxy : 0 < x ^ 2 + y ^ 2 := by positivity
  have h := vectorSquaredModulus_bounds p hp x y
  exact ⟨div_pos (vectorSquaredModulus_pos p hp x y hy) hxy,
    (le_div_iff₀ hxy).mpr h.1, (div_le_iff₀ hxy).mpr h.2⟩

private theorem reciprocal_components (x y : ℝ) :
    (⟨x, -y⟩ : ℂ)⁻¹ = (⟨x / (x ^ 2 + y ^ 2), y / (x ^ 2 + y ^ 2)⟩ : ℂ) := by
  apply Complex.ext <;> simp [Complex.inv_re, Complex.inv_im, Complex.normSq_apply, pow_two]

/-- The rounded twist reciprocal has normwise relative error at most four unit roundoffs. -/
theorem roundedTwistReciprocal_error (p : ℕ) (hp : 2 ≤ p)
    (hω : unitRoundoff p ≤ 1 / 128) (x y : ℝ) (hy : 0 < y) :
    ‖roundedTwistReciprocal p hp x y - (⟨x, -y⟩ : ℂ)⁻¹‖ ≤
      4 * unitRoundoff p * ‖(⟨x, -y⟩ : ℂ)⁻¹‖ := by
  obtain ⟨hd, hdl, hdu⟩ := rounded_modulus_ratio p hp x y hy
  have hs : vectorSquaredModulus p hp x y ≠ 0 := (vectorSquaredModulus_pos p hp x y hy).ne'
  have hxy : x ^ 2 + y ^ 2 ≠ 0 := (show 0 < x ^ 2 + y ^ 2 by positivity).ne'
  have hcomponent (a : ℝ) :
      |roundToEven p hp (a / vectorSquaredModulus p hp x y) - a / (x ^ 2 + y ^ 2)| ≤
        4 * unitRoundoff p * |a / (x ^ 2 + y ^ 2)| := by
    obtain ⟨f, hfl, hfu, hf⟩ := rounded_factor p hp (a / vectorSquaredModulus p hp x y)
    have he := reciprocal_factor_error (unitRoundoff_pos p).le hω hd hdl hdu hfl hfu
    rw [hf, show a / vectorSquaredModulus p hp x y * f - a / (x ^ 2 + y ^ 2) =
      (f / (vectorSquaredModulus p hp x y / (x ^ 2 + y ^ 2)) - 1) *
        (a / (x ^ 2 + y ^ 2)) by field_simp, abs_mul]
    exact mul_le_mul_of_nonneg_right he (abs_nonneg _)
  rw [reciprocal_components]
  apply complex_sub_le_of_components (mul_nonneg (by norm_num) (unitRoundoff_pos p).le)
  · exact hcomponent x
  · exact hcomponent y

/-- The quotient using the original real edge has normwise relative error
at most six unit roundoffs. -/
theorem roundedEdgeQuotient_error (p : ℕ) (hp : 2 ≤ p)
    (hω : unitRoundoff p ≤ 1 / 128) (b x y : ℝ) (hy : 0 < y) :
    ‖roundedEdgeQuotient p hp b x y - (b : ℂ) / ⟨x, -y⟩‖ ≤
      6 * unitRoundoff p * ‖(b : ℂ) / ⟨x, -y⟩‖ := by
  obtain ⟨hd, hdl, hdu⟩ := rounded_modulus_ratio p hp x y hy
  have hs : vectorSquaredModulus p hp x y ≠ 0 := (vectorSquaredModulus_pos p hp x y hy).ne'
  have hxy : x ^ 2 + y ^ 2 ≠ 0 := (show 0 < x ^ 2 + y ^ 2 by positivity).ne'
  have hcomponent (a : ℝ) :
      |roundToEven p hp (roundToEven p hp (b * a) / vectorSquaredModulus p hp x y) -
        b * a / (x ^ 2 + y ^ 2)| ≤ 6 * unitRoundoff p * |b * a / (x ^ 2 + y ^ 2)| := by
    obtain ⟨f, hfl, hfu, hf⟩ := rounded_factor p hp (b * a)
    obtain ⟨g, hgl, hgu, hg⟩ :=
      rounded_factor p hp (roundToEven p hp (b * a) / vectorSquaredModulus p hp x y)
    have he := quotient_factor_error (unitRoundoff_pos p).le hω hd hdl hdu hfl hfu hgl hgu
    rw [hg, hf, show b * a * f / vectorSquaredModulus p hp x y * g -
      b * a / (x ^ 2 + y ^ 2) =
        (f * g / (vectorSquaredModulus p hp x y / (x ^ 2 + y ^ 2)) - 1) *
          (b * a / (x ^ 2 + y ^ 2)) by field_simp, abs_mul]
    exact mul_le_mul_of_nonneg_right he (abs_nonneg _)
  rw [div_eq_mul_inv, reciprocal_components]
  apply complex_sub_le_of_components (mul_nonneg (by norm_num) (unitRoundoff_pos p).le)
  · simpa [roundedEdgeQuotient, Complex.mul_re, mul_div_assoc] using hcomponent x
  · simpa [roundedEdgeQuotient, Complex.mul_im, mul_div_assoc] using hcomponent y

private theorem complex_round_components_error (p : ℕ) (hp : 2 ≤ p) (z : ℂ) :
    ‖(⟨roundToEven p hp z.re, roundToEven p hp z.im⟩ : ℂ) - z‖ ≤
      unitRoundoff p * ‖z‖ :=
  complex_sub_le_of_components (unitRoundoff_pos p).le
    (abs_roundToEven_sub_le p hp _) (abs_roundToEven_sub_le p hp _)

private theorem complex_mul_abs_components (z v : ℂ) :
    ‖(⟨|z.re * v.re| + |z.im * v.im|, |z.re * v.im| + |z.im * v.re|⟩ : ℂ)‖ ≤
      Real.sqrt 2 * ‖z * v‖ := by
  apply le_of_sq_le_sq _ (by positivity)
  rw [mul_pow, Real.sq_sqrt (by norm_num), Complex.sq_norm, Complex.normSq_apply,
    norm_mul, mul_pow, Complex.sq_norm, Complex.sq_norm,
    Complex.normSq_apply, Complex.normSq_apply]
  change (|z.re * v.re| + |z.im * v.im|) * (|z.re * v.re| + |z.im * v.im|) +
    (|z.re * v.im| + |z.im * v.re|) * (|z.re * v.im| + |z.im * v.re|) ≤
      2 * ((z.re * z.re + z.im * z.im) * (v.re * v.re + v.im * v.im))
  have h (a b : ℝ) : (|a| + |b|) * (|a| + |b|) ≤ 2 * (a ^ 2 + b ^ 2) := by
    have ha := sq_abs a
    have hb := sq_abs b
    nlinarith only [ha, hb, sq_nonneg (|a| - |b|)]
  nlinarith only [h (z.re * v.re) (z.im * v.im), h (z.re * v.im) (z.im * v.re)]

/-- The actual complex multiply has a normwise error bound valid through
cancellation in either component. -/
theorem roundedComplexProduct_error (p : ℕ) (hp : 2 ≤ p)
    (hω : unitRoundoff p ≤ 1 / 128) (z v : ℂ) :
    ‖roundedComplexProduct p hp z v - z * v‖ ≤ 3 * unitRoundoff p * (‖z‖ * ‖v‖) := by
  let ω := unitRoundoff p
  let R := roundToEven p hp
  let t : ℂ := ⟨R (z.re * v.re) - R (z.im * v.im),
    R (z.re * v.im) + R (z.im * v.re)⟩
  let c : ℂ := ⟨|z.re * v.re| + |z.im * v.im|, |z.re * v.im| + |z.im * v.re|⟩
  have hd (a b : ℝ) : |R a - R b - (a - b)| ≤ ω * (|a| + |b|) := by
    rw [show R a - R b - (a - b) = (R a - a) - (R b - b) by ring, mul_add]
    exact (abs_sub _ _).trans (add_le_add (abs_roundToEven_sub_le p hp _)
      (abs_roundToEven_sub_le p hp _))
  have ha (a b : ℝ) : |R a + R b - (a + b)| ≤ ω * (|a| + |b|) := by
    rw [show R a + R b - (a + b) = (R a - a) + (R b - b) by ring, mul_add]
    exact (abs_add_le _ _).trans (add_le_add (abs_roundToEven_sub_le p hp _)
      (abs_roundToEven_sub_le p hp _))
  have ht : ‖t - z * v‖ ≤ ω * ‖c‖ := by
    have hmk := norm_mk_le_mul (unitRoundoff_pos p).le
      ((hd (z.re * v.re) (z.im * v.im)).trans_eq
        (by rw [abs_of_nonneg (by positivity : 0 ≤ |z.re * v.re| + |z.im * v.im|)]))
      ((ha (z.re * v.im) (z.im * v.re)).trans_eq
        (by rw [abs_of_nonneg (by positivity : 0 ≤ |z.re * v.im| + |z.im * v.re|)]))
    convert hmk using 2
  have hs : ‖t‖ ≤ ‖z * v‖ + ω * ‖c‖ :=
    (by simpa [norm_sub_rev (z * v) t] using norm_le_norm_add_norm_sub (z * v) t :
      ‖t‖ ≤ ‖z * v‖ + ‖t - z * v‖).trans (add_le_add_right ht _)
  have hR : ‖roundedComplexProduct p hp z v - t‖ ≤ ω * ‖t‖ :=
    complex_round_components_error p hp t
  have hc : ‖c‖ ≤ Real.sqrt 2 * ‖z * v‖ := complex_mul_abs_components z v
  have hω₀ : 0 ≤ ω := (unitRoundoff_pos p).le
  have hw : ω ≤ 1 / 128 := hω
  have hs2 : Real.sqrt 2 ≤ (3 / 2 : ℝ) := by
    apply le_of_sq_le_sq _ (by norm_num)
    rw [Real.sq_sqrt (by norm_num)]
    norm_num
  calc
    ‖roundedComplexProduct p hp z v - z * v‖ ≤ ω * ‖t‖ + ω * ‖c‖ :=
      (by simpa only [dist_eq_norm] using dist_triangle (roundedComplexProduct p hp z v) t (z * v) : ‖roundedComplexProduct p hp z v - z * v‖ ≤ ‖roundedComplexProduct p hp z v - t‖ + ‖t - z * v‖).trans (add_le_add hR ht)
    _ ≤ ω * (‖z * v‖ + ω * ‖c‖) + ω * ‖c‖ :=
      add_le_add_left (mul_le_mul_of_nonneg_left hs hω₀) _
    _ = ω * ‖z * v‖ + ω * (1 + ω) * ‖c‖ := by ring
    _ ≤ ω * ‖z * v‖ + ω * (1 + ω) * (Real.sqrt 2 * ‖z * v‖) := by gcongr
    _ = (1 + (1 + ω) * Real.sqrt 2) * ω * ‖z * v‖ := by ring
    _ ≤ 3 * ω * (‖z‖ * ‖v‖) := by
      rw [norm_mul]
      gcongr
      calc
        _ ≤ 1 + (1 + 1 / 128) * (3 / 2 : ℝ) := by gcongr
        _ ≤ _ := by norm_num

/-- Data for one propagation step, with its edges in the input and exact
factorization and the stored pivot `pivotRe - I * pivotNegIm`. -/
structure InversePathEdge where
  original : ℝ
  absorbed : ℂ
  pivotRe : ℝ
  pivotNegIm : ℝ

/-- The stored pivot used by both path recurrences. -/
def InversePathEdge.pivot (e : InversePathEdge) : ℂ := ⟨e.pivotRe, -e.pivotNegIm⟩

/-- The original-edge computation, with exact zero across a zero edge. -/
noncomputable def roundedInverseStep (p : ℕ) (hp : 2 ≤ p) (e : InversePathEdge)
    (v : ℂ) : ℂ :=
  if e.original = 0 then 0
  else roundedComplexProduct p hp (-roundedEdgeQuotient p hp e.original e.pivotRe e.pivotNegIm) v

/-- The exact recurrence uses the absorbed edge from the structured factorization. -/
noncomputable def exactInverseStep (e : InversePathEdge) (v : ℂ) : ℂ :=
  -(e.absorbed / e.pivot) * v

/-- A list of steps is ordered from the output component back toward the twist. -/
noncomputable def roundedInversePath (p : ℕ) (hp : 2 ≤ p) (x y : ℝ) :
    List InversePathEdge → ℂ
  | [] => roundedTwistReciprocal p hp x y
  | e :: path => roundedInverseStep p hp e (roundedInversePath p hp x y path)

/-- Exact inverse column entry on the same path, starting with the exact
reciprocal of the stored twist. -/
noncomputable def exactInversePath (x y : ℝ) : List InversePathEdge → ℂ
  | [] => (⟨x, -y⟩ : ℂ)⁻¹
  | e :: path => exactInverseStep e (exactInversePath x y path)

private noncomputable def originalInverseStep (e : InversePathEdge) (v : ℂ) : ℂ :=
  -((e.original : ℂ) / e.pivot) * v

private theorem roundedInverseStep_error (p : ℕ) (hp : 2 ≤ p)
    (hω : unitRoundoff p ≤ 1 / 128) (e : InversePathEdge) (hy : 0 < e.pivotNegIm) (v : ℂ) :
    ‖roundedInverseStep p hp e v - originalInverseStep e v‖ ≤
      10 * unitRoundoff p * ‖originalInverseStep e v‖ := by
  let ω := unitRoundoff p
  let a := (e.original : ℂ) / e.pivot
  let A := roundedEdgeQuotient p hp e.original e.pivotRe e.pivotNegIm
  by_cases hz : e.original = 0
  · simp [roundedInverseStep, originalInverseStep, hz]
  rw [roundedInverseStep, if_neg hz]
  change ‖roundedComplexProduct p hp (-A) v - (-a) * v‖ ≤ 10 * ω * ‖(-a) * v‖
  have hω₀ : 0 ≤ ω := (unitRoundoff_pos p).le
  have hw : ω ≤ 1 / 128 := hω
  have h := roundedEdgeQuotient_error p hp hω e.original e.pivotRe e.pivotNegIm hy
  change ‖A - a‖ ≤ 6 * ω * ‖a‖ at h
  have hA : ‖A‖ ≤ (1 + 6 * ω) * ‖a‖ := by
    calc
      _ ≤ ‖a‖ + ‖A - a‖ := by simpa [norm_sub_rev a A] using norm_le_norm_add_norm_sub a A
      _ ≤ ‖a‖ + 6 * ω * ‖a‖ := add_le_add_right h _
      _ = _ := by ring
  have hmul : ‖(-A) * v - (-a) * v‖ ≤ 6 * ω * ‖a‖ * ‖v‖ := by
    rw [← sub_mul, norm_mul, show -A - -a = -(A - a) by ring, norm_neg]
    exact mul_le_mul_of_nonneg_right h (norm_nonneg _)
  have hcoef : 3 * ω * (1 + 6 * ω) + 6 * ω ≤ 10 * ω := by
    nlinarith [mul_nonneg hω₀ (sub_nonneg.mpr hw)]
  calc
    _ ≤ ‖roundedComplexProduct p hp (-A) v - (-A) * v‖ + ‖(-A) * v - (-a) * v‖ :=
      by simpa only [dist_eq_norm] using dist_triangle (roundedComplexProduct p hp (-A) v) ((-A) * v) ((-a) * v)
    _ ≤ 3 * ω * (‖-A‖ * ‖v‖) + 6 * ω * ‖a‖ * ‖v‖ :=
      add_le_add (roundedComplexProduct_error p hp hω (-A) v) hmul
    _ ≤ 3 * ω * (((1 + 6 * ω) * ‖a‖) * ‖v‖) + 6 * ω * ‖a‖ * ‖v‖ := by
      rw [norm_neg]
      gcongr
    _ = (3 * ω * (1 + 6 * ω) + 6 * ω) * (‖a‖ * ‖v‖) := by ring
    _ ≤ _ := by rw [norm_mul, norm_neg]; gcongr

private theorem absorbed_edge_error {ω : ℝ} (hω₀ : 0 ≤ ω) (hω : ω ≤ 1 / 128)
    (e : InversePathEdge) (he : ‖e.absorbed - (e.original : ℂ)‖ ≤
      11 * ω * ‖(e.original : ℂ)‖) :
    ‖(e.original : ℂ) - e.absorbed‖ ≤ 13 * ω * ‖e.absorbed‖ := by
  let a : ℂ := e.original
  let b := e.absorbed
  change ‖b - a‖ ≤ 11 * ω * ‖a‖ at he
  have hba := calc
    ‖a‖ ≤ ‖b‖ + ‖b - a‖ := norm_le_norm_add_norm_sub b a
    _ ≤ ‖b‖ + 11 * ω * ‖a‖ := add_le_add_right he _
  have hl : (1 - 11 * ω) * ‖a‖ ≤ ‖b‖ := by linarith
  have hcoef : 11 * ω ≤ 13 * ω * (1 - 11 * ω) := by
    nlinarith [mul_nonneg hω₀ (sub_nonneg.mpr hω)]
  rw [norm_sub_rev]
  calc
    _ ≤ 11 * ω * ‖a‖ := he
    _ ≤ (13 * ω * (1 - 11 * ω)) * ‖a‖ := mul_le_mul_of_nonneg_right hcoef (norm_nonneg _)
    _ = 13 * ω * ((1 - 11 * ω) * ‖a‖) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hl (by positivity)

private theorem originalInverseStep_error {ω : ℝ} (hω₀ : 0 ≤ ω) (hω : ω ≤ 1 / 128)
    (e : InversePathEdge) (he : ‖e.absorbed - (e.original : ℂ)‖ ≤
      11 * ω * ‖(e.original : ℂ)‖) (v : ℂ) :
    ‖originalInverseStep e v - exactInverseStep e v‖ ≤ 13 * ω * ‖exactInverseStep e v‖ := by
  have h := absorbed_edge_error hω₀ hω e he
  unfold originalInverseStep exactInverseStep
  rw [← sub_mul, show -((e.original : ℂ) / e.pivot) - -(e.absorbed / e.pivot) =
    -(((e.original : ℂ) - e.absorbed) / e.pivot) by rw [sub_div]; ring,
    norm_mul, norm_mul, norm_neg, norm_neg, norm_div, norm_div]
  calc
    _ ≤ (13 * ω * ‖e.absorbed‖ / ‖e.pivot‖) * ‖v‖ := by gcongr
    _ = _ := by ring

private theorem exists_factor_of_norm_sub_le {c : ℝ} (hc : 0 ≤ c) {a b : ℂ}
    (h : ‖b - a‖ ≤ c * ‖a‖) : ∃ ζ : ℂ, ‖ζ - 1‖ ≤ c ∧ b = a * ζ := by
  by_cases ha : a = 0
  · subst a
    simp only [sub_zero, norm_zero, mul_zero, norm_le_zero_iff] at h
    exact ⟨1, by simpa using hc, by simp [h]⟩
  refine ⟨b / a, ?_, ?_⟩
  · rw [← div_self ha, ← sub_div, norm_div]
    exact (div_le_iff₀ (norm_pos_iff.mpr ha)).mpr h
  · field_simp

private theorem mul_sub_one_radius {a b : ℂ} {A B : ℝ}
    (ha : ‖a - 1‖ ≤ A - 1) (hb : ‖b - 1‖ ≤ B - 1) :
    ‖a * b - 1‖ ≤ A * B - 1 := by
  have hB : 0 ≤ B - 1 := (norm_nonneg _).trans hb
  have hA : ‖a‖ ≤ A := by
    have h := norm_le_norm_add_norm_sub 1 a
    rw [norm_sub_rev (1 : ℂ) a, norm_one] at h
    linarith
  rw [show a * b - 1 = a * (b - 1) + (a - 1) by ring]
  calc
    _ ≤ ‖a * (b - 1)‖ + ‖a - 1‖ := norm_add_le _ _
    _ ≤ A * (B - 1) + (A - 1) := by
      rw [norm_mul]
      exact add_le_add (mul_le_mul hA hb (norm_nonneg _) ((norm_nonneg _).trans hA)) ha
    _ = _ := by ring

/-- Separate the center factor and both lists of factors along the path.
The two lists are in outward recurrence order from the output coordinate
toward the twist and have one factor per edge. -/
theorem roundedInversePath_factorization (p : ℕ) (hp : 2 ≤ p)
    (hω : unitRoundoff p ≤ 1 / 128) (x y : ℝ) (hy : 0 < y) (path : List InversePathEdge)
    (hpivot : ∀ e ∈ path, 0 < e.pivotNegIm)
    (hedge : ∀ e ∈ path, ‖e.absorbed - (e.original : ℂ)‖ ≤
      11 * unitRoundoff p * ‖(e.original : ℂ)‖) :
    ∃ (c : ℂ) (edges ops : List ℂ),
      edges.length = path.length ∧ ops.length = path.length ∧
      ‖c - 1‖ ≤ 4 * unitRoundoff p ∧
      (∀ a ∈ edges, ‖a - 1‖ ≤ 13 * unitRoundoff p) ∧
      (∀ b ∈ ops, ‖b - 1‖ ≤ 10 * unitRoundoff p) ∧
      roundedInversePath p hp x y path = exactInversePath x y path * (c * edges.prod * ops.prod) := by
  have hω₀ : 0 ≤ unitRoundoff p := (unitRoundoff_pos p).le
  induction path with
  | nil =>
    obtain ⟨c, hc, he⟩ := exists_factor_of_norm_sub_le (by positivity)
      (roundedTwistReciprocal_error p hp hω x y hy)
    exact ⟨c, [], [], rfl, rfl, hc, by simp, by simp,
      by simpa only [List.prod_nil, mul_one] using he⟩
  | cons e path ih =>
    obtain ⟨c, es, os, helen, holen, hc, he, ho, heq⟩ := ih
      (fun f hf => hpivot f (List.mem_cons_of_mem _ hf))
      (fun f hf => hedge f (List.mem_cons_of_mem _ hf))
    obtain ⟨a, ha, hax⟩ := exists_factor_of_norm_sub_le (by positivity)
      (originalInverseStep_error hω₀ hω e (hedge e (by simp)) (exactInversePath x y path))
    obtain ⟨b, hb, hbx⟩ := exists_factor_of_norm_sub_le (by positivity)
      (roundedInverseStep_error p hp hω e (hpivot e (by simp)) (roundedInversePath p hp x y path))
    have hcomm : originalInverseStep e (roundedInversePath p hp x y path) =
        originalInverseStep e (exactInversePath x y path) * (c * es.prod * os.prod) := by
      rw [heq, originalInverseStep, ← mul_assoc]
      rfl
    refine ⟨c, a :: es, b :: os, by simp [helen], by simp [holen], hc, ?_, ?_, ?_⟩
    · intro z hz
      exact (List.mem_cons.mp hz).elim (fun hz => hz ▸ ha) (he z)
    · intro z hz
      exact (List.mem_cons.mp hz).elim (fun hz => hz ▸ hb) (ho z)
    · simp only [roundedInversePath, exactInversePath, hbx, hcomm, hax, List.prod_cons]
      ring

private theorem list_prod_sub_one_radius (f : List ℂ) (u : ℝ)
    (hf : ∀ z ∈ f, ‖z - 1‖ ≤ u) :
    ‖f.prod - 1‖ ≤ (1 + u) ^ f.length - 1 := by
  induction f with
  | nil => simp
  | cons a f ih =>
    have ha : ‖a - 1‖ ≤ (1 + u) - 1 := by simpa using hf a (by simp)
    have h := mul_sub_one_radius ha (ih (fun z hz => hf z (List.mem_cons_of_mem _ hz)))
    simpa only [List.length_cons, List.prod_cons, pow_succ, mul_comm] using h

/-- The finite product has the radius from the reciprocal, edge replacement
and propagation rounding factors. -/
theorem roundedInversePath_factor (p : ℕ) (hp : 2 ≤ p) (hω : unitRoundoff p ≤ 1 / 128)
    (x y : ℝ) (hy : 0 < y) (path : List InversePathEdge)
    (hpivot : ∀ e ∈ path, 0 < e.pivotNegIm)
    (hedge : ∀ e ∈ path, ‖e.absorbed - (e.original : ℂ)‖ ≤
      11 * unitRoundoff p * ‖(e.original : ℂ)‖) :
    ∃ ζ : ℂ, roundedInversePath p hp x y path = exactInversePath x y path * ζ ∧
      ‖ζ - 1‖ ≤ (1 + 4 * unitRoundoff p) * (1 + 13 * unitRoundoff p) ^ path.length *
        (1 + 10 * unitRoundoff p) ^ path.length - 1 := by
  obtain ⟨c, es, os, helen, holen, hc, he, ho, heq⟩ :=
    roundedInversePath_factorization p hp hω x y hy path hpivot hedge
  have hc' : ‖c - 1‖ ≤ (1 + 4 * unitRoundoff p) - 1 := by simpa using hc
  refine ⟨c * es.prod * os.prod, heq, ?_⟩
  have h := mul_sub_one_radius
    (mul_sub_one_radius hc' (list_prod_sub_one_radius es _ he))
    (list_prod_sub_one_radius os _ ho)
  simpa only [helen, holen] using h

private theorem roundedInverseStep_zero (p : ℕ) (hp : 2 ≤ p) (e : InversePathEdge) :
    roundedInverseStep p hp e 0 = 0 := by
  have hz : roundToEven p hp 0 = 0 :=
    roundToEven_eq_self_of_native (native_zero p hp)
  by_cases h : e.original = 0
  · simp [roundedInverseStep, h]
  · apply Complex.ext <;> simp [roundedInverseStep, h, roundedComplexProduct, hz]

/-- An input zero edge makes the rounded component zero throughout the
rest of its outward path. -/
theorem roundedInversePath_zero_of_mem (p : ℕ) (hp : 2 ≤ p) (x y : ℝ)
    (path : List InversePathEdge) (edge : InversePathEdge)
    (hmem : edge ∈ path) (hz : edge.original = 0) :
    roundedInversePath p hp x y path = 0 := by
  induction path with
  | nil => simp at hmem
  | cons e path ih =>
    rcases List.mem_cons.mp hmem with rfl | h
    · simp [roundedInversePath, roundedInverseStep, hz]
    · rw [roundedInversePath, ih h, roundedInverseStep_zero]

/-- The imaginary component of the rounded recurrence lies in the working format. -/
theorem roundedInversePath_im_native (p : ℕ) (hp : 2 ≤ p) (x y : ℝ)
    (path : List InversePathEdge) : Native p hp (roundedInversePath p hp x y path).im := by
  cases path with
  | nil => exact roundToEven_native p hp _
  | cons e path =>
    rw [roundedInversePath, roundedInverseStep]
    split
    · exact native_zero p hp
    · exact roundToEven_native p hp _

/-- The path factor bound with the ambient dimension and the source's precision
condition. The bound includes paths with a zero original edge. -/
theorem roundedInversePath_error (n p : ℕ) (hp : 2 ≤ p) (hn : 2 ≤ n)
    (hnω : (n : ℝ) * unitRoundoff p ≤ 1 / 128)
    (x y : ℝ) (hy : 0 < y) (path : List InversePathEdge) (hpath : path.length ≤ n)
    (hpivot : ∀ e ∈ path, 0 < e.pivotNegIm)
    (hedge : ∀ e ∈ path, ‖e.absorbed - (e.original : ℂ)‖ ≤
      11 * unitRoundoff p * ‖(e.original : ℂ)‖) :
    ‖roundedInversePath p hp x y path - exactInversePath x y path‖ ≤
      64 * (n : ℝ) * unitRoundoff p * ‖exactInversePath x y path‖ := by
  let ω := unitRoundoff p
  let k := path.length
  have hω₀ : 0 < ω := unitRoundoff_pos p
  have hn₂ : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn₁ : (1 : ℝ) ≤ n := by linarith
  have hk : (k : ℝ) ≤ n := by exact_mod_cast hpath
  have hω : ω ≤ 1 / 128 := calc
    ω = 1 * ω := by ring
    _ ≤ (n : ℝ) * ω := mul_le_mul_of_nonneg_right hn₁ hω₀.le
    _ ≤ 1 / 128 := hnω
  obtain ⟨ζ, hζ, hζb⟩ := roundedInversePath_factor p hp hω x y hy path hpivot hedge
  have hscaling : 4 * ω + (k : ℝ) * (13 * ω) + (k : ℝ) * (10 * ω) ≤ 25 * (n : ℝ) * ω := by
    nlinarith only [mul_le_mul_of_nonneg_right hk hω₀.le,
      mul_le_mul_of_nonneg_right hn₂ hω₀.le]
  have hprod : (1 + 4 * ω) * (1 + 13 * ω) ^ k * (1 + 10 * ω) ^ k ≤
      Real.exp (25 * (n : ℝ) * ω) := by
    calc
      _ ≤ Real.exp (4 * ω) * Real.exp (13 * ω) ^ k * Real.exp (10 * ω) ^ k := by
        have h (a : ℝ) : 1 + a ≤ Real.exp a := by
          simpa [add_comm] using Real.add_one_le_exp a
        gcongr <;> apply h
      _ = Real.exp (4 * ω + (k : ℝ) * (13 * ω) + (k : ℝ) * (10 * ω)) := by
        rw [Real.exp_add, Real.exp_add, Real.exp_nat_mul, Real.exp_nat_mul]
      _ ≤ _ := Real.exp_le_exp.mpr hscaling
  have hsmall : 25 * (n : ℝ) * ω < 1 / 4 := by linarith
  have hpos : 0 < 25 * (n : ℝ) * ω := by positivity
  have hcap : Real.exp (25 * (n : ℝ) * ω) - 1 ≤ 64 * (n : ℝ) * ω := by
    have h := real_exp_sub_one_lt_div_one_sub_half_of_pos_of_lt_two hpos
      (show 25 * (n : ℝ) * ω < 2 by linarith)
    refine h.le.trans ((div_le_iff₀ (by linarith)).mpr ?_)
    have hden : (1 / 2 : ℝ) ≤ 1 - (25 * (n : ℝ) * ω) / 2 := by linarith
    calc
      _ ≤ 64 * (n : ℝ) * ω * (1 / 2) := by linarith
      _ ≤ _ := mul_le_mul_of_nonneg_left hden (by positivity)
  rw [hζ, show exactInversePath x y path * ζ - exactInversePath x y path =
    exactInversePath x y path * (ζ - 1) by ring, norm_mul]
  have hrel := hζb.trans ((sub_le_sub_right hprod 1).trans hcap)
  exact (mul_le_mul_of_nonneg_left hrel (norm_nonneg _)).trans_eq (mul_comm _ _)

private theorem euclidean_le_of_pointwise {ι 𝕜 𝕝 : Type*} [Fintype ι]
    [NormedAddCommGroup 𝕜] [NormedAddCommGroup 𝕝]
    (v : ι → 𝕜) (w : ι → 𝕝) (c : ℝ) (hc : 0 ≤ c) (h : ∀ i, ‖v i‖ ≤ c * ‖w i‖) :
    ‖(WithLp.toLp 2 v : PiLp 2 (fun _ : ι => 𝕜))‖ ≤ c * ‖WithLp.toLp 2 w‖ := by
  apply le_of_sq_le_sq _ (by positivity)
  rw [mul_pow, PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  change ‖v i‖ ^ 2 ≤ c ^ 2 * ‖w i‖ ^ 2
  rw [← mul_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) (h i) 2

/-- The vector error and the error after taking componentwise imaginary parts
for all paths from the selected twist. -/
theorem roundedInversePathVectors_bounds (n p : ℕ) (hp : 2 ≤ p) (hn : 2 ≤ n)
    (hnω : (n : ℝ) * unitRoundoff p ≤ 1 / 128) {u : ℝ}
    (hu : (n : ℝ) * unitRoundoff p ≤ u / 65536)
    (x y : ℝ) (hy : 0 < y) (path : Fin n → List InversePathEdge)
    (hpath : ∀ i, (path i).length ≤ n)
    (hpivot : ∀ i, ∀ e ∈ path i, 0 < e.pivotNegIm)
    (hedge : ∀ i, ∀ e ∈ path i, ‖e.absorbed - (e.original : ℂ)‖ ≤
      11 * unitRoundoff p * ‖(e.original : ℂ)‖) :
    let w : PiLp 2 (fun _ : Fin n => ℂ) :=
      WithLp.toLp 2 (fun i => exactInversePath x y (path i))
    let wHat : PiLp 2 (fun _ : Fin n => ℂ) :=
      WithLp.toLp 2 (fun i => roundedInversePath p hp x y (path i))
    let v : PiLp 2 (fun _ : Fin n => ℝ) := WithLp.toLp 2 (fun i => (w i).im)
    let vHat : PiLp 2 (fun _ : Fin n => ℝ) := WithLp.toLp 2 (fun i => (wHat i).im)
    ‖wHat - w‖ ≤ 64 * (n : ℝ) * unitRoundoff p * ‖w‖ ∧
    ‖wHat - w‖ ≤ u / 1024 * ‖w‖ ∧
    (‖w‖ ≤ 3 * ‖v‖ → ‖vHat - v‖ ≤ (3 * u / 1024) * ‖v‖) := by
  dsimp only
  let w := fun i : Fin n => exactInversePath x y (path i)
  let wHat := fun i : Fin n => roundedInversePath p hp x y (path i)
  let v := fun i : Fin n => (w i).im
  let vHat := fun i : Fin n => (wHat i).im
  let c := 64 * (n : ℝ) * unitRoundoff p
  change ‖WithLp.toLp 2 (wHat - w)‖ ≤ c * ‖WithLp.toLp 2 w‖ ∧
    ‖WithLp.toLp 2 (wHat - w)‖ ≤ u / 1024 * ‖WithLp.toLp 2 w‖ ∧
    (‖WithLp.toLp 2 w‖ ≤ 3 * ‖WithLp.toLp 2 v‖ →
      ‖WithLp.toLp 2 (vHat - v)‖ ≤ 3 * u / 1024 * ‖WithLp.toLp 2 v‖)
  have hω₀ : 0 ≤ unitRoundoff p := (unitRoundoff_pos p).le
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have h := euclidean_le_of_pointwise (wHat - w) w c hc fun i =>
    roundedInversePath_error n p hp hn hnω x y hy (path i) (hpath i) (hpivot i) (hedge i)
  have hc' : c ≤ u / 1024 := by dsimp [c]; linarith
  have hu₀ : 0 ≤ u / 1024 := hc.trans hc'
  have hw := h.trans (mul_le_mul_of_nonneg_right hc' (norm_nonneg _))
  refine ⟨h, hw, fun hphase => ?_⟩
  have him : ‖WithLp.toLp 2 (vHat - v)‖ ≤ ‖WithLp.toLp 2 (wHat - w)‖ := by
    simpa only [one_mul] using
      euclidean_le_of_pointwise (vHat - v) (wHat - w) 1 (by norm_num) (fun i => by
        simpa only [one_mul, Real.norm_eq_abs] using Complex.abs_im_le_norm (wHat i - w i))
  calc
    _ ≤ u / 1024 * ‖WithLp.toLp 2 w‖ := him.trans hw
    _ ≤ u / 1024 * (3 * ‖WithLp.toLp 2 v‖) := mul_le_mul_of_nonneg_left hphase hu₀
    _ = _ := by ring

end NumStability.CertifiedTridiagonalEigenpairs
