import ComputationalMathematics.Analysis.FloatingPointArithmetic.UnboundedBinary.Basic
import Mathlib.Data.Real.Sqrt

/-!
# Rounded Sturm pivots with a positive clipping threshold

The shifted diagonal, square, quotient, and final subtraction use separate
nearest-even operations. An entire pivot is replaced by the positive threshold
when its magnitude is below that threshold. Relative rounding factors from the
square, division, and final subtraction are absorbed into the adjacent
off-diagonal of an exact tridiagonal recurrence.
-/

namespace NumStability.FloatingPointFormat.UnboundedBinary

noncomputable section

/-- The clipping threshold for target accuracy `2⁻ʳ`. -/
def sturmClipThreshold (r : ℕ) : ℝ := unitRoundoff r / 16

theorem sturmClipThreshold_pos (r : ℕ) : 0 < sturmClipThreshold r :=
  div_pos (unitRoundoff_pos r) (by norm_num)

theorem sturmClipThreshold_eq_zpow (r : ℕ) :
    sturmClipThreshold r = (2 : ℝ) ^ (-(r : ℤ) + (-4)) := by
  rw [zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
  norm_num [sturmClipThreshold, unitRoundoff, div_eq_mul_inv]

theorem sturmClipThreshold_native (q : ℕ) (hq : 2 ≤ q) (r : ℕ) :
    Native q hq (sturmClipThreshold r) := by
  rw [sturmClipThreshold_eq_zpow]
  exact native_zpow q hq _

/-- Eight extra significand bits make the roundoff at most `2⁻ʳ / 256`. -/
theorem sturm_unitRoundoff_le {r q : ℕ} (hq : r + 8 ≤ q) :
    unitRoundoff q ≤ unitRoundoff r / 256 := by
  have hneg : -(q : ℤ) ≤ -(r : ℤ) + (-8) := by omega
  unfold unitRoundoff
  calc
    (2 : ℝ) ^ (-(q : ℤ)) ≤ (2 : ℝ) ^ (-(r : ℤ) + (-8)) :=
      zpow_le_zpow_right₀ (by norm_num) hneg
    _ = (2 : ℝ) ^ (-(r : ℤ)) / 256 := by
      rw [zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
      norm_num [div_eq_mul_inv]

/-- The sum of the diagonal and two edge budgets is below a quarter of the
requested eigenvalue enclosure margin. -/
theorem sturmBackwardError_lt {r q : ℕ} (hq : r + 8 ≤ q) :
    13 * unitRoundoff q + 2 * sturmClipThreshold r < unitRoundoff r / 4 := by
  have hw := sturm_unitRoundoff_le hq
  have hr := unitRoundoff_pos r
  unfold sturmClipThreshold
  linarith

/-- Keep raw pivots of magnitude at least `s`, and replace smaller ones by `s`. -/
def clipSturmPivot (s raw : ℝ) : ℝ := if s ≤ |raw| then raw else s

theorem le_abs_clipSturmPivot {s : ℝ} (hs : 0 ≤ s) (raw : ℝ) :
    s ≤ |clipSturmPivot s raw| := by
  by_cases h : s ≤ |raw|
  · simp [clipSturmPivot, h]
  · simp [clipSturmPivot, h, abs_of_nonneg hs]

theorem abs_clipSturmPivot_sub_lt {s : ℝ} (hs : 0 < s) (raw : ℝ) :
    |clipSturmPivot s raw - raw| < 2 * s := by
  by_cases h : s ≤ |raw|
  · simp [clipSturmPivot, h, hs]
  · rw [clipSturmPivot, if_neg h]
    exact (abs_sub _ _).trans_lt (by rw [abs_of_pos hs]; linarith [lt_of_not_ge h])

theorem clipSturmPivot_native {q : ℕ} {hq : 2 ≤ q} {s raw : ℝ}
    (hs : Native q hq s) (hraw : Native q hq raw) :
    Native q hq (clipSturmPivot s raw) := by
  unfold clipSturmPivot
  split <;> assumption

/-- The first pivot is a single rounded shifted diagonal, followed by clipping. -/
def clippedSturmFirst (q : ℕ) (hq : 2 ≤ q) (s a x : ℝ) : ℝ :=
  clipSturmPivot s (roundToEven q hq (a - x))

/-- The four rounded operations for a subsequent raw Sturm pivot. -/
def clippedSturmRaw (q : ℕ) (hq : 2 ≤ q) (a b x prev : ℝ) : ℝ :=
  let c := roundToEven q hq (a - x)
  let z := roundToEven q hq (b ^ 2)
  let v := roundToEven q hq (z / prev)
  roundToEven q hq (c - v)

/-- Clip the newly computed raw pivot before counting it or using it as a divisor. -/
def clippedSturmStep (q : ℕ) (hq : 2 ≤ q) (s a b x prev : ℝ) : ℝ :=
  clipSturmPivot s (clippedSturmRaw q hq a b x prev)

private theorem abs_two_roundingFactors_sub_one_le {u α δ : ℝ}
    (hu0 : 0 ≤ u) (hu : u ≤ 1 / 4) (hα : |α| ≤ u) (hδ : |δ| ≤ u) :
    |(1 + α) * (1 + δ) - 1| ≤ (9 / 4) * u := by
  have hprod : |α * δ| ≤ u ^ 2 := by
    rw [abs_mul, pow_two]
    exact mul_le_mul hα hδ (abs_nonneg _) hu0
  calc
    |(1 + α) * (1 + δ) - 1| = |(α + δ) + α * δ| := by congr 1; ring
    _ ≤ (|α| + |δ|) + |α * δ| :=
      (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ u + u + u ^ 2 := add_le_add (add_le_add hα hδ) hprod
    _ ≤ (9 / 4) * u := by nlinarith [mul_nonneg hu0 (sub_nonneg.mpr hu)]

private theorem abs_sqrt_roundingFactorProduct_sub_one_le
    {u β γ δ : ℝ} (hu0 : 0 ≤ u) (hu : u ≤ 1 / 4)
    (hβ : |β| ≤ u) (hγ : |γ| ≤ u) (hδ : |δ| ≤ u) :
    |Real.sqrt ((1 + β) * (1 + γ) * (1 + δ)) - 1| ≤ 2 * u := by
  have hβ0 : 0 ≤ 1 + β := by linarith [(abs_le.mp hβ).1]
  have hγ0 : 0 ≤ 1 + γ := by linarith [(abs_le.mp hγ).1]
  have hδ0 : 0 ≤ 1 + δ := by linarith [(abs_le.mp hδ).1]
  have hlow0 : 0 ≤ 1 - u := by linarith
  have hupp0 : 0 ≤ 1 + u := by linarith
  have hlow : (1 - u) ^ 3 ≤ (1 + β) * (1 + γ) * (1 + δ) := by
    rw [pow_succ, pow_two]
    exact mul_le_mul
      (mul_le_mul (by linarith [(abs_le.mp hβ).1]) (by linarith [(abs_le.mp hγ).1])
        hlow0 hβ0)
      (by linarith [(abs_le.mp hδ).1]) hlow0 (mul_nonneg hβ0 hγ0)
  have hupp : (1 + β) * (1 + γ) * (1 + δ) ≤ (1 + u) ^ 3 := by
    rw [pow_succ, pow_two]
    exact mul_le_mul
      (mul_le_mul (by linarith [(abs_le.mp hβ).2]) (by linarith [(abs_le.mp hγ).2])
        hγ0 hupp0)
      (by linarith [(abs_le.mp hδ).2]) hδ0 (mul_nonneg hupp0 hupp0)
  have hu2 : u ^ 2 ≤ u / 4 := by nlinarith [mul_nonneg hu0 (sub_nonneg.mpr hu)]
  have hgaplow : 0 ≤ 1 - u - u ^ 2 := by linarith
  have hgapupp : 0 ≤ 1 + u - u ^ 2 := by linarith
  have hslo : 1 - 2 * u ≤ Real.sqrt ((1 + β) * (1 + γ) * (1 + δ)) :=
    Real.le_sqrt_of_sq_le (by nlinarith [mul_nonneg hu0 hgaplow])
  have hshi : Real.sqrt ((1 + β) * (1 + γ) * (1 + δ)) ≤ 1 + 2 * u :=
    (Real.sqrt_le_left (by linarith)).2 (by nlinarith [mul_nonneg hu0 hgapupp])
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- A first-pivot witness using only shifted-diagonal rounding and clipping. -/
theorem clippedSturmFirst_backwardWitness (q : ℕ) (hq : 2 ≤ q) {s a x : ℝ}
    (hs : 0 < s) (ha : |a - x| ≤ 4) :
    ∃ a' : ℝ, |a' - a| ≤ 9 * unitRoundoff q + 2 * s ∧
      clippedSturmFirst q hq s a x = a' - x := by
  let raw := roundToEven q hq (a - x)
  let d := clipSturmPivot s raw
  have hround : |raw - (a - x)| ≤ 4 * unitRoundoff q := by
    calc
      |raw - (a - x)| ≤ unitRoundoff q * |a - x| :=
        abs_roundToEven_sub_le q hq (a - x)
      _ ≤ unitRoundoff q * 4 := mul_le_mul_of_nonneg_left ha (unitRoundoff_pos q).le
      _ = 4 * unitRoundoff q := mul_comm _ _
  refine ⟨x + d, ?_, by change d = x + d - x; ring⟩
  calc
    |x + d - a| = |(d - raw) + (raw - (a - x))| := by congr 1; ring
    _ ≤ |d - raw| + |raw - (a - x)| := abs_add_le _ _
    _ ≤ 2 * s + 4 * unitRoundoff q :=
      add_le_add (abs_clipSturmPivot_sub_lt hs raw).le hround
    _ ≤ 9 * unitRoundoff q + 2 * s := by linarith [unitRoundoff_pos q]

/-- A subsequent clipped pivot is exact for a perturbed shifted diagonal and
adjacent off-diagonal. The off-diagonal witness absorbs relative rounding of
the square, quotient, and final subtraction independently of the size of `prev`. -/
theorem clippedSturmStep_backwardWitness (q : ℕ) (hq : 2 ≤ q)
    {s a b x prev : ℝ} (hs : 0 < s) (ha : |a - x| ≤ 4) (hb : |b| ≤ 1) :
    ∃ a' b' : ℝ, |a' - a| ≤ 9 * unitRoundoff q + 2 * s ∧
      |b' - b| ≤ 2 * unitRoundoff q ∧
      clippedSturmStep q hq s a b x prev = a' - x - b' ^ 2 / prev := by
  let u := unitRoundoff q
  let R := roundToEven q hq
  let raw := clippedSturmRaw q hq a b x prev
  obtain ⟨α, hα, hαR⟩ := roundToEven_signedRelErrorWitness q hq (a - x)
  obtain ⟨β, hβ, hβR⟩ := roundToEven_signedRelErrorWitness q hq (b ^ 2)
  obtain ⟨γ, hγ, hγR⟩ := roundToEven_signedRelErrorWitness q hq (R (b ^ 2) / prev)
  obtain ⟨δ, hδ, hδR⟩ := roundToEven_signedRelErrorWitness q hq
    (R (a - x) - R (R (b ^ 2) / prev))
  unfold signedRelErrorWitness at hαR hβR hγR hδR
  let product := (1 + β) * (1 + γ) * (1 + δ)
  have hu0 : 0 ≤ u := (unitRoundoff_pos q).le
  have hu : u ≤ 1 / 4 := unitRoundoff_le_quarter q hq
  have hβ0 : 0 < 1 + β := by linarith [(abs_le.mp hβ).1]
  have hγ0 : 0 < 1 + γ := by linarith [(abs_le.mp hγ).1]
  have hδ0 : 0 < 1 + δ := by linarith [(abs_le.mp hδ).1]
  have hproduct : 0 < product := mul_pos (mul_pos hβ0 hγ0) hδ0
  have hsqrt : |Real.sqrt product - 1| ≤ 2 * u :=
    abs_sqrt_roundingFactorProduct_sub_one_le hu0 hu hβ hγ hδ
  let b' := b * Real.sqrt product
  have hb'sq : b' ^ 2 = b ^ 2 * product := by
    dsimp [b']
    rw [mul_pow, Real.sq_sqrt hproduct.le]
  have hb' : |b' - b| ≤ 2 * u := by
    calc
      |b' - b| = |b| * |Real.sqrt product - 1| := by
        rw [← abs_mul]
        congr 1
        dsimp [b']
        ring
      _ ≤ 1 * (2 * u) := mul_le_mul hb hsqrt (abs_nonneg _) (by norm_num)
      _ = 2 * u := one_mul _
  have hraw : raw = (a - x) * (1 + α) * (1 + δ) - b ^ 2 * product / prev := by
    dsimp [raw, clippedSturmRaw, R] at *
    rw [hδR, hγR, hβR, hαR]
    dsimp [product]
    simp only [div_eq_mul_inv]
    ring
  let e := clipSturmPivot s raw - raw
  let a' := x + (a - x) * (1 + α) * (1 + δ) + e
  have hfactors : |(1 + α) * (1 + δ) - 1| ≤ (9 / 4) * u :=
    abs_two_roundingFactors_sub_one_le hu0 hu hα hδ
  have ha' : |a' - a| ≤ 9 * u + 2 * s := by
    calc
      |a' - a| = |(a - x) * ((1 + α) * (1 + δ) - 1) + e| := by
        congr 1
        dsimp [a']
        ring
      _ ≤ |a - x| * |(1 + α) * (1 + δ) - 1| + |e| := by
        rw [← abs_mul]
        exact abs_add_le _ _
      _ ≤ 4 * ((9 / 4) * u) + 2 * s :=
        add_le_add (mul_le_mul ha hfactors (abs_nonneg _) (by norm_num))
          (abs_clipSturmPivot_sub_lt hs raw).le
      _ = 9 * u + 2 * s := by ring
  refine ⟨a', b', ha', hb', ?_⟩
  change clipSturmPivot s raw = a' - x - b' ^ 2 / prev
  rw [hb'sq]
  dsimp [a', e]
  rw [hraw]
  ring

/-- All stored pivots of the clipped recurrence, with the edge `i` joining
rows `i.castSucc` and `i.succ`. -/
def clippedSturmPivots {n : ℕ} (q : ℕ) (hq : 2 ≤ q) (r : ℕ)
    (a : Fin (n + 1) → ℝ) (b : Fin n → ℝ) (x : ℝ) : Fin (n + 1) → ℝ :=
  Fin.induction (motive := fun _ => ℝ)
    (clippedSturmFirst q hq (sturmClipThreshold r) (a 0) x)
    (fun i prev => clippedSturmStep q hq (sturmClipThreshold r) (a i.succ) (b i) x prev)

@[simp] theorem clippedSturmPivots_zero {n q r : ℕ} {hq : 2 ≤ q}
    (a : Fin (n + 1) → ℝ) (b : Fin n → ℝ) (x : ℝ) :
    clippedSturmPivots q hq r a b x 0 = clippedSturmFirst q hq (sturmClipThreshold r) (a 0) x := by
  unfold clippedSturmPivots
  exact Fin.induction_zero _ _

@[simp] theorem clippedSturmPivots_succ {n q r : ℕ} {hq : 2 ≤ q}
    (a : Fin (n + 1) → ℝ) (b : Fin n → ℝ) (x : ℝ) (i : Fin n) :
    clippedSturmPivots q hq r a b x i.succ =
      clippedSturmStep q hq (sturmClipThreshold r) (a i.succ) (b i) x
        (clippedSturmPivots q hq r a b x i.castSucc) := by
  unfold clippedSturmPivots
  exact Fin.induction_succ _ _ _

theorem sturmClipThreshold_le_abs_pivots {n q r : ℕ} {hq : 2 ≤ q}
    (a : Fin (n + 1) → ℝ) (b : Fin n → ℝ) (x : ℝ) (i : Fin (n + 1)) :
    sturmClipThreshold r ≤ |clippedSturmPivots q hq r a b x i| := by
  refine Fin.cases ?_ (fun j => ?_) i
  · rw [clippedSturmPivots_zero, clippedSturmFirst]
    exact le_abs_clipSturmPivot (sturmClipThreshold_pos r).le _
  · rw [clippedSturmPivots_succ, clippedSturmStep]
    exact le_abs_clipSturmPivot (sturmClipThreshold_pos r).le _

theorem clippedSturmPivots_ne_zero {n q r : ℕ} {hq : 2 ≤ q}
    (a : Fin (n + 1) → ℝ) (b : Fin n → ℝ) (x : ℝ) (i : Fin (n + 1)) :
    clippedSturmPivots q hq r a b x i ≠ 0 := by
  intro h
  have hbound := sturmClipThreshold_le_abs_pivots (q := q) (hq := hq) (r := r) a b x i
  rw [h, abs_zero] at hbound
  exact (sturmClipThreshold_pos r).not_ge hbound

theorem clippedSturmPivots_native {n q r : ℕ} {hq : 2 ≤ q}
    (a : Fin (n + 1) → ℝ) (b : Fin n → ℝ) (x : ℝ) (i : Fin (n + 1)) :
    Native q hq (clippedSturmPivots q hq r a b x i) := by
  refine Fin.cases ?_ (fun j => ?_) i
  · rw [clippedSturmPivots_zero, clippedSturmFirst]
    exact clipSturmPivot_native (sturmClipThreshold_native q hq r) (roundToEven_native q hq _)
  · rw [clippedSturmPivots_succ, clippedSturmStep, clippedSturmRaw]
    exact clipSturmPivot_native (sturmClipThreshold_native q hq r) (roundToEven_native q hq _)

/-- The complete rounded recurrence is the exact recurrence for perturbed
coordinates, with uniform bounds on the diagonal and adjacent edges. -/
theorem clippedSturmPivots_backwardWitness {n : ℕ} (q : ℕ) (hq : 2 ≤ q) (r : ℕ)
    (a : Fin (n + 1) → ℝ) (b : Fin n → ℝ) (x : ℝ)
    (ha : ∀ i, |a i - x| ≤ 4) (hb : ∀ i, |b i| ≤ 1) :
    let d := clippedSturmPivots q hq r a b x
    ∃ (a' : Fin (n + 1) → ℝ) (b' : Fin n → ℝ),
      (∀ i, |a' i - a i| ≤ 9 * unitRoundoff q + 2 * sturmClipThreshold r) ∧
      (∀ i, |b' i - b i| ≤ 2 * unitRoundoff q) ∧
      d 0 = a' 0 - x ∧
      (∀ i : Fin n, d i.succ = a' i.succ - x - (b' i) ^ 2 / d i.castSucc) := by
  let s := sturmClipThreshold r
  have hs : 0 < s := sturmClipThreshold_pos r
  let d := clippedSturmPivots q hq r a b x
  obtain ⟨first, hfirst, hfirst_eq⟩ := clippedSturmFirst_backwardWitness q hq hs (ha 0)
  have hsteps (i : Fin n) :=
    clippedSturmStep_backwardWitness q hq (prev := d i.castSucc) hs (ha i.succ) (hb i)
  choose aNext b' hdiag hoff hstep_eq using hsteps
  refine ⟨Fin.cons first aNext, b', ?_, hoff, ?_, ?_⟩
  · intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa only [Fin.cons_zero] using hfirst
    · simpa only [Fin.cons_succ] using hdiag j
  · simpa only [Fin.cons_zero, clippedSturmPivots_zero] using hfirst_eq
  · intro i
    simpa only [Fin.cons_succ, clippedSturmPivots_succ] using hstep_eq i

end
end NumStability.FloatingPointFormat.UnboundedBinary
