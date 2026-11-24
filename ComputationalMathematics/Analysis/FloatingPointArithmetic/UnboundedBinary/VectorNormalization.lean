import ComputationalMathematics.Analysis.FloatingPointArithmetic.UnboundedBinary.ScalarOperations
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Vector normalization in unbounded binary arithmetic

Round each square and sum from left to right. Round the square root and each
componentwise quotient, then convert each component to the output precision.
The Euclidean error bounds apply to the values represented by these words.
-/

open scoped BigOperators
open WithLp

namespace NumStability.FloatingPointFormat.UnboundedBinary.Word

variable {n q : ℕ} {hq : 2 ≤ q}

/-- The vector of real values represented by a family of binary words. -/
noncomputable def euclidean (x : Fin n → Word q hq) : EuclideanSpace ℝ (Fin n) :=
  toLp 2 fun i => (x i).value

@[simp] theorem euclidean_apply (x : Fin n → Word q hq) (i : Fin n) :
    euclidean x i = (x i).value := rfl

private noncomputable def square (x : Word q hq) : Word q hq :=
  (ScalarOperation.mul x x).eval

/-- Left-to-right rounded summation, using the first term to initialize the
accumulator. The addition to exact zero can be omitted for a native term. -/
noncomputable def sumNative : {n : ℕ} → (Fin n → Word q hq) → Word q hq
  | 0, _ => .zero
  | 1, x => x 0
  | k + 2, x =>
    (ScalarOperation.add (sumNative (x ∘ Fin.castSucc)) (x (Fin.last (k + 1)))).eval

/-- Round the exact squares of an arbitrary real vector, then sum those words. -/
noncomputable def sumSquaresOfReal (q : ℕ) (hq : 2 ≤ q) (x : Fin n → ℝ) : Word q hq :=
  sumNative fun i => round q hq (x i ^ 2)

/-- Compute the squared norm of a word vector with rounded squares and additions. -/
noncomputable def sumSquares (x : Fin n → Word q hq) : Word q hq :=
  sumNative fun i => square (x i)

private theorem abs_round_bound (x : ℝ) :
    |roundToEven q hq x - x| ≤ unitRoundoff q * |x| :=
  abs_roundToEven_sub_le q hq x

private theorem round_enclosure {x : ℝ} (hx : 0 ≤ x) :
    (1 - unitRoundoff q) * x ≤ roundToEven q hq x ∧
      roundToEven q hq x ≤ (1 + unitRoundoff q) * x := by
  have h := abs_round_bound (hq := hq) x
  rw [abs_of_nonneg hx, abs_le] at h
  constructor <;> linarith [h.1, h.2]

private theorem sumSquaresOfReal_enclosure_sum (x : Fin n → ℝ) :
    (1 - unitRoundoff q)^n * (∑ i, x i ^ 2) ≤ (sumSquaresOfReal q hq x).value ∧
      (sumSquaresOfReal q hq x).value ≤ (1 + unitRoundoff q)^n * (∑ i, x i ^ 2) := by
  let w := unitRoundoff q
  have hw := unitRoundoff_pos q
  have hquarter := unitRoundoff_le_quarter q hq
  have hlo : 0 ≤ 1 - w := by dsimp [w]; linarith
  have hhi : 0 ≤ 1 + w := by dsimp [w]; linarith
  induction n with
  | zero => simp [sumSquaresOfReal, sumNative, value]
  | succ k ih =>
    cases k with
    | zero =>
      simpa [sumSquaresOfReal, sumNative, Fin.sum_univ_one] using
        round_enclosure (hq := hq) (sq_nonneg (x 0))
    | succ k =>
      let s := ∑ i : Fin (k + 1), x i.castSucc ^ 2
      let t := x (Fin.last (k + 1)) ^ 2
      let r := (sumSquaresOfReal q hq (x ∘ Fin.castSucc)).value
      let a := (round q hq t).value
      have hs : 0 ≤ s := Finset.sum_nonneg fun _ _ => sq_nonneg _
      have ht : 0 ≤ t := sq_nonneg _
      have hr : (1 - w)^(k + 1) * s ≤ r ∧ r ≤ (1 + w)^(k + 1) * s := ih _
      have ha : (1 - w) * t ≤ a ∧ a ≤ (1 + w) * t := by simp only [a, value_round]; exact round_enclosure ht
      have hr' : 0 ≤ r := (mul_nonneg (pow_nonneg hlo _) hs).trans hr.1
      have ha' : 0 ≤ a := (mul_nonneg hlo ht).trans ha.1
      have hround := round_enclosure (hq := hq) (add_nonneg hr' ha')
      have hlow : (1 - w)^(k + 1) * t ≤ a := by
        refine (mul_le_mul_of_nonneg_right ?_ ht).trans ha.1
        exact pow_le_of_le_one hlo (by dsimp [w]; linarith) (Nat.succ_ne_zero _)
      have hhigh : a ≤ (1 + w)^(k + 1) * t := by
        refine ha.2.trans (mul_le_mul_of_nonneg_right ?_ ht)
        exact le_self_pow₀ (by dsimp [w]; linarith) (Nat.succ_ne_zero _)
      rw [Fin.sum_univ_castSucc]
      change (1 - w)^(k + 2) * (s + t) ≤ (round q hq (r + a)).value ∧
        (round q hq (r + a)).value ≤ (1 + w)^(k + 2) * (s + t)
      rw [value_round]
      constructor
      · refine le_trans ?_ hround.1
        rw [pow_succ, mul_comm ((1 - w) ^ (k + 1)), mul_assoc]
        exact mul_le_mul_of_nonneg_left (by rw [mul_add]; exact add_le_add hr.1 hlow) hlo
      · refine hround.2.trans ?_
        rw [pow_succ, mul_comm ((1 + w) ^ (k + 1)), mul_assoc]
        exact mul_le_mul_of_nonneg_left (by rw [mul_add]; exact add_le_add hr.2 hhigh) hhi

/-- The rounded squares and sequential sum enclose the squared Euclidean norm
of every real vector, including zero. -/
theorem sumSquaresOfReal_enclosure (x : Fin n → ℝ) :
    (1 - unitRoundoff q)^n * ‖(toLp 2 x : EuclideanSpace ℝ (Fin n))‖ ^ 2 ≤
      (sumSquaresOfReal q hq x).value ∧
    (sumSquaresOfReal q hq x).value ≤
      (1 + unitRoundoff q)^n * ‖(toLp 2 x : EuclideanSpace ℝ (Fin n))‖ ^ 2 := by
  simpa only [EuclideanSpace.norm_sq_eq, ofLp_toLp, Real.norm_eq_abs, sq_abs] using
    sumSquaresOfReal_enclosure_sum (hq := hq) x

theorem sumSquares_eq_sumSquaresOfReal (x : Fin n → Word q hq) :
    sumSquares x = sumSquaresOfReal q hq (fun i => (x i).value) := by
  unfold sumSquares sumSquaresOfReal
  congr 1
  funext i
  change round q hq ((x i).value * (x i).value) = round q hq ((x i).value ^ 2)
  rw [pow_two]

/-- Enclosure for the computed sum of squares in terms of the exact squared
norm. There are at most `n` rounding factors on each summand. -/
theorem sumSquares_enclosure (x : Fin n → Word q hq) :
    (1 - unitRoundoff q)^n * ‖euclidean x‖ ^ 2 ≤ (sumSquares x).value ∧
      (sumSquares x).value ≤ (1 + unitRoundoff q)^n * ‖euclidean x‖ ^ 2 := by
  rw [sumSquares_eq_sumSquaresOfReal]
  exact sumSquaresOfReal_enclosure (fun i => (x i).value)

theorem sumSquares_nonneg (x : Fin n → Word q hq) : 0 ≤ (sumSquares x).value := by
  have hw := unitRoundoff_le_quarter q hq
  exact (mul_nonneg (pow_nonneg (by linarith) _) (sq_nonneg _)).trans
    (sumSquares_enclosure x).1

theorem sumSquares_pos (x : Fin n → Word q hq) (hx : euclidean x ≠ 0) :
    0 < (sumSquares x).value := by
  have hw := unitRoundoff_le_quarter q hq
  exact (mul_pos (pow_pos (by linarith) _) (pow_pos (norm_pos_iff.mpr hx) _)).trans_le
    (sumSquares_enclosure x).1

/-- The rounded square root of the computed sum of squares. -/
noncomputable def roundedNorm (x : Fin n → Word q hq) : Word q hq :=
  (ScalarOperation.sqrt (sumSquares x) (sumSquares_nonneg x)).eval

theorem roundedNorm_pos (x : Fin n → Word q hq) (hx : euclidean x ≠ 0) :
    0 < (roundedNorm x).value := by
  change 0 < (round q hq (Real.sqrt (sumSquares x).value)).value
  rw [value_round]
  exact roundToEven_pos _ _ _ (Real.sqrt_pos.2 (sumSquares_pos x hx))

/-- Normalize a nonzero word vector at its working precision. -/
noncomputable def normalize (x : Fin n → Word q hq) (hx : euclidean x ≠ 0) :
    Fin n → Word q hq :=
  let d := roundedNorm x
  fun i => (ScalarOperation.div (x i) d (roundedNorm_pos x hx).ne').eval

/-- Normalize at working precision and round each quotient to precision `p`. -/
noncomputable def normalizeTo (p : ℕ) (hp : 2 ≤ p)
    (x : Fin n → Word q hq) (hx : euclidean x ≠ 0) : Fin n → Word p hp :=
  let y := normalize x hx
  fun i => (y i).convert p hp

theorem euclidean_round_of_native (y : Fin n → ℝ) (hy : ∀ i, Native q hq (y i)) :
    euclidean (fun i => round q hq (y i)) = toLp 2 y := by
  ext i
  exact (value_round q hq (y i)).trans (roundToEven_eq_self_of_native (hy i))

/-- Enclosure for the computed norm, with the square roots of the accumulated
multiplicative factors and one further factor for rounding the square root. -/
theorem roundedNorm_ratio_enclosure (x : Fin n → Word q hq) (hx : euclidean x ≠ 0) :
    (1 - unitRoundoff q) * Real.sqrt ((1 - unitRoundoff q)^n) ≤
      (roundedNorm x).value / ‖euclidean x‖ ∧
    (roundedNorm x).value / ‖euclidean x‖ ≤
      (1 + unitRoundoff q) * Real.sqrt ((1 + unitRoundoff q)^n) := by
  have hw := unitRoundoff_pos q
  have hwq := unitRoundoff_le_quarter q hq
  have hlo : 0 ≤ 1 - unitRoundoff q := by linarith
  have hhi : 0 ≤ 1 + unitRoundoff q := by linarith
  have hz := norm_pos_iff.mpr hx
  have hs := sumSquares_enclosure x
  have hl := Real.sqrt_le_sqrt hs.1
  have hu := Real.sqrt_le_sqrt hs.2
  rw [Real.sqrt_mul (pow_nonneg hlo _), Real.sqrt_sq hz.le] at hl
  rw [Real.sqrt_mul (pow_nonneg hhi _), Real.sqrt_sq hz.le] at hu
  have hr := round_enclosure (hq := hq) (Real.sqrt_nonneg (sumSquares x).value)
  change _ ≤ (round q hq (Real.sqrt (sumSquares x).value)).value / _ ∧
    (round q hq (Real.sqrt (sumSquares x).value)).value / _ ≤ _
  rw [value_round, le_div_iff₀ hz, div_le_iff₀ hz]
  constructor
  · refine le_trans ?_ hr.1
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left hl hlo
  · refine hr.2.trans ?_
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left hu hhi

private theorem sqrt_rounding_factors {w : ℝ} (hw : 0 ≤ w) (hw1 : w ≤ 1)
    (n : ℕ) (ha : (n : ℝ) * w ≤ 1 / 128) :
    1 - n * w ≤ Real.sqrt ((1 - w)^n) ∧
      Real.sqrt ((1 + w)^n) ≤ 1 + n * w := by
  let a := (n : ℝ) * w
  have ha0 : 0 ≤ a := by dsimp [a]; positivity
  have ha1 : 0 ≤ 1 - a := by dsimp [a]; linarith
  have hl : 1 - a ≤ (1 - w)^n := by
    simpa only [a, mul_neg, ← sub_eq_add_neg] using
      (one_add_mul_le_pow (show -2 ≤ -w by linarith) n)
  have hprod : (1 + w)^n * (1 - w)^n ≤ 1 := by
    rw [← mul_pow]
    apply pow_le_one₀ (mul_nonneg (by linarith) (by linarith))
    nlinarith [sq_nonneg w]
  have hu : (1 + w)^n * (1 - a) ≤ 1 :=
    (mul_le_mul_of_nonneg_left hl (pow_nonneg (by linarith) _)).trans hprod
  constructor
  · apply (Real.le_sqrt ha1 (pow_nonneg (by linarith) _)).mpr
    exact (sq_le ha1 (by linarith)).trans hl
  · refine Real.sqrt_le_iff.mpr ⟨by linarith, ?_⟩
    have ha2 : a ≤ (1 / 128 : ℝ) := ha
    have hupper : 1 ≤ (1 + a)^2 * (1 - a) := by
      have hsq := sq_le ha0 (show a ≤ 1 by linarith)
      nlinarith [mul_nonneg ha0 (show 0 ≤ 1 - a - a^2 by linarith)]
    exact le_of_mul_le_mul_right (hu.trans hupper) (by linarith)

private theorem roundedNorm_ratio_error (x : Fin n → Word q hq) (hx : euclidean x ≠ 0)
    (hn : 1 ≤ n) (hb : (n : ℝ) * unitRoundoff q ≤ 1 / 128) :
    let a := (n : ℝ) * unitRoundoff q
    let r := (roundedNorm x).value / ‖euclidean x‖
    |r - 1| ≤ 9 / 4 * a ∧ 7 / 8 ≤ r := by
  dsimp only
  let w := unitRoundoff q
  let a := (n : ℝ) * w
  let r := (roundedNorm x).value / ‖euclidean x‖
  change |r - 1| ≤ 9 / 4 * a ∧ 7 / 8 ≤ r
  have hw : 0 ≤ w := (unitRoundoff_pos q).le
  have hwq : w ≤ 1 / 4 := unitRoundoff_le_quarter q hq
  have hwa : w ≤ a := le_mul_of_one_le_left hw (by exact_mod_cast hn)
  have ha : a ≤ 1 / 128 := hb
  have ha0 : 0 ≤ a := hw.trans hwa
  have hf := sqrt_rounding_factors hw (by linarith) n hb
  have hr : (1 - w) * Real.sqrt ((1 - w)^n) ≤ r ∧
      r ≤ (1 + w) * Real.sqrt ((1 + w)^n) := roundedNorm_ratio_enclosure x hx
  have hlo : (1 - w) * (1 - a) ≤ r :=
    (mul_le_mul_of_nonneg_left hf.1 (by linarith)).trans hr.1
  have hhi : r ≤ (1 + w) * (1 + a) :=
    hr.2.trans (mul_le_mul_of_nonneg_left hf.2 (by linarith))
  have hmul₀ : 0 ≤ w * a := mul_nonneg hw ha0
  have hmul₁ : w * a ≤ a / 4 := by linarith [mul_le_mul_of_nonneg_right hwq ha0]
  exact ⟨abs_le.mpr ⟨by nlinarith, by nlinarith⟩, by nlinarith⟩

private theorem norm_le_mul_of_abs_apply_le {x y : EuclideanSpace ℝ (Fin n)} {c : ℝ}
    (hc : 0 ≤ c) (h : ∀ i, |x i| ≤ c * |y i|) :
    ‖x‖ ≤ c * ‖y‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hc (norm_nonneg _))).mp
  rw [mul_pow, EuclideanSpace.norm_sq_eq x, EuclideanSpace.norm_sq_eq y, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [← mul_pow]
  exact (sq_le_sq₀ (abs_nonneg _) (mul_nonneg hc (abs_nonneg _))).mpr (h i)

private theorem norm_exact_normalize {x : EuclideanSpace ℝ (Fin n)} (hx : x ≠ 0) :
    ‖‖x‖⁻¹ • x‖ = 1 := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg x)),
    inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx)]

/-- Euclidean normalization error before converting the result to the output
precision. The bound also holds in dimension one. -/
theorem normalize_error (x : Fin n → Word q hq) (hx : euclidean x ≠ 0)
    (hn : 1 ≤ n) (hb : (n : ℝ) * unitRoundoff q ≤ 1 / 128) :
    ‖euclidean (normalize x hx) - ‖euclidean x‖⁻¹ • euclidean x‖ ≤
      4 * n * unitRoundoff q := by
  let a := (n : ℝ) * unitRoundoff q
  let r := (roundedNorm x).value / ‖euclidean x‖
  have ha : 0 ≤ a := mul_nonneg (Nat.cast_nonneg _) (unitRoundoff_pos q).le
  have hqa : unitRoundoff q ≤ a :=
    le_mul_of_one_le_left (unitRoundoff_pos q).le (by exact_mod_cast hn)
  have hr : |r - 1| ≤ 9 / 4 * a ∧ 7 / 8 ≤ r := roundedNorm_ratio_error x hx hn hb
  have hrpos : 0 < r := by linarith [hr.2]
  have hz := norm_ne_zero_iff.mpr hx
  have hd := (roundedNorm_pos x hx).ne'
  let y := ‖euclidean x‖⁻¹ • euclidean x
  have hc : ∀ i, |(euclidean (normalize x hx) - y) i| ≤ (4 * a) * |y i| := by
    intro i
    obtain ⟨δ, hδ, hvalue⟩ :=
      roundToEven_signedRelErrorWitness q hq ((x i).value / (roundedNorm x).value)
    have hfactor : |(1 + δ - r) / r| ≤ 4 * a := by
      rw [abs_div, abs_of_pos hrpos, div_le_iff₀ hrpos]
      calc
        |1 + δ - r| = |δ - (r - 1)| := by congr 1; ring
        _ ≤ |δ| + |r - 1| := abs_sub _ _
        _ ≤ 4 * a * r := by
          have hmul := mul_le_mul_of_nonneg_left hr.2 (show 0 ≤ 4 * a by positivity)
          linarith [hr.1, hδ.trans hqa]
    change |(round q hq ((x i).value / (roundedNorm x).value)).value -
      ‖euclidean x‖⁻¹ * (x i).value| ≤ (4 * a) * |y i|
    rw [value_round]
    change _ = _ * (1 + δ) at hvalue
    rw [hvalue]
    have heq : (x i).value / (roundedNorm x).value * (1 + δ) -
        ‖euclidean x‖⁻¹ * (x i).value = ((1 + δ - r) / r) * y i := by
      change _ = ((1 + δ - ((roundedNorm x).value / ‖euclidean x‖)) /
        ((roundedNorm x).value / ‖euclidean x‖)) * (‖euclidean x‖⁻¹ * (x i).value)
      field_simp
    rw [heq, abs_mul]
    exact mul_le_mul_of_nonneg_right hfactor (abs_nonneg _)
  simpa only [y, norm_exact_normalize hx, mul_one, a, ← mul_assoc] using
    norm_le_mul_of_abs_apply_le (show 0 ≤ 4 * a by positivity) hc

/-- Euclidean error of componentwise nearest-even conversion. -/
theorem euclidean_convert_error (p : ℕ) (hp : 2 ≤ p) (x : Fin n → Word q hq) :
    ‖euclidean (fun i => (x i).convert p hp) - euclidean x‖ ≤ unitRoundoff p * ‖euclidean x‖ := by
  refine norm_le_mul_of_abs_apply_le (unitRoundoff_pos p).le fun i => ?_
  change |(round p hp (x i).value).value - (x i).value| ≤ unitRoundoff p * |(x i).value|
  rw [value_round]
  exact abs_roundToEven_sub_le p hp _

/-- Perturbation of exact normalization in a real normed space. -/
theorem exact_normalization_sub_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {x z : E} (hx : x ≠ 0) (hz : z ≠ 0) :
    ‖‖x‖⁻¹ • x - ‖z‖⁻¹ • z‖ ≤ 2 * ‖x - z‖ / ‖z‖ := by
  have hx' := norm_pos_iff.mpr hx
  have hz' := norm_pos_iff.mpr hz
  have hdiff : ‖‖x‖⁻¹ • x - ‖z‖⁻¹ • x‖ ≤ ‖x - z‖ / ‖z‖ := by
    rw [← sub_smul, norm_smul, Real.norm_eq_abs]
    have hfield : (‖x‖⁻¹ - ‖z‖⁻¹) * ‖x‖ = (‖z‖ - ‖x‖) / ‖z‖ := by
      field_simp
    calc
      |‖x‖⁻¹ - ‖z‖⁻¹| * ‖x‖ = |(‖x‖⁻¹ - ‖z‖⁻¹) * ‖x‖| := by
        rw [abs_mul, abs_of_nonneg hx'.le]
      _ = |‖z‖ - ‖x‖| / ‖z‖ := by rw [hfield, abs_div, abs_of_pos hz']
      _ ≤ ‖x - z‖ / ‖z‖ := by
        exact div_le_div_of_nonneg_right
          ((abs_norm_sub_norm_le z x).trans_eq (norm_sub_rev z x)) hz'.le
  have hrest : ‖‖z‖⁻¹ • x - ‖z‖⁻¹ • z‖ = ‖x - z‖ / ‖z‖ := by
    rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr hz'.le),
      div_eq_inv_mul]
  calc
    _ ≤ ‖‖x‖⁻¹ • x - ‖z‖⁻¹ • x‖ + ‖‖z‖⁻¹ • x - ‖z‖⁻¹ • z‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ _ := by rw [mul_div_assoc]; linarith [hdiff, hrest]

/-- The actual output at precision `p`, compared to the exact normalization
of a nonzero reference vector. -/
theorem normalizeTo_error (p : ℕ) (hp : 2 ≤ p) (x : Fin n → Word q hq)
    (hx : euclidean x ≠ 0) {z : EuclideanSpace ℝ (Fin n)} (hz : z ≠ 0)
    (hn : 1 ≤ n) (hb : (n : ℝ) * unitRoundoff q ≤ 1 / 128) :
    ‖euclidean (normalizeTo p hp x hx) - ‖z‖⁻¹ • z‖ ≤
      2 * ‖euclidean x - z‖ / ‖z‖ + 4 * n * unitRoundoff q +
        unitRoundoff p * (1 + 4 * n * unitRoundoff q) := by
  let v := euclidean (normalize x hx)
  let y := ‖euclidean x‖⁻¹ • euclidean x
  have hwork : ‖v - y‖ ≤ 4 * n * unitRoundoff q := normalize_error x hx hn hb
  have hv : ‖v‖ ≤ 1 + 4 * n * unitRoundoff q := by
    have hnorm : ‖y‖ = 1 := norm_exact_normalize hx
    have htri := norm_le_norm_sub_add v y
    linarith
  have hout : ‖euclidean (normalizeTo p hp x hx) - v‖ ≤
      unitRoundoff p * (1 + 4 * n * unitRoundoff q) :=
    (euclidean_convert_error p hp (normalize x hx)).trans
      (mul_le_mul_of_nonneg_left hv (unitRoundoff_pos p).le)
  have href : ‖y - ‖z‖⁻¹ • z‖ ≤ _ := exact_normalization_sub_le hx hz
  calc
    _ ≤ ‖euclidean (normalizeTo p hp x hx) - v‖ + ‖v - ‖z‖⁻¹ • z‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ _ := by linarith [norm_sub_le_norm_sub_add_norm_sub v y (‖z‖⁻¹ • z)]

end NumStability.FloatingPointFormat.UnboundedBinary.Word
