import ComputationalMathematics.Analysis.FloatingPointArithmetic.UnboundedBinary.Defs
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

/-!
# Unbounded binary rounding and exact radix scaling

Representation closure and nearest-even rounding laws for unrestricted binary
exponents, with exact radix scaling of represented values and rounding evidence.

These are real-value mathematical laws. They do not implement a real-to-word
conversion or establish source instruction admissibility or arithmetic work.
-/

namespace NumStability.FloatingPointFormat

noncomputable section

theorem betaR_zpow_mul_normalizedValue (fmt : FloatingPointFormat) (q : ℤ)
    (negative : Bool) (m : ℕ) (e : ℤ) :
    fmt.betaR ^ q * fmt.normalizedValue negative m e =
      fmt.normalizedValue negative m (e + q) := by
  unfold FloatingPointFormat.normalizedValue
  rw [show e + q - (fmt.t : ℤ) = q + (e - (fmt.t : ℤ)) by ring,
    zpow_add₀ (ne_of_gt fmt.betaR_pos)]
  ring

theorem unboundedNormalizedSystem_betaR_zpow_mul (fmt : FloatingPointFormat) (q : ℤ) {x : ℝ}
    (hx : fmt.unboundedNormalizedSystem x) :
    fmt.unboundedNormalizedSystem (fmt.betaR ^ q * x) := by
  rcases hx with ⟨negative, m, e, hm, hx⟩
  exact ⟨negative, m, e + q, hm, by rw [hx, betaR_zpow_mul_normalizedValue]⟩

theorem unboundedNormalizedSystem_div_betaR_zpow (fmt : FloatingPointFormat) (q : ℤ) {x : ℝ}
    (hx : fmt.unboundedNormalizedSystem x) :
    fmt.unboundedNormalizedSystem (x / fmt.betaR ^ q) := by
  have h := unboundedNormalizedSystem_betaR_zpow_mul fmt (-q) hx
  simpa only [zpow_neg, div_eq_mul_inv, mul_comm] using h

theorem realOrderAdjacentNormalized_betaR_zpow_mul (fmt : FloatingPointFormat) (q : ℤ)
    {a b : ℝ} (hab : fmt.realOrderAdjacentNormalized a b) :
    fmt.realOrderAdjacentNormalized (fmt.betaR ^ q * a) (fmt.betaR ^ q * b) := by
  let c := fmt.betaR ^ q
  have hc : 0 < c := zpow_pos fmt.betaR_pos q
  refine ⟨unboundedNormalizedSystem_betaR_zpow_mul fmt q hab.1, unboundedNormalizedSystem_betaR_zpow_mul fmt q hab.2.1, ?_, ?_⟩
  · intro heq
    exact hab.2.2.1 (mul_left_cancel₀ (ne_of_gt hc) heq)
  · intro z hz hbetween
    have hzdiv := unboundedNormalizedSystem_div_betaR_zpow fmt q hz
    apply hab.2.2.2 (z / c) hzdiv
    rcases hbetween with h | h
    · exact Or.inl ⟨(lt_div_iff₀ hc).2 (by simpa [mul_comm] using h.1),
        (div_lt_iff₀ hc).2 (by simpa [mul_comm] using h.2)⟩
    · exact Or.inr ⟨(lt_div_iff₀ hc).2 (by simpa [mul_comm] using h.1),
        (div_lt_iff₀ hc).2 (by simpa [mul_comm] using h.2)⟩

/-- Positive scaling preserves both distance comparisons and the unchanged
mantissa parity, including exact ties. -/
theorem nearestAdjacentRoundToEven_pos_mul (c : ℝ) (hc : 0 < c)
    (x a b : ℝ) (m : ℕ) :
    FloatingPointFormat.nearestAdjacentRoundToEven (c * x) (c * a) (c * b) m =
      c * FloatingPointFormat.nearestAdjacentRoundToEven x a b m := by
  unfold FloatingPointFormat.nearestAdjacentRoundToEven
  simp only [← mul_sub, abs_mul, abs_of_pos hc, mul_lt_mul_iff_right₀ hc]
  split_ifs <;> rfl

/-- Complete transport of actual concrete RNE evidence. The same mantissa
and its parity are retained; only every exponent is shifted by q. -/
theorem sourceRoundToEvenEvidence_betaR_zpow_mul (fmt : FloatingPointFormat) (q : ℤ)
    {x y : ℝ} (h : fmt.sourceRoundToEvenEvidence x y) :
    fmt.sourceRoundToEvenEvidence (fmt.betaR ^ q * x) (fmt.betaR ^ q * y) := by
  let c := fmt.betaR ^ q
  have hc : 0 < c := zpow_pos fmt.betaR_pos q
  have power_hi (e : ℤ) : fmt.betaR ^ (e + q) = c * fmt.betaR ^ e := by
    dsimp [c]
    rw [← zpow_add₀ (ne_of_gt fmt.betaR_pos)]
    congr 1
    ring
  have power_lo (e : ℤ) : fmt.betaR ^ (e + q - 1) = c * fmt.betaR ^ (e - 1) := by
    dsimp [c]
    rw [← zpow_add₀ (ne_of_gt fmt.betaR_pos)]
    congr 1
    ring
  rcases h with hpos | hneg
  · rcases hpos with ⟨e, hlo, hhi, hexact | hbracket⟩
    · left
      refine ⟨e + q, ?_, ?_, Or.inl ?_⟩
      · rw [power_lo]
        exact mul_le_mul_of_nonneg_left hlo hc.le
      · rw [power_hi]
        exact mul_le_mul_of_nonneg_left hhi hc.le
      · rcases hexact with ⟨m, hm, hx, hy⟩
        exact ⟨m, hm, by rw [hx, betaR_zpow_mul_normalizedValue], by rw [hy]⟩
    · left
      refine ⟨e + q, ?_, ?_, Or.inr ?_⟩
      · rw [power_lo]
        exact mul_le_mul_of_nonneg_left hlo hc.le
      · rw [power_hi]
        exact mul_le_mul_of_nonneg_left hhi hc.le
      · rcases hbracket with ⟨a, b, m, hadj, hleft, ha0, hax, hxb, hy⟩
        refine ⟨c * a, c * b, m, realOrderAdjacentNormalized_betaR_zpow_mul fmt q hadj, ?_,
          mul_nonneg hc.le ha0, mul_le_mul_of_nonneg_left hax hc.le,
          mul_le_mul_of_nonneg_left hxb hc.le, ?_⟩
        · rcases hleft with ⟨negative, eLeft, hm, ha⟩
          exact ⟨negative, eLeft + q, hm, by rw [ha, betaR_zpow_mul_normalizedValue]⟩
        · rw [hy, nearestAdjacentRoundToEven_pos_mul c hc]
  · rcases hneg with ⟨e, hlo, hhi, hexact | hbracket⟩
    · right
      refine ⟨e + q, ?_, ?_, Or.inl ?_⟩
      · calc
          -(fmt.betaR ^ (e + q)) = c * (-(fmt.betaR ^ e)) := by
            rw [power_hi, mul_neg]
          _ ≤ c * x := mul_le_mul_of_nonneg_left hlo hc.le
      · calc
          c * x ≤ c * (-(fmt.betaR ^ (e - 1))) :=
            mul_le_mul_of_nonneg_left hhi hc.le
          _ = -(fmt.betaR ^ (e + q - 1)) := by rw [power_lo, mul_neg]
      · rcases hexact with ⟨m, hm, hx, hy⟩
        exact ⟨m, hm, by rw [hx, betaR_zpow_mul_normalizedValue], by rw [hy]⟩
    · right
      refine ⟨e + q, ?_, ?_, Or.inr ?_⟩
      · calc
          -(fmt.betaR ^ (e + q)) = c * (-(fmt.betaR ^ e)) := by
            rw [power_hi, mul_neg]
          _ ≤ c * x := mul_le_mul_of_nonneg_left hlo hc.le
      · calc
          c * x ≤ c * (-(fmt.betaR ^ (e - 1))) :=
            mul_le_mul_of_nonneg_left hhi hc.le
          _ = -(fmt.betaR ^ (e + q - 1)) := by rw [power_lo, mul_neg]
      · rcases hbracket with ⟨a, b, m, hadj, hleft, hb0, hax, hxb, hy⟩
        refine ⟨c * a, c * b, m, realOrderAdjacentNormalized_betaR_zpow_mul fmt q hadj, ?_,
          mul_nonpos_of_nonneg_of_nonpos hc.le hb0,
          mul_le_mul_of_nonneg_left hax hc.le,
          mul_le_mul_of_nonneg_left hxb hc.le, ?_⟩
        · rcases hleft with ⟨negative, eLeft, hm, ha⟩
          exact ⟨negative, eLeft + q, hm, by rw [ha, betaR_zpow_mul_normalizedValue]⟩
        · rw [hy, nearestAdjacentRoundToEven_pos_mul c hc]

end

end NumStability.FloatingPointFormat

namespace NumStability.FloatingPointFormat.UnboundedBinary

noncomputable section

private theorem exists_even_nonzero (fmt : FloatingPointFormat) (x : ℝ)
    (hx : x ≠ 0) : ∃ y, fmt.sourceRoundToEvenEvidence x y := by
  rcases lt_trichotomy x 0 with hneg | hzero | hpos
  · obtain ⟨y, δ, _hnear, _hδ, _hwit, hpolicy⟩ :=
      fmt.exists_nearestAdjacentRoundToEven_signedRelErrorWitness_lt_negative hneg
    exact ⟨y, hpolicy⟩
  · exact False.elim (hx hzero)
  · obtain ⟨y, δ, _hnear, _hδ, _hwit, hpolicy⟩ :=
      fmt.exists_nearestAdjacentRoundToEven_signedRelErrorWitness_lt_positive hpos
    exact ⟨y, hpolicy⟩

open FloatingPointFormat.UnboundedBinary in
theorem roundToEven_policy_of_ne_zero (p : ℕ) (hp : 2 ≤ p) {x : ℝ}
    (hx : x ≠ 0) :
    (format p hp).sourceRoundToEvenEvidence x (roundToEven p hp x) := by
  have hex := exists_even_nonzero (format p hp) x hx
  simpa only [roundToEven, if_neg hx] using Classical.epsilon_spec hex

open FloatingPointFormat.UnboundedBinary in
/-- All real inputs, every integer scale exponent, including negative powers.
No native-input or finite exponent-range restriction has been added. -/
theorem roundToEven_zpow_mul (p : ℕ) (hp : 2 ≤ p) (q : ℤ) (x : ℝ) :
    roundToEven p hp ((2 : ℝ) ^ q * x) =
      (2 : ℝ) ^ q * roundToEven p hp x := by
  by_cases hx : x = 0
  · simp [hx, roundToEven]
  · have hc : (2 : ℝ) ^ q ≠ 0 := ne_of_gt (zpow_pos (by norm_num) q)
    have hscaled : (2 : ℝ) ^ q * x ≠ 0 := mul_ne_zero hc hx
    exact FloatingPointFormat.sourceRoundToEvenEvidence_unique
      (roundToEven_policy_of_ne_zero p hp hscaled)
      (sourceRoundToEvenEvidence_betaR_zpow_mul (format p hp) q
        (roundToEven_policy_of_ne_zero p hp hx))


/-- Existing concrete global nearest/even witnesses, combined only by sign. -/
private theorem exists_even_witness (fmt : FloatingPointFormat) (x : ℝ)
    (hx : x ≠ 0) :
    ∃ y δ : ℝ,
      fmt.nearestRoundingToUnbounded x y ∧
      |δ| < fmt.unitRoundoff ∧ signedRelErrorWitness y x δ ∧
      fmt.sourceRoundToEvenEvidence x y := by
  rcases lt_trichotomy x 0 with hneg | hzero | hpos
  · exact fmt.exists_nearestAdjacentRoundToEven_signedRelErrorWitness_lt_negative hneg
  · exact False.elim (hx hzero)
  · exact fmt.exists_nearestAdjacentRoundToEven_signedRelErrorWitness_lt_positive hpos


theorem format_unitRoundoff (p : ℕ) (hp : 2 ≤ p) :
    (format p hp).unitRoundoff = unitRoundoff p := by
  change (1 / 2 : ℝ) * (2 : ℝ) ^ (1 - (p : ℤ)) =
    (2 : ℝ) ^ (-(p : ℤ))
  rw [sub_eq_add_neg, zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
  norm_num
  ring

theorem unitRoundoff_pos (p : ℕ) : 0 < unitRoundoff p := by
  exact zpow_pos (by norm_num : (0 : ℝ) < 2) _

theorem unitRoundoff_le_quarter (p : ℕ) (hp : 2 ≤ p) :
    unitRoundoff p ≤ (1 / 4 : ℝ) := by
  have hpZ : (2 : ℤ) ≤ (p : ℤ) := by exact_mod_cast hp
  calc
    unitRoundoff p = (2 : ℝ) ^ (-(p : ℤ)) := rfl
    _ ≤ (2 : ℝ) ^ (-2 : ℤ) :=
      zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (neg_le_neg hpZ)
    _ = (1 / 4 : ℝ) := by norm_num

theorem native_zero (p : ℕ) (hp : 2 ≤ p) : Native p hp 0 :=
  Or.inl rfl

theorem native_neg {p : ℕ} {hp : 2 ≤ p} {x : ℝ}
    (hx : Native p hp x) : Native p hp (-x) := by
  rcases hx with rfl | hx
  · exact Or.inl (neg_zero)
  · exact Or.inr (FloatingPointFormat.unboundedNormalizedSystem_neg hx)

theorem native_zpow (p : ℕ) (hp : 2 ≤ p) (k : ℤ) :
    Native p hp ((2 : ℝ) ^ k) := by
  let fmt := format p hp
  right
  refine ⟨false, fmt.minNormalMantissa, k + 1,
    fmt.minNormalMantissa_normalized, ?_⟩
  rw [fmt.normalizedValue_false_minNormalMantissa_eq]
  change (2 : ℝ) ^ k = (2 : ℝ) ^ (k + 1 - 1)
  congr 1
  ring

theorem native_one (p : ℕ) (hp : 2 ≤ p) : Native p hp 1 := by
  simpa using native_zpow p hp (0 : ℤ)

theorem native_two (p : ℕ) (hp : 2 ≤ p) : Native p hp 2 := by
  simpa using native_zpow p hp (1 : ℤ)

theorem native_unitRoundoff (p : ℕ) (hp : 2 ≤ p) :
    Native p hp (unitRoundoff p) :=
  native_zpow p hp (-(p : ℤ))

theorem native_mul_zpow {p : ℕ} {hp : 2 ≤ p} {x : ℝ}
    (hx : Native p hp x) (k : ℤ) :
    Native p hp (x * (2 : ℝ) ^ k) := by
  rcases hx with rfl | ⟨negative, m, e, hm, hx⟩
  · exact Or.inl (zero_mul _)
  · right
    refine ⟨negative, m, e + k, hm, ?_⟩
    rw [hx]
    change
      ((if negative then (-1 : ℝ) else 1) * (m : ℝ) *
        (2 : ℝ) ^ (e - (p : ℤ))) * (2 : ℝ) ^ k =
      (if negative then (-1 : ℝ) else 1) * (m : ℝ) *
        (2 : ℝ) ^ ((e + k) - (p : ℤ))
    rw [show (e + k) - (p : ℤ) = (e - (p : ℤ)) + k by ring,
      zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
    ring

@[simp] theorem roundToEven_zero (p : ℕ) (hp : 2 ≤ p) : roundToEven p hp 0 = 0 := by
  simp [roundToEven]

theorem roundToEven_spec_of_ne_zero (p : ℕ) (hp : 2 ≤ p) {x : ℝ} (hx : x ≠ 0) :
    ∃ δ : ℝ,
      (format p hp).nearestRoundingToUnbounded x (roundToEven p hp x) ∧
      |δ| < unitRoundoff p ∧ signedRelErrorWitness (roundToEven p hp x) x δ ∧
      (format p hp).sourceRoundToEvenEvidence x (roundToEven p hp x) := by
  obtain ⟨y, δ, hnear, hδ, hwit, hpolicy⟩ :=
    exists_even_witness (format p hp) x hx
  have heq : roundToEven p hp x = y :=
    FloatingPointFormat.sourceRoundToEvenEvidence_unique
      (roundToEven_policy_of_ne_zero p hp hx) hpolicy
  simp only [heq]
  exact ⟨δ, hnear, by simpa only [format_unitRoundoff] using hδ, hwit, hpolicy⟩

theorem roundToEven_nearestRoundingToUnbounded_of_ne_zero (p : ℕ) (hp : 2 ≤ p) {x : ℝ} (hx : x ≠ 0) :
    (format p hp).nearestRoundingToUnbounded x (roundToEven p hp x) := by
  obtain ⟨δ, hnear, _hδ, _hwit, _hpolicy⟩ := roundToEven_spec_of_ne_zero p hp hx
  exact hnear

theorem roundToEven_native (p : ℕ) (hp : 2 ≤ p) (x : ℝ) :
    Native p hp (roundToEven p hp x) := by
  by_cases hx : x = 0
  · simpa [hx] using native_zero p hp
  · exact Or.inr (roundToEven_nearestRoundingToUnbounded_of_ne_zero p hp hx).1

theorem roundToEven_eq_self_of_native {p : ℕ} {hp : 2 ≤ p} {x : ℝ}
    (hx : Native p hp x) : roundToEven p hp x = x := by
  rcases hx with rfl | hx
  · exact roundToEven_zero p hp
  · exact FloatingPointFormat.nearestRoundingToUnbounded_eq_self_of_mem hx
      (roundToEven_nearestRoundingToUnbounded_of_ne_zero p hp
        (FloatingPointFormat.unboundedNormalizedSystem_ne_zero hx))

/-- The bound holds for every exact real input, including exact zero. -/
theorem roundToEven_signedRelErrorWitness (p : ℕ) (hp : 2 ≤ p) (x : ℝ) :
    ∃ δ : ℝ, |δ| ≤ unitRoundoff p ∧
      signedRelErrorWitness (roundToEven p hp x) x δ := by
  by_cases hx : x = 0
  · subst x
    refine ⟨0, ?_, ?_⟩
    · simpa using (unitRoundoff_pos p).le
    · simp [signedRelErrorWitness]
  · obtain ⟨δ, _hnear, hδ, hwit, _hpolicy⟩ := roundToEven_spec_of_ne_zero p hp hx
    exact ⟨δ, hδ.le, hwit⟩

theorem abs_roundToEven_sub_le (p : ℕ) (hp : 2 ≤ p) (x : ℝ) :
    |roundToEven p hp x - x| ≤ unitRoundoff p * |x| := by
  obtain ⟨δ, hδ, hwit⟩ := roundToEven_signedRelErrorWitness p hp x
  have hdiff : roundToEven p hp x - x = x * δ := by
    unfold signedRelErrorWitness at hwit
    rw [hwit]
    ring
  rw [hdiff, abs_mul]
  calc
    |x| * |δ| ≤ |x| * unitRoundoff p :=
      mul_le_mul_of_nonneg_left hδ (abs_nonneg x)
    _ = unitRoundoff p * |x| := mul_comm _ _

/-- Adding zero to G does not change the selected nonzero nearest result. -/
theorem roundToEven_nearestRoundingIn (p : ℕ) (hp : 2 ≤ p) (x : ℝ) :
    FloatingPointFormat.nearestRoundingIn (Native p hp) x (roundToEven p hp x) := by
  by_cases hx : x = 0
  · subst x
    rw [roundToEven_zero]
    exact FloatingPointFormat.nearestRoundingIn_self (native_zero p hp)
  · refine ⟨roundToEven_native p hp x, ?_⟩
    intro z hz
    rcases hz with rfl | hz
    · have hu : unitRoundoff p ≤ 1 :=
        (unitRoundoff_le_quarter p hp).trans (by norm_num)
      calc
        |x - roundToEven p hp x| = |roundToEven p hp x - x| := abs_sub_comm _ _
        _ ≤ unitRoundoff p * |x| := abs_roundToEven_sub_le p hp x
        _ ≤ 1 * |x| := mul_le_mul_of_nonneg_right hu (abs_nonneg x)
        _ = |x - 0| := by simp
    · exact (roundToEven_nearestRoundingToUnbounded_of_ne_zero p hp hx).2 z hz

/-- Same generic nearest-point midpoint argument as the existing finite API;
here the candidate set is the actual unbounded binary Native set. -/
theorem roundToEven_monotone (p : ℕ) (hp : 2 ≤ p) : Monotone (roundToEven p hp) := by
  intro x y hxy
  by_cases hEq : x = y
  · subst y
    exact le_rfl
  have hxy_lt : x < y := lt_of_le_of_ne hxy hEq
  let a := roundToEven p hp x
  let b := roundToEven p hp y
  have hxround : FloatingPointFormat.nearestRoundingIn (Native p hp) x a :=
    roundToEven_nearestRoundingIn p hp x
  have hyround : FloatingPointFormat.nearestRoundingIn (Native p hp) y b :=
    roundToEven_nearestRoundingIn p hp y
  by_contra hnot
  have hba : b < a := lt_of_not_ge hnot
  have hxnear : |x - a| ≤ |x - b| := hxround.2 b hyround.1
  have hynear : |y - b| ≤ |y - a| := hyround.2 a hxround.1
  have hxsq : (x - a) ^ 2 ≤ (x - b) ^ 2 := (sq_le_sq).2 hxnear
  have hysq : (y - b) ^ 2 ≤ (y - a) ^ 2 := (sq_le_sq).2 hynear
  have hprod : 0 < (a - b) * (y - x) :=
    mul_pos (sub_pos.mpr hba) (sub_pos.mpr hxy_lt)
  nlinarith

theorem roundToEven_neg (p : ℕ) (hp : 2 ≤ p) (x : ℝ) :
    roundToEven p hp (-x) = -roundToEven p hp x := by
  by_cases hx : x = 0
  · simp [hx]
  · obtain ⟨δ, _hnear, _hδ, _hwit, hpolicy⟩ := roundToEven_spec_of_ne_zero p hp hx
    obtain ⟨δneg, _hnearneg, _hδneg, _hwitneg, hpolicyneg⟩ :=
      roundToEven_spec_of_ne_zero p hp (neg_ne_zero.mpr hx)
    have hbeta : FloatingPointFormat.evenMantissa (format p hp).beta := by
      norm_num [FloatingPointFormat.evenMantissa, format]
    have ht : 1 < (format p hp).t := by
      change 1 < p
      exact lt_of_lt_of_le (by decide : 1 < 2) hp
    exact FloatingPointFormat.sourceRoundToEvenEvidence_unique hpolicyneg
      (FloatingPointFormat.sourceRoundToEvenEvidence_neg hbeta ht hpolicy)

theorem native_roundToEven_div_two (p : ℕ) (hp : 2 ≤ p) (x : ℝ) :
    Native p hp (roundToEven p hp x / 2) := by
  simpa [div_eq_mul_inv] using
    native_mul_zpow (roundToEven_native p hp x) (-1 : ℤ)

theorem roundToEven_roundToEven_div_two (p : ℕ) (hp : 2 ≤ p) (x : ℝ) :
    roundToEven p hp (roundToEven p hp x / 2) = roundToEven p hp x / 2 :=
  roundToEven_eq_self_of_native (native_roundToEven_div_two p hp x)

theorem abs_roundToEven_div_sub_one_le (p : ℕ) (hp : 2 ≤ p) (x : ℝ) (hx : x ≠ 0) :
    |roundToEven p hp x / x - 1| ≤ unitRoundoff p := by
  obtain ⟨δ, hδ, hwit⟩ := roundToEven_signedRelErrorWitness p hp x
  have hquot : roundToEven p hp x / x - 1 = δ := by
    unfold signedRelErrorWitness at hwit
    rw [hwit]
    field_simp [hx]
    ring
  rw [hquot]
  exact hδ

theorem abs_roundToEven_sub_le_of_abs_le (p : ℕ) (hp : 2 ≤ p) (x M : ℝ)
    (hM : |x| ≤ M) :
    |roundToEven p hp x - x| ≤ unitRoundoff p * M := by
  exact (abs_roundToEven_sub_le p hp x).trans
    (mul_le_mul_of_nonneg_left hM (unitRoundoff_pos p).le)

theorem roundToEven_pos (p : ℕ) (hp : 2 ≤ p) (x : ℝ) (hx : 0 < x) :
    0 < roundToEven p hp x := by
  obtain ⟨δ, hδ, hwit⟩ := roundToEven_signedRelErrorWitness p hp x
  have hlo : -unitRoundoff p ≤ δ := (abs_le.mp hδ).1
  have hu := unitRoundoff_le_quarter p hp
  have hfactor : 0 < 1 + δ := by linarith
  unfold signedRelErrorWitness at hwit
  rw [hwit]
  exact mul_pos hx hfactor

theorem roundToEven_neg_of_neg (p : ℕ) (hp : 2 ≤ p) (x : ℝ) (hx : x < 0) :
    roundToEven p hp x < 0 := by
  obtain ⟨δ, hδ, hwit⟩ := roundToEven_signedRelErrorWitness p hp x
  have hlo : -unitRoundoff p ≤ δ := (abs_le.mp hδ).1
  have hu := unitRoundoff_le_quarter p hp
  have hfactor : 0 < 1 + δ := by linarith
  unfold signedRelErrorWitness at hwit
  rw [hwit]
  exact mul_neg_of_neg_of_pos hx hfactor

theorem roundToEven_mul_zpow (p : ℕ) (hp : 2 ≤ p) (x : ℝ) (k : ℤ) :
    roundToEven p hp (x * (2 : ℝ) ^ k) =
      roundToEven p hp x * (2 : ℝ) ^ k := by
  simpa only [mul_comm] using roundToEven_zpow_mul p hp k x

end

end NumStability.FloatingPointFormat.UnboundedBinary
