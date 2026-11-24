import ComputationalMathematics.Analysis.FloatingPointArithmetic.UnboundedBinary.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Tactic.Positivity

/-!
# Exact small integer words in unbounded binary arithmetic

Natural and signed integer denotations with bounded magnitude are native values.
The counter below performs one actual nearest-even addition per step. Its
natural-number argument is an index; its state is a real denotation of a native
numerical word. These laws use no finite exponent bounds or wider arithmetic.
They do not assert an implementation or a work bound for integer conversion.
-/

namespace NumStability.FloatingPointFormat.UnboundedBinary

noncomputable section

/-- Every nonnegative integer below `2^p` is exactly representable, including zero. -/
theorem native_natCast_of_lt_two_pow (p : ℕ) (hp : 2 ≤ p) {m : ℕ}
    (hm : m < 2 ^ p) : Native p hp (m : ℝ) := by
  by_cases hm0 : m = 0
  · subst m
    simpa using native_zero p hp
  let q := Nat.log 2 m
  let shift := p - 1 - q
  have hq : q < p := Nat.log_lt_of_lt_pow hm0 hm
  have hsum : q + shift = p - 1 := by dsimp [shift]; omega
  have hsum' : (q + 1) + shift = p := by omega
  have hlo : 2 ^ (p - 1) ≤ m * 2 ^ shift := by
    rw [← hsum, pow_add]
    exact Nat.mul_le_mul_right _ (Nat.pow_log_le_self 2 hm0)
  have hhi : m * 2 ^ shift < 2 ^ p := by
    rw [← hsum', pow_add]
    exact Nat.mul_lt_mul_of_pos_right (Nat.lt_pow_succ_log_self (by decide) m)
      (by positivity)
  right
  refine ⟨false, m * 2 ^ shift, (p : ℤ) - (shift : ℤ), ⟨hlo, hhi⟩, ?_⟩
  change (m : ℝ) = (format p hp).normalizedValue false
    (m * (format p hp).beta ^ shift) ((p : ℤ) - (shift : ℤ))
  rw [FloatingPointFormat.normalizedValue_mul_beta_pow_subExponent_eq]
  simp [FloatingPointFormat.normalizedValue, FloatingPointFormat.signValue, format]

/-- The smaller bound used for the coefficient counters in native polar evaluation. -/
theorem native_natCast_of_lt_two_pow_pred (p : ℕ) (hp : 2 ≤ p) {m : ℕ}
    (hm : m < 2 ^ (p - 1)) : Native p hp (m : ℝ) := by
  apply native_natCast_of_lt_two_pow p hp
  exact hm.trans_le (Nat.pow_le_pow_right (by decide) (Nat.sub_le _ _))

/-- Signed integer words are exact whenever their natural magnitude is below `2^p`. -/
theorem native_intCast_of_natAbs_lt_two_pow (p : ℕ) (hp : 2 ≤ p) {z : ℤ}
    (hz : z.natAbs < 2 ^ p) : Native p hp (z : ℝ) := by
  cases z with
  | ofNat n => exact native_natCast_of_lt_two_pow p hp hz
  | negSucc n =>
      simpa using native_neg (native_natCast_of_lt_two_pow p hp hz)

theorem native_intCast_of_natAbs_lt_two_pow_pred (p : ℕ) (hp : 2 ≤ p) {z : ℤ}
    (hz : z.natAbs < 2 ^ (p - 1)) : Native p hp (z : ℝ) := by
  apply native_intCast_of_natAbs_lt_two_pow p hp
  exact hz.trans_le (Nat.pow_le_pow_right (by decide) (Nat.sub_le _ _))

theorem roundToEven_natCast_of_lt_two_pow (p : ℕ) (hp : 2 ≤ p) {m : ℕ}
    (hm : m < 2 ^ p) : roundToEven p hp (m : ℝ) = (m : ℝ) :=
  roundToEven_eq_self_of_native (native_natCast_of_lt_two_pow p hp hm)

theorem roundToEven_intCast_of_natAbs_lt_two_pow (p : ℕ) (hp : 2 ≤ p) {z : ℤ}
    (hz : z.natAbs < 2 ^ p) : roundToEven p hp (z : ℝ) = (z : ℝ) :=
  roundToEven_eq_self_of_native (native_intCast_of_natAbs_lt_two_pow p hp hz)

/-- One rounded addition of two is exact if the resulting integer is in range. -/
theorem roundToEven_natCast_add_two (p : ℕ) (hp : 2 ≤ p) {m : ℕ}
    (hm : m + 2 < 2 ^ p) :
    roundToEven p hp ((m : ℝ) + 2) = ((m + 2 : ℕ) : ℝ) := by
  simpa only [Nat.cast_add, Nat.cast_ofNat] using
    roundToEven_natCast_of_lt_two_pow p hp hm

/-- The signed version needs only a magnitude bound on the resulting word. -/
theorem roundToEven_intCast_add_two (p : ℕ) (hp : 2 ≤ p) {z : ℤ}
    (hz : (z + 2).natAbs < 2 ^ p) :
    roundToEven p hp ((z : ℝ) + 2) = ((z + 2 : ℤ) : ℝ) := by
  simpa only [Int.cast_add, Int.cast_ofNat, Nat.cast_ofNat] using
    roundToEven_intCast_of_natAbs_lt_two_pow p hp hz

/-- Numerical counter, using one nearest-even addition at each successor index. -/
def addTwoCounter (p : ℕ) (hp : 2 ≤ p) (start : ℝ) : ℕ → ℝ
  | 0 => start
  | j + 1 => roundToEven p hp (addTwoCounter p hp start j + 2)

/-- An explicit final-word bound guarantees every counter state through `N` is exact. -/
theorem addTwoCounter_eq_natCast (p : ℕ) (hp : 2 ≤ p) (m N : ℕ)
    (hbound : m + 2 * N < 2 ^ p) {j : ℕ} (hj : j ≤ N) :
    addTwoCounter p hp (m : ℝ) j = ((m + 2 * j : ℕ) : ℝ) := by
  induction j with
  | zero => simp [addTwoCounter]
  | succ j ih =>
      rw [addTwoCounter, ih (by omega)]
      have hstep : m + 2 * j + 2 < 2 ^ p := by omega
      rw [roundToEven_natCast_add_two p hp hstep]
      congr 1

/-- Counter states covered by the endpoint bound are native numerical words. -/
theorem addTwoCounter_native (p : ℕ) (hp : 2 ≤ p) (m N : ℕ)
    (hbound : m + 2 * N < 2 ^ p) {j : ℕ} (hj : j ≤ N) :
    Native p hp (addTwoCounter p hp (m : ℝ) j) := by
  rw [addTwoCounter_eq_natCast p hp m N hbound hj]
  apply native_natCast_of_lt_two_pow p hp
  omega

/-- Both odd and even coefficient words, including the endpoint, from rounded counters. -/
theorem coefficientCounters_eq (p : ℕ) (hp : 2 ≤ p) (N : ℕ)
    (hbound : 2 * N + 2 < 2 ^ (p - 1)) {j : ℕ} (hj : j ≤ N) :
    addTwoCounter p hp 1 j = ((2 * j + 1 : ℕ) : ℝ) ∧
      addTwoCounter p hp 2 j = ((2 * j + 2 : ℕ) : ℝ) := by
  have hpow : 2 ^ (p - 1) ≤ 2 ^ p :=
    Nat.pow_le_pow_right (by decide) (Nat.sub_le _ _)
  constructor
  · simpa [Nat.add_comm] using
      addTwoCounter_eq_natCast p hp 1 N (by omega) hj
  · simpa [Nat.add_comm] using
      addTwoCounter_eq_natCast p hp 2 N (by omega) hj

/-- The generated coefficient words are native and their denominator is positive. -/
theorem coefficientCounters_native_and_pos (p : ℕ) (hp : 2 ≤ p) (N : ℕ)
    (hbound : 2 * N + 2 < 2 ^ (p - 1)) {j : ℕ} (hj : j ≤ N) :
    Native p hp (addTwoCounter p hp 1 j) ∧
      Native p hp (addTwoCounter p hp 2 j) ∧
        0 < addTwoCounter p hp 2 j := by
  obtain ⟨hodd, heven⟩ := coefficientCounters_eq p hp N hbound hj
  rw [hodd, heven]
  refine ⟨native_natCast_of_lt_two_pow_pred p hp (by omega),
    native_natCast_of_lt_two_pow_pred p hp (by omega), ?_⟩
  positivity

end

end NumStability.FloatingPointFormat.UnboundedBinary
