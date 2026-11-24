import ComputationalMathematics.Analysis.FloatingPointArithmetic.UnboundedBinary.ScalarOperations

/-! Exact changes to the precision of stored binary words. -/

namespace NumStability.FloatingPointFormat.UnboundedBinary.Word

/-- Exactly widen a word by zero-extending its binary significand. -/
def widen {p q : ℕ} {hp : 2 ≤ p} (hq : 2 ≤ q) (hpq : p ≤ q) :
    Word p hp → Word q hq
  | .zero => .zero
  | .normal sign m e hm => .normal sign (m * 2 ^ (q - p)) e (by
    change 2 ^ (p - 1) ≤ m ∧ m < 2 ^ p at hm
    change 2 ^ (q - 1) ≤ m * 2 ^ (q - p) ∧ m * 2 ^ (q - p) < 2 ^ q
    constructor
    · rw [show q - 1 = (p - 1) + (q - p) by omega, pow_add]
      exact Nat.mul_le_mul_right _ hm.1
    · calc
        _ < 2 ^ p * 2 ^ (q - p) := Nat.mul_lt_mul_of_pos_right hm.2 (by positivity)
        _ = 2 ^ q := by rw [← pow_add, show p + (q - p) = q by omega])

@[simp] theorem value_widen {p q : ℕ} {hp : 2 ≤ p} (hq : 2 ≤ q) (hpq : p ≤ q)
    (x : Word p hp) : (x.widen hq hpq).value = x.value := by
  cases x with
  | zero => rfl
  | normal sign m e hm =>
    change (if sign then -1 else 1 : ℝ) * (((m * 2 ^ (q - p)) : ℕ) : ℝ) *
        (2 : ℝ) ^ (e - (q : ℤ)) =
      (if sign then -1 else 1 : ℝ) * (m : ℝ) * (2 : ℝ) ^ (e - (p : ℤ))
    push_cast
    have hpow : (2 : ℝ) ^ (q - p) * (2 : ℝ) ^ (e - (q : ℤ)) = (2 : ℝ) ^ (e - (p : ℤ)) := by
      rw [← zpow_natCast (2 : ℝ) (q - p), ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
      congr 1
      omega
    rw [← hpow]
    ring

end NumStability.FloatingPointFormat.UnboundedBinary.Word
