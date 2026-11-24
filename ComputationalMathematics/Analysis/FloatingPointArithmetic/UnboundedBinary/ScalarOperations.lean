import ComputationalMathematics.Analysis.FloatingPointArithmetic.UnboundedBinary.Basic
import Mathlib.Data.Real.Sqrt

/-!
# Scalar operations on unbounded binary words

A normalized word stores its exponent explicitly. Exact power-of-two scaling
updates that field. Rounded arithmetic is specified by its real denotation
using the shared nearest-even selector.
-/

namespace NumStability.FloatingPointFormat.UnboundedBinary

/-- A binary scalar word with a separate zero case and no exponent bound. -/
inductive Word (p : ℕ) (hp : 2 ≤ p) where
  | zero
  | normal (negative : Bool) (significand : ℕ) (exponent : ℤ)
      (normalized : (format p hp).normalizedMantissa significand)

namespace Word

/-- Real value represented by a word. -/
noncomputable def value {p : ℕ} {hp : 2 ≤ p} : Word p hp → ℝ
  | .zero => 0
  | .normal negative significand exponent _ =>
    (format p hp).normalizedValue negative significand exponent

/-- The stored exponent of a nonzero word. -/
def exponent {p : ℕ} {hp : 2 ≤ p} : Word p hp → Option ℤ
  | .zero => none
  | .normal _ _ exponent _ => some exponent

/-- Exact multiplication by a binary power, as a representation operation. -/
def scale {p : ℕ} {hp : 2 ≤ p} (k : ℤ) : Word p hp → Word p hp
  | .zero => .zero
  | .normal negative significand exponent normalized =>
    .normal negative significand (exponent + k) normalized

theorem native_value {p : ℕ} {hp : 2 ≤ p} (word : Word p hp) :
    Native p hp word.value := by
  cases word with
  | zero => exact Or.inl rfl
  | normal negative significand exponent normalized =>
    exact Or.inr ⟨negative, significand, exponent, normalized, rfl⟩

theorem exists_value_iff_native {p : ℕ} {hp : 2 ≤ p} {x : ℝ} :
    (∃ word : Word p hp, word.value = x) ↔ Native p hp x := by
  constructor
  · rintro ⟨word, rfl⟩
    exact word.native_value
  · rintro (rfl | ⟨negative, significand, exponent, normalized, rfl⟩)
    · exact ⟨.zero, rfl⟩
    · exact ⟨.normal negative significand exponent normalized, rfl⟩

theorem value_scale {p : ℕ} {hp : 2 ≤ p} (word : Word p hp) (k : ℤ) :
    (word.scale k).value = (2 : ℝ) ^ k * word.value := by
  cases word with
  | zero => simp [scale, value]
  | normal negative significand exponent normalized =>
    exact (betaR_zpow_mul_normalizedValue (format p hp) k negative significand exponent).symm

theorem exponent_scale {p : ℕ} {hp : 2 ≤ p} (word : Word p hp) (k : ℤ) :
    (word.scale k).exponent = word.exponent.map (· + k) := by
  cases word <;> rfl

/-- The word representing the nearest-even real result at the requested precision. -/
noncomputable def round (p : ℕ) (hp : 2 ≤ p) (x : ℝ) : Word p hp :=
  Classical.choose (exists_value_iff_native.mpr (roundToEven_native p hp x))

@[simp] theorem value_round (p : ℕ) (hp : 2 ≤ p) (x : ℝ) :
    (round p hp x).value = roundToEven p hp x :=
  Classical.choose_spec (exists_value_iff_native.mpr (roundToEven_native p hp x))

/-- One precision conversion, with nearest-even rounding at the destination. -/
noncomputable def convert {p : ℕ} {hp : 2 ≤ p} (q : ℕ) (hq : 2 ≤ q)
    (word : Word p hp) : Word q hq :=
  round q hq word.value

end Word

/-- Scalar operations at one binary precision. Division and square root carry
the hypotheses that put the operands in the real operation's domain. -/
inductive ScalarOperation (p : ℕ) (hp : 2 ≤ p) where
  | add (x y : Word p hp)
  | sub (x y : Word p hp)
  | mul (x y : Word p hp)
  | div (x y : Word p hp) (hy : y.value ≠ 0)
  | sqrt (x : Word p hp) (hx : 0 ≤ x.value)

namespace ScalarOperation

/-- The real result used to specify the corresponding rounded operation. -/
noncomputable def exactValue {p : ℕ} {hp : 2 ≤ p} : ScalarOperation p hp → ℝ
  | .add x y => x.value + y.value
  | .sub x y => x.value - y.value
  | .mul x y => x.value * y.value
  | .div x y _ => x.value / y.value
  | .sqrt x _ => Real.sqrt x.value

/-- Evaluate the scalar operation with one nearest-even rounding. -/
noncomputable def eval {p : ℕ} {hp : 2 ≤ p} (operation : ScalarOperation p hp) : Word p hp :=
  Word.round p hp operation.exactValue

end ScalarOperation

end NumStability.FloatingPointFormat.UnboundedBinary
