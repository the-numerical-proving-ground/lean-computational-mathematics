import ComputationalMathematics.Analysis.FloatingPointArithmetic.UnboundedBinary.NativeEmptyBinScan
import ComputationalMathematics.Analysis.FloatingPointArithmetic.UnboundedBinary.WordComparison

/-!
# Default native comparison for the first-empty-bin scan

The scan currently stores native scalars as a subtype of the reals. The
adapter identifies a subtype value with its unique stored binary word. In
the word representation, the comparison reads only its existing fields.
-/

namespace NumStability.FloatingPointFormat.UnboundedBinary.EmptyBinScan

/-- Compare the stored binary representations of both native operands. -/
noncomputable def defaultComparison (p : ℕ) (hp : 2 ≤ p) : Comparison p hp where
  lt a b := (UnboundedBinary.Word.ofNative a.val a.property).lt
    (UnboundedBinary.Word.ofNative b.val b.property)
  correct a b := by
    rw [UnboundedBinary.Word.lt_eq_true_iff, UnboundedBinary.Word.value_ofNative,
      UnboundedBinary.Word.value_ofNative]

/-- On already stored words the default scan comparison is the executable
field comparison. No representation conversion changes either value. -/
@[simp] theorem defaultComparison_lt_of_values {p : ℕ} {hp : 2 ≤ p}
    (a b : UnboundedBinary.Word p hp) :
    (defaultComparison p hp).lt ⟨a.value, a.native_value⟩ ⟨b.value, b.native_value⟩ =
      a.lt b := by
  simp only [defaultComparison, UnboundedBinary.Word.ofNative_value]

end NumStability.FloatingPointFormat.UnboundedBinary.EmptyBinScan
