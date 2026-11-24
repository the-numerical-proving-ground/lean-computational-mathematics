import ComputationalMathematics.Analysis.FloatingPointArithmetic.UnboundedBinary.ScalarOperations

/-!
# Exact order on stored binary words

Signs, exponents and significands determine the real order exactly.
The comparison of stored fields is executable and requires no rounding.
-/

namespace NumStability.FloatingPointFormat.UnboundedBinary.Word

variable {p : ℕ} {hp : 2 ≤ p}

private def positiveFieldsLT (m : ℕ) (e : ℤ) (n : ℕ) (f : ℤ) : Bool :=
  decide (e < f ∨ (e = f ∧ m < n))

private theorem positiveFieldsLT_correct {m n : ℕ} {e f : ℤ}
    (hm : (format p hp).normalizedMantissa m) (hn : (format p hp).normalizedMantissa n) :
    positiveFieldsLT m e n f = true ↔
      (format p hp).normalizedValue false m e < (format p hp).normalizedValue false n f := by
  simp only [positiveFieldsLT, decide_eq_true_eq]
  rcases lt_trichotomy e f with hef | rfl | hfe
  · simp [hef, (format p hp).normalizedValue_false_lt_of_exp_lt hm hn hef]
  · simpa using ((format p hp).normalizedValue_sameExponent_lt_iff_false m n e).symm
  · have hv := (format p hp).normalizedValue_false_lt_of_exp_lt hn hm hfe
    simp [not_lt_of_gt hfe, ne_of_gt hfe, not_lt_of_gt hv]

/-- Strict numerical order, evaluated only on the two stored words. -/
def lt : Word p hp → Word p hp → Bool
  | .zero, .zero => false
  | .zero, .normal negative _ _ _ => !negative
  | .normal negative _ _ _, .zero => negative
  | .normal false m e _, .normal false n f _ => positiveFieldsLT m e n f
  | .normal true m e _, .normal true n f _ => positiveFieldsLT n f m e
  | .normal true _ _ _, .normal false _ _ _ => true
  | .normal false _ _ _, .normal true _ _ _ => false

/-- Strict comparison agrees with the real denotations, for all signs and zero. -/
theorem lt_eq_true_iff (a b : Word p hp) : a.lt b = true ↔ a.value < b.value := by
  cases a with
  | zero =>
    cases b with
    | zero => simp [lt, value]
    | normal negative n f hn =>
      cases negative
      · simp [lt, value, (format p hp).normalizedValue_false_pos (e := f) hn]
      · simp [lt, value, not_lt_of_gt ((format p hp).normalizedValue_true_neg (e := f) hn)]
  | normal negative m e hm =>
    cases b with
    | zero =>
      cases negative
      · simp [lt, value, not_lt_of_gt ((format p hp).normalizedValue_false_pos (e := e) hm)]
      · simp [lt, value, (format p hp).normalizedValue_true_neg (e := e) hm]
    | normal negative' n f hn =>
      cases negative <;> cases negative'
      · exact positiveFieldsLT_correct hm hn
      · have hv := lt_trans ((format p hp).normalizedValue_true_neg (e := f) hn)
          ((format p hp).normalizedValue_false_pos (e := e) hm)
        simp [lt, value, not_lt_of_gt hv]
      · have hv := lt_trans ((format p hp).normalizedValue_true_neg (e := e) hm)
          ((format p hp).normalizedValue_false_pos (e := f) hn)
        simp [lt, value, hv]
      · simpa only [lt, value, (format p hp).normalizedValue_true_eq_neg_false, neg_lt_neg_iff]
          using (positiveFieldsLT_correct (e := f) (f := e) hn hm)

/-- The normalized representation of a native value is unique, including zero. -/
theorem value_injective : Function.Injective (value : Word p hp → ℝ) := by
  intro a b h
  cases a with
  | zero =>
    cases b with
    | zero => rfl
    | normal s n e hn => exact ((format p hp).normalizedValue_ne_zero hn h.symm).elim
  | normal s m e hm =>
    cases b with
    | zero => exact ((format p hp).normalizedValue_ne_zero hm h).elim
    | normal t n f hn =>
      obtain ⟨rfl, rfl, rfl⟩ := (format p hp).normalizedValue_eq_sign_exp_mantissa hm hn h
      rfl

/-- Interpret an already-native scalar as its unique stored word. This adapter
is a representation of the same value and performs no numerical rounding. -/
noncomputable def ofNative (x : ℝ) (hx : Native p hp x) : Word p hp :=
  Classical.choose (exists_value_iff_native.mpr hx)

@[simp] theorem value_ofNative (x : ℝ) (hx : Native p hp x) : (ofNative x hx).value = x :=
  Classical.choose_spec (exists_value_iff_native.mpr hx)

@[simp] theorem ofNative_value (a : Word p hp) : ofNative a.value a.native_value = a :=
  value_injective (value_ofNative _ _)

end NumStability.FloatingPointFormat.UnboundedBinary.Word
