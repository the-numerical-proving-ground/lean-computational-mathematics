import ComputationalMathematics.Analysis.FloatingPointArithmetic.UnboundedBinary.ScalarOperations

/-!
# Unbounded binary rounding at positive precision

At one bit the normalized significands of both neighbors of a nonnative
midpoint are odd. IEEE 754-2019 §4.3.1 completes nearest-even in this case by
taking the larger magnitude. Equivalently, GNU MPFR §4.4 compares the two
significands at the exponent of the unrounded number, before the carry
renormalizes the upper magnitude. At higher precision the usual normalized
nearest-even rule already selects an endpoint.
-/

namespace NumStability.FloatingPointFormat.UnboundedBinary

/-- The unbounded binary format parameters at any positive precision. -/
def positiveFormat (p : ℕ) (hp : 0 < p) : FloatingPointFormat where
  beta := 2
  t := p
  emin := 0
  emax := 0
  beta_ge_two := le_rfl
  t_pos := hp
  emin_le_emax := le_rfl

/-- The native numbers include zero and all integer exponents. -/
def NativeAt (p : ℕ) (hp : 0 < p) (x : ℝ) : Prop :=
  x = 0 ∨ (positiveFormat p hp).unboundedNormalizedSystem x

theorem nativeAt_iff_native (p : ℕ) (hp : 2 ≤ p) (x : ℝ) :
    NativeAt p (by omega) x ↔ Native p hp x :=
  Iff.rfl

theorem oneBit_significand_eq_one {m : ℕ}
    (hm : (positiveFormat 1 (by decide)).normalizedMantissa m) : m = 1 := by
  change 1 ≤ m ∧ m < 2 at hm
  omega

private theorem exists_oneBit (x : ℝ) (hx : x ≠ 0) :
    ∃ y δ : ℝ,
      (positiveFormat 1 (by decide)).nearestRoundingToUnbounded x y ∧
      |δ| < unitRoundoff 1 ∧ signedRelErrorWitness y x δ ∧
      (positiveFormat 1 (by decide)).sourceRoundAwayEvidence x y := by
  obtain ⟨y, δ, hnear, hδ, hwit, hevidence⟩ :=
    exists_nearestAdjacentRoundAway_signedRelErrorWitness_lt_nonzero
      (fmt := positiveFormat 1 (by decide)) hx
  refine ⟨y, δ, hnear, ?_, hwit, hevidence⟩
  have heq : (positiveFormat 1 (by decide)).unitRoundoff = unitRoundoff 1 := by
    norm_num [FloatingPointFormat.unitRoundoff, FloatingPointFormat.machineEpsilon,
      FloatingPointFormat.betaR, positiveFormat, unitRoundoff]
  simpa only [heq] using hδ

private noncomputable def roundOneBit (x : ℝ) : ℝ :=
  if x = 0 then 0 else Classical.epsilon fun y =>
    ∃ δ : ℝ, (positiveFormat 1 (by decide)).nearestRoundingToUnbounded x y ∧
      |δ| < unitRoundoff 1 ∧ signedRelErrorWitness y x δ ∧
      (positiveFormat 1 (by decide)).sourceRoundAwayEvidence x y

private theorem roundOneBit_spec {x : ℝ} (hx : x ≠ 0) :
    ∃ δ : ℝ,
      (positiveFormat 1 (by decide)).nearestRoundingToUnbounded x (roundOneBit x) ∧
      |δ| < unitRoundoff 1 ∧ signedRelErrorWitness (roundOneBit x) x δ ∧
      (positiveFormat 1 (by decide)).sourceRoundAwayEvidence x (roundOneBit x) := by
  simpa only [roundOneBit, if_neg hx] using Classical.epsilon_spec (exists_oneBit x hx)

/-- Nearest-even rounding, including the standard one-bit tie case. -/
noncomputable def roundAt (p : ℕ) (_hp : 0 < p) (x : ℝ) : ℝ :=
  if hp : 2 ≤ p then roundToEven p hp x else roundOneBit x

theorem roundAt_eq_roundToEven (p : ℕ) (hp : 2 ≤ p) (x : ℝ) :
    roundAt p (by omega) x = roundToEven p hp x := by
  simp [roundAt, hp]

theorem roundAt_oneBit_evidence {x : ℝ} (hx : x ≠ 0) :
    (positiveFormat 1 (by decide)).sourceRoundAwayEvidence x (roundAt 1 (by decide) x) := by
  obtain ⟨_, _, _, _, hpolicy⟩ := roundOneBit_spec hx
  simpa [roundAt] using hpolicy

theorem abs_roundAt_sub_le (p : ℕ) (hp : 0 < p) (x : ℝ) :
    |roundAt p hp x - x| ≤ unitRoundoff p * |x| := by
  by_cases htwo : 2 ≤ p
  · rw [roundAt_eq_roundToEven p htwo]
    exact abs_roundToEven_sub_le p htwo x
  · have h : p = 1 := by omega
    subst p
    simp only [roundAt, Nat.reduceLeDiff, dite_false]
    by_cases hx : x = 0
    · simp [hx, roundOneBit]
    obtain ⟨δ, _, hδ, hwit, _⟩ := roundOneBit_spec hx
    have hdiff : roundOneBit x - x = x * δ := by
      unfold signedRelErrorWitness at hwit
      rw [hwit]
      ring
    rw [hdiff, abs_mul, mul_comm |x|]
    exact mul_le_mul_of_nonneg_right hδ.le (abs_nonneg x)

theorem roundAt_nearest (p : ℕ) (hp : 0 < p) (x : ℝ) :
    FloatingPointFormat.nearestRoundingIn (NativeAt p hp) x (roundAt p hp x) := by
  by_cases htwo : 2 ≤ p
  · rw [roundAt_eq_roundToEven p htwo]
    exact roundToEven_nearestRoundingIn p htwo x
  · have h : p = 1 := by omega
    subst p
    by_cases hx : x = 0
    · subst x
      have hr : roundAt 1 (by decide) 0 = 0 := by simp [roundAt, roundOneBit]
      rw [hr]
      exact FloatingPointFormat.nearestRoundingIn_self (Or.inl rfl)
    have hr : roundAt 1 (by decide) x = roundOneBit x := by simp [roundAt]
    rw [hr]
    obtain ⟨_, hnear, _, _, _⟩ := roundOneBit_spec hx
    refine ⟨Or.inr hnear.1, ?_⟩
    intro z hz
    rcases hz with rfl | hz
    · have hbound := abs_roundAt_sub_le 1 (by decide) x
      rw [hr] at hbound
      have hunit : unitRoundoff 1 ≤ 1 := by norm_num [unitRoundoff]
      simpa [abs_sub_comm x (roundOneBit x)] using
        hbound.trans (mul_le_of_le_one_left (abs_nonneg x) hunit)
    · exact hnear.2 z hz

end NumStability.FloatingPointFormat.UnboundedBinary
