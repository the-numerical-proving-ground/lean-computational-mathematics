import ComputationalMathematics.Analysis.FloatingPointArithmetic.NearestRoundingError

/-!
# Unbounded binary nearest-even rounding

Mathematical denotations for precision `p ≥ 2`, with unrestricted integer
exponents and an explicit zero value. The shared format's finite exponent
metadata is unused by its unbounded value set and nearest-even policy.

These definitions specify the primitive's real semantics. They do not implement
a real-to-word conversion or establish an arithmetic work bound.
-/

namespace NumStability.FloatingPointFormat.UnboundedBinary

/-- Binary precision specialization. Only `beta` and `t` participate in the
unbounded normalized system selected below. -/
def format (p : ℕ) (hp : 2 ≤ p) : FloatingPointFormat where
  beta := 2
  t := p
  emin := 0
  emax := 0
  beta_ge_two := le_rfl
  t_pos := lt_of_lt_of_le (by decide : 0 < 2) hp
  emin_le_emax := le_rfl

/-- Zero or an exactly represented signed normalized binary value with at most
`p` significand bits and an arbitrary integer exponent. -/
def Native (p : ℕ) (hp : 2 ≤ p) (x : ℝ) : Prop :=
  x = 0 ∨ (format p hp).unboundedNormalizedSystem x

/-- Unit roundoff at precision `p`, without an exponent-range restriction. -/
noncomputable def unitRoundoff (p : ℕ) : ℝ := (2 : ℝ) ^ (-(p : ℤ))

/-- The chosen nearest-even real denotation, with exact zero handled explicitly.
The selector uses only the existing concrete nearest-even policy; error bounds
are conclusions to be proved separately. -/
noncomputable def roundToEven (p : ℕ) (hp : 2 ≤ p) (x : ℝ) : ℝ :=
  if x = 0 then 0
  else Classical.epsilon fun y => (format p hp).sourceRoundToEvenEvidence x y

end NumStability.FloatingPointFormat.UnboundedBinary
