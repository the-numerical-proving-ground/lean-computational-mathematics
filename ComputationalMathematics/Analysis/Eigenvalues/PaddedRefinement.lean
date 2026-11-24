import ComputationalMathematics.Analysis.Eigenvalues.NoisyRankCertificate
import ComputationalMathematics.Analysis.FloatingPointArithmetic.UnboundedBinary.IntegerWords
import ComputationalMathematics.Analysis.FloatingPointArithmetic.UnboundedBinary.ScalarOperations

/-!
# Fixed-length rounded refinement from strict-count brackets

For a monotone finite list, a count between the strict-below counts at
`x - ε` and `x + ε` suffices to refine a selected position. The shifts,
endpoints, and result are represented at one unbounded binary precision.
-/

namespace NumStability.FloatingPointFormat.UnboundedBinary.PaddedRefinement

open NumStability.NoisyRankCertificate

noncomputable section

private def exactWord {q : ℕ} {hq : 2 ≤ q} {x : ℝ} (hx : Native q hq x) :
    Word q hq :=
  Classical.choose (Word.exists_value_iff_native.mpr hx)

@[simp] private theorem exactWord_value {q : ℕ} {hq : 2 ≤ q} {x : ℝ}
    (hx : Native q hq x) : (exactWord hx).value = x :=
  Classical.choose_spec (Word.exists_value_iff_native.mpr hx)

/-- The two stored endpoints of the refinement loop. -/
structure Endpoints (q : ℕ) (hq : 2 ≤ q) where
  lower : Word q hq
  upper : Word q hq

/-- The initial interval for the scaled eigenvalue problem. -/
def initial (q : ℕ) (hq : 2 ≤ q) : Endpoints q hq :=
  ⟨exactWord (native_neg (native_two q hq)), exactWord (native_two q hq)⟩

/-- The source midpoint, formed by rounding the sum and scaling by one half. -/
def midpoint {q : ℕ} {hq : 2 ≤ q} (interval : Endpoints q hq) : Word q hq :=
  ((ScalarOperation.add interval.lower interval.upper).eval).scale (-1)

@[simp] theorem midpoint_value {q : ℕ} {hq : 2 ≤ q} (interval : Endpoints q hq) :
    (midpoint interval).value =
      roundToEven q hq (interval.lower.value + interval.upper.value) / 2 := by
  rw [midpoint, Word.value_scale]
  simp [ScalarOperation.eval, ScalarOperation.exactValue, div_eq_mul_inv, mul_comm]

private theorem native_three (q : ℕ) (hq : 2 ≤ q) : Native q hq (3 : ℝ) := by
  exact_mod_cast native_natCast_of_lt_two_pow q hq
    (show 3 < 2 ^ q from (by norm_num : 3 < 2 ^ 2).trans_le
      (Nat.pow_le_pow_right (by norm_num) hq))

/-- The prescribed padding, formed by scaling the stored integer three. -/
def padding (q : ℕ) (hq : 2 ≤ q) (r : ℕ) : Word q hq :=
  (exactWord (native_three q hq)).scale (-(r : ℤ) - 1)

@[simp] theorem padding_value (q : ℕ) (hq : 2 ≤ q) (r : ℕ) :
    (padding q hq r).value = 3 * unitRoundoff r / 2 := by
  rw [padding, Word.value_scale, exactWord_value,
    zpow_sub₀ (by norm_num : (2 : ℝ) ≠ 0), zpow_one]
  unfold unitRoundoff
  ring

open Classical in
/-- Apply one rounded padded update using the count at the supplied midpoint. -/
def update {n q : ℕ} {hq : 2 ≤ q} (t : Word q hq) (j : Fin n)
    (interval : Endpoints q hq) (x : Word q hq) (count : ℕ) : Endpoints q hq :=
  if count ≤ j.val then
    let candidate := (ScalarOperation.sub x t).eval
    ⟨if interval.lower.value ≤ candidate.value then candidate else interval.lower, interval.upper⟩
  else
    let candidate := (ScalarOperation.add x t).eval
    ⟨interval.lower, if candidate.value ≤ interval.upper.value then candidate else interval.upper⟩

/-- One count at the stored midpoint, followed by one rounded padded update. -/
def step {n q : ℕ} {hq : 2 ≤ q} (r : ℕ) (j : Fin n)
    (count : Word q hq → ℕ) (interval : Endpoints q hq) : Endpoints q hq :=
  let x := midpoint interval
  update (padding q hq r) j interval x (count x)

/-- The loop state after exactly `m` updates. -/
def iterate {n q : ℕ} {hq : 2 ≤ q} (r : ℕ) (j : Fin n)
    (count : Word q hq → ℕ) : ℕ → Endpoints q hq
  | 0 => initial q hq
  | m + 1 => step r j count (iterate r j count m)

/-- The returned midpoint after exactly `r + 4` transitions. -/
def refine {n q : ℕ} {hq : 2 ≤ q} (r : ℕ) (j : Fin n)
    (count : Word q hq → ℕ) : Word q hq :=
  midpoint (iterate r j count (r + 4))

/-- The stored endpoints enclose the value inside the initial interval. -/
def Endpoints.Contains {q : ℕ} {hq : 2 ≤ q}
    (interval : Endpoints q hq) (value : ℝ) : Prop :=
  -2 ≤ interval.lower.value ∧ interval.lower.value ≤ value ∧
    value ≤ interval.upper.value ∧ interval.upper.value ≤ 2

private theorem eps_le_quarter {r : ℕ} (hr : 2 ≤ r) : unitRoundoff r ≤ 1 / 4 := by
  unfold unitRoundoff
  have hcast : (2 : ℤ) ≤ (r : ℤ) := by exact_mod_cast hr
  calc
    (2 : ℝ) ^ (-(r : ℤ)) ≤ (2 : ℝ) ^ (-2 : ℤ) :=
      zpow_le_zpow_right₀ (by norm_num) (by omega)
    _ = 1 / 4 := by norm_num

private theorem unitRoundoff_le_eps_div {q r : ℕ} (hqr : r + 8 ≤ q) :
    unitRoundoff q ≤ unitRoundoff r / 256 := by
  unfold unitRoundoff
  have hcast : (r : ℤ) + 8 ≤ (q : ℤ) := by exact_mod_cast hqr
  calc
    (2 : ℝ) ^ (-(q : ℤ)) ≤ (2 : ℝ) ^ (-(r : ℤ) - 8) :=
      zpow_le_zpow_right₀ (by norm_num) (by omega)
    _ = _ := by rw [zpow_sub₀ (by norm_num : (2 : ℝ) ≠ 0)]; norm_num

private theorem midpoint_bounds {q : ℕ} {hq : 2 ≤ q} {interval : Endpoints q hq}
    {value : ℝ} (h : interval.Contains value) :
    interval.lower.value ≤ (midpoint interval).value ∧
    (midpoint interval).value ≤ interval.upper.value ∧
    |(midpoint interval).value - (interval.lower.value + interval.upper.value) / 2| ≤
      2 * unitRoundoff q := by
  obtain ⟨hlo, hl, hh, hhi⟩ := h
  have hln : Native q hq (interval.lower.value * 2) := by
    simpa using native_mul_zpow interval.lower.native_value (1 : ℤ)
  have hhn : Native q hq (interval.upper.value * 2) := by
    simpa using native_mul_zpow interval.upper.native_value (1 : ℤ)
  have hl' := roundToEven_monotone q hq (show
      interval.lower.value * 2 ≤ interval.lower.value + interval.upper.value by linarith)
  have hh' := roundToEven_monotone q hq (show
      interval.lower.value + interval.upper.value ≤ interval.upper.value * 2 by linarith)
  rw [roundToEven_eq_self_of_native hln] at hl'
  rw [roundToEven_eq_self_of_native hhn] at hh'
  have herr := abs_roundToEven_sub_le_of_abs_le q hq
    (interval.lower.value + interval.upper.value) 4 (abs_le.mpr ⟨by linarith, by linarith⟩)
  refine ⟨by rw [midpoint_value]; linarith, by rw [midpoint_value]; linarith, ?_⟩
  rw [midpoint_value]
  rw [← sub_div, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  linarith

private theorem step_bounds {n q r : ℕ} {hq : 2 ≤ q} {j : Fin n}
    {values : Fin n → ℝ} (hvalues : Monotone values)
    {count : Word q hq → ℕ}
    (hcount : ∀ x, -2 ≤ x.value → x.value ≤ 2 →
      strictBelowCount values (x.value - unitRoundoff r) ≤ count x ∧
      count x ≤ strictBelowCount values (x.value + unitRoundoff r))
    (hr : 2 ≤ r) (hqr : r + 8 ≤ q) {interval : Endpoints q hq}
    (hinterval : interval.Contains (values j)) :
    (step r j count interval).Contains (values j) ∧
      (step r j count interval).upper.value - (step r j count interval).lower.value ≤
        (interval.upper.value - interval.lower.value) / 2 +
          3 * unitRoundoff r / 2 + 5 * unitRoundoff q := by
  obtain ⟨hlx, hxh, hmid⟩ := midpoint_bounds hinterval
  obtain ⟨hlo, hl, hh, hhi⟩ := hinterval
  let x := midpoint interval
  let t := 3 * unitRoundoff r / 2
  have hxl : -2 ≤ x.value := hlo.trans hlx
  have hxh' : x.value ≤ 2 := hxh.trans hhi
  have htc : 0 ≤ t ∧ t ≤ 3 / 8 := by
    dsimp [t]
    constructor <;> linarith [unitRoundoff_pos r, eps_le_quarter hr]
  have hu := unitRoundoff_le_eps_div hqr
  have hε := unitRoundoff_pos r
  have hcl : |roundToEven q hq (x.value - t) - (x.value - t)| ≤ 3 * unitRoundoff q := by
    rw [mul_comm]
    exact abs_roundToEven_sub_le_of_abs_le q hq _ 3
      (abs_le.mpr ⟨by linarith [htc.2], by linarith [htc.1]⟩)
  have hch : |roundToEven q hq (x.value + t) - (x.value + t)| ≤ 3 * unitRoundoff q := by
    rw [mul_comm]
    exact abs_roundToEven_sub_le_of_abs_le q hq _ 3
      (abs_le.mpr ⟨by linarith [htc.1], by linarith [htc.2]⟩)
  have hmid' := abs_le.mp hmid
  have hcl' := abs_le.mp hcl
  have hch' := abs_le.mp hch
  have ⟨hcountlo, hcounthi⟩ := hcount x hxl hxh'
  by_cases hc : count x ≤ j.val
  · have hrank := le_of_strictBelowCount_le hvalues _ j (hcountlo.trans hc)
    have hcand : roundToEven q hq (x.value - t) ≤ values j := by
      dsimp [t] at *
      linarith [hcl'.2]
    simp only [step, update, show count (midpoint interval) ≤ j.val from hc, if_true]
    change _ ∧ _
    split <;> rename_i hselect
    · refine ⟨⟨hlo.trans hselect, ?_, hh, hhi⟩, ?_⟩
      · simpa only [ScalarOperation.eval, ScalarOperation.exactValue, Word.value_round,
          padding_value, t] using hcand
      · simp only [ScalarOperation.eval, ScalarOperation.exactValue, Word.value_round, padding_value]
        dsimp [t] at *
        linarith [hcl'.1, hmid'.1]
    · refine ⟨⟨hlo, hl, hh, hhi⟩, ?_⟩
      change interval.upper.value - interval.lower.value ≤ _
      dsimp [t] at *
      have hselect' : roundToEven q hq (x.value - 3 * unitRoundoff r / 2) ≤
          interval.lower.value := by
        simpa only [padding_value, ScalarOperation.eval, ScalarOperation.exactValue,
          Word.value_round] using (le_of_not_ge hselect)
      linarith [hcl'.1, hmid'.1]
  · have hrank := lt_of_lt_strictBelowCount hvalues _ j ((lt_of_not_ge hc).trans_le hcounthi)
    have hcand : values j ≤ roundToEven q hq (x.value + t) := by
      dsimp [t] at *
      linarith [hch'.1]
    simp only [step, update, show ¬ count (midpoint interval) ≤ j.val from hc, if_false]
    change _ ∧ _
    split <;> rename_i hselect
    · refine ⟨⟨hlo, hl, ?_, hselect.trans hhi⟩, ?_⟩
      · simpa only [ScalarOperation.eval, ScalarOperation.exactValue, Word.value_round,
          padding_value, t] using hcand
      · simp only [ScalarOperation.eval, ScalarOperation.exactValue, Word.value_round, padding_value]
        dsimp [t] at *
        linarith [hch'.2, hmid'.2]
    · refine ⟨⟨hlo, hl, hh, hhi⟩, ?_⟩
      change interval.upper.value - interval.lower.value ≤ _
      dsimp [t] at *
      have hselect' : interval.upper.value ≤
          roundToEven q hq (x.value + 3 * unitRoundoff r / 2) := by
        simpa only [padding_value, ScalarOperation.eval, ScalarOperation.exactValue,
          Word.value_round] using (le_of_not_ge hselect)
      linarith [hch'.2, hmid'.2]

/-- The rounded padded loop preserves the enclosure and returns a label with
the stated accuracy from the strict-count brackets. Repeated entries are allowed. -/
theorem refine_enclosures_and_accuracy {n q r : ℕ} {hq : 2 ≤ q} (j : Fin n)
    {values : Fin n → ℝ} (hvalues : Monotone values)
    (hlo : -2 ≤ values j) (hhi : values j ≤ 2)
    (count : Word q hq → ℕ)
    (hcount : ∀ x, -2 ≤ x.value → x.value ≤ 2 →
      strictBelowCount values (x.value - unitRoundoff r) ≤ count x ∧
      count x ≤ strictBelowCount values (x.value + unitRoundoff r))
    (hr : 2 ≤ r) (hqr : r + 8 ≤ q) :
    (∀ m,
      let interval := iterate r j count m
      let x := midpoint interval
      interval.Contains (values j) ∧
        interval.lower.value ≤ x.value ∧ x.value ≤ interval.upper.value) ∧
    |(refine r j count).value - values j| ≤ (423 / 256) * unitRoundoff r ∧
      (423 / 256) * unitRoundoff r < 2 * unitRoundoff r := by
  let B := 3 * unitRoundoff r / 2 + 5 * unitRoundoff q
  have hloop (m : ℕ) : (iterate r j count m).Contains (values j) ∧
      (iterate r j count m).upper.value - (iterate r j count m).lower.value ≤
        4 * unitRoundoff m + 2 * B := by
    induction m with
    | zero =>
        constructor
        · simpa [iterate, initial, Endpoints.Contains] using And.intro hlo hhi
        · simp only [iterate, initial, exactWord_value]
          have hB : 0 ≤ B := by dsimp [B]; linarith [unitRoundoff_pos r, unitRoundoff_pos q]
          norm_num [unitRoundoff]
          exact le_add_of_nonneg_right (mul_nonneg (by norm_num) hB)
    | succ m ih =>
        obtain ⟨hm, hw⟩ := ih
        obtain ⟨hnext, hcontract⟩ := step_bounds hvalues hcount hr hqr hm
        refine ⟨hnext, ?_⟩
        have hhalf : unitRoundoff (m + 1) = unitRoundoff m / 2 := by
          simp only [unitRoundoff, Nat.cast_add, Nat.cast_one]
          rw [show -((m : ℤ) + 1) = -(m : ℤ) - 1 by ring,
            zpow_sub₀ (by norm_num : (2 : ℝ) ≠ 0), zpow_one]
        rw [hhalf]
        change (step r j count (iterate r j count m)).upper.value -
          (step r j count (iterate r j count m)).lower.value ≤ _
        dsimp [B] at *
        linarith
  refine ⟨?_, ?_⟩
  · intro m
    have hinterval := (hloop m).1
    have hmidpoint := midpoint_bounds hinterval
    exact ⟨hinterval, hmidpoint.1, hmidpoint.2.1⟩
  let interval := iterate r j count (r + 4)
  have ⟨hinterval, hwidth⟩ := hloop (r + 4)
  have hsmall : unitRoundoff (r + 4) = unitRoundoff r / 16 := by
    simp only [unitRoundoff, Nat.cast_add, Nat.cast_ofNat]
    rw [show -((r : ℤ) + 4) = -(r : ℤ) - 4 by ring, zpow_sub₀ (by norm_num : (2 : ℝ) ≠ 0)]
    norm_num
  have hmid := abs_le.mp (midpoint_bounds hinterval).2.2
  obtain ⟨_, hl, hh, _⟩ := hinterval
  have hu := unitRoundoff_le_eps_div hqr
  have hε := unitRoundoff_pos r
  rw [hsmall] at hwidth
  change |(midpoint interval).value - values j| ≤ (423 / 256) * unitRoundoff r ∧ _
  dsimp [B] at hwidth
  exact ⟨abs_le.mpr ⟨by linarith [hmid.1], by linarith [hmid.2]⟩, by linarith⟩

end

end NumStability.FloatingPointFormat.UnboundedBinary.PaddedRefinement
