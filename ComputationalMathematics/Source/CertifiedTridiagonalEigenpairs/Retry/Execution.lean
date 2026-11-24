import ComputationalMathematics.Source.CertifiedTridiagonalEigenpairs.FiniteTrial.CostReliabilityTarget
import ComputationalMathematics.Source.CertifiedTridiagonalEigenpairs.Retry.FiniteTrials

/-!
# The accept-first tridiagonal retry execution

Each trial consumes its own block of fair bits and runs the rounded gate on the same
original diagonal and subdiagonal. The first accepted run supplies the stored words
for the rest of the eigensolver. A stream with no acceptance has infinite attempt count.
-/

open MeasureTheory
open scoped ENNReal

namespace NumStability.CertifiedTridiagonalEigenpairs

open IndependentRetry NoisyRankCertificate

/-- The bits read by one invocation of the actual rounded gate. -/
abbrev GateBits (n : ℕ) (J : Finset ℕ) :=
  Fin (n + 1) → FairBitWord (rngBits (n + 1) J.card)

/-- The sampler's bit law repeated independently for every trial of the gate. -/
noncomputable abbrev retryBitMeasure (n : ℕ) (J : Finset ℕ) : Measure (ℕ → GateBits n J) :=
  streamMeasure (trialBitLaw (n + 1) J.card).toMeasure

/-- The index is zero-based. The sampled diagonal is the one stored by the successful gate. -/
structure RetryResult (n : ℕ) (J : Finset ℕ) (p : ℕ) where
  index : ℕ
  trial : {t : FiniteTrialResult n J p // t.accepted = true}

/-- Return the first successful gate invocation. `none` represents a stream that never returns. -/
noncomputable def retryRun {n p : ℕ} {J : Finset ℕ}
    (a : Fin (n + 1) → TrialWord n J p) (b : Fin n → TrialWord n J p)
    (bits : ℕ → GateBits n J) : Option (RetryResult n J p) := by
  classical
  exact if h : ∃ j, trialAccepts n p J a b (bits j) = true then
    some ⟨Nat.find h, ⟨trialRun n p J a b (bits (Nat.find h)), Nat.find_spec h⟩⟩
  else none

/-- Reconstruct the matrix used after acceptance from the stored diagonal and original subdiagonal. -/
noncomputable def RetryResult.matrix {n p : ℕ} {J : Finset ℕ}
    (result : RetryResult n J p) (b : Fin n → TrialWord n J p) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  sturmTridiagonal (fun i => (result.trial.val.diagonal[i.val]).value) (fun e => (b e).value)

section Execution

variable {n p : ℕ} {J : Finset ℕ}
  {a : Fin (n + 1) → TrialWord n J p} {b : Fin n → TrialWord n J p}
  {bits : ℕ → GateBits n J} {result : RetryResult n J p}

theorem retryRun_eq_none_iff : retryRun a b bits = none ↔ ∀ j, bits j ∈ trialRejected n p J a b := by
  classical
  unfold retryRun
  split_ifs with h
  · simp only [false_iff]
    obtain ⟨j, hj⟩ := h
    exact fun hall => by simpa [trialRejected, hj] using hall j
  · simp only [true_iff]
    intro j
    change trialAccepts n p J a b (bits j) = false
    exact Bool.eq_false_iff.mpr fun hj => h ⟨j, hj⟩

/-- The run has returned the same gate result from the first trial that accepts. -/
theorem retryRun_first (h : retryRun a b bits = some result) :
    result.trial.val = trialRun n p J a b (bits result.index) ∧
      (∀ i < result.index, bits i ∈ trialRejected n p J a b) := by
  classical
  unfold retryRun at h
  split_ifs at h with hex
  · obtain rfl := Option.some.inj h
    exact ⟨rfl, fun i hi => Bool.eq_false_iff.mpr (Nat.find_min hex hi)⟩

theorem retryRun_at_first {j : ℕ} (haccept : trialAccepts n p J a b (bits j) = true)
    (hreject : ∀ i < j, bits i ∈ trialRejected n p J a b) :
    ∃ r, retryRun a b bits = some r ∧ r.index = j := by
  classical
  have hex : ∃ i, trialAccepts n p J a b (bits i) = true := ⟨j, haccept⟩
  rw [retryRun, dif_pos hex]
  refine ⟨_, rfl, ?_⟩
  apply le_antisymm (Nat.find_min' hex haccept)
  by_contra! hj
  exact Bool.eq_false_iff.mp (hreject _ hj) (Nat.find_spec hex)

/-- The matrix returned by the retry loop is the matrix certified on that successful trial. -/
theorem retryRun_matrix (h : retryRun a b bits = some result) :
    result.matrix b = trialMatrix a b (bits result.index) := by
  unfold RetryResult.matrix
  rw [(retryRun_first h).1]
  rfl

theorem retryRun_accepts (h : retryRun a b bits = some result) :
    trialAccepts n p J a b (bits result.index) = true := by
  change (trialRun n p J a b (bits result.index)).accepted = true
  rw [← (retryRun_first h).1]
  exact result.trial.property

/-- The return index corresponds to one more attempt than the number of rejections. -/
theorem retryRun_retryCount_eq (h : retryRun a b bits = some result) :
    retryCount (trialRejected n p J a b) bits = (result.index : ℝ≥0∞) + 1 := by
  apply retryCount_eq_of_first_accept (mem_rejectionPrefix.mpr (retryRun_first h).2)
  simp [trialRejected, retryRun_accepts h]

theorem retryRun_count_top_iff :
    retryCount (trialRejected n p J a b) bits = ⊤ ↔ retryRun a b bits = none := by
  rw [retryCount_eq_top_iff, retryRun_eq_none_iff]

/-- A finite run returns almost surely once the actual one-trial rejection bound holds. -/
theorem ae_retryRun_returns
    (hβ : (trialBitLaw (n + 1) J.card).toMeasure (trialRejected n p J a b) ≤
      ENNReal.ofReal (rejectionBound (n + 1))) :
    ∀ᵐ x ∂retryBitMeasure n J, ∃ r, retryRun a b x = some r := by
  have hr : MeasurableSet (trialRejected n p J a b) := (trialRejected n p J a b).to_countable.measurableSet
  have hN : 0 < nextPowerOfTwo (n + 1) := by unfold nextPowerOfTwo; positivity
  have hlt : rejectionBound (n + 1) < 1 / 2 := trialRejectionBound_lt_half hN
  have hβlt : ENNReal.ofReal (rejectionBound (n + 1)) < 1 := by
    rw [← ENNReal.ofReal_one, ENNReal.ofReal_lt_ofReal_iff (by norm_num)]
    linarith
  filter_upwards [ae_exists_accept (trialBitLaw (n + 1) J.card).toMeasure hr (hβ.trans_lt hβlt)]
    with x hx
  cases hrun : retryRun a b x with
  | none => obtain ⟨j, hj⟩ := hx; exact False.elim (hj (retryRun_eq_none_iff.mp hrun j))
  | some r => exact ⟨r, rfl⟩

/-- For the actual accept-first execution, looking at the first `m` bit blocks suffices
for its attempt-count tail. -/
theorem retryRun_attemptTail_le
    (hβ : (trialBitLaw (n + 1) J.card).toMeasure (trialRejected n p J a b) ≤
      ENNReal.ofReal (rejectionBound (n + 1))) (m : ℕ) :
    retryBitMeasure n J {x | (m : ℝ≥0∞) < retryCount (trialRejected n p J a b) x} ≤
      ENNReal.ofReal (rejectionBound (n + 1)) ^ m := by
  have hr : MeasurableSet (trialRejected n p J a b) := (trialRejected n p J a b).to_countable.measurableSet
  rw [measure_retryCount_tail _ hr]
  gcongr

theorem retryRun_attemptExpectation_le
    (hβ : (trialBitLaw (n + 1) J.card).toMeasure (trialRejected n p J a b) ≤
      ENNReal.ofReal (rejectionBound (n + 1))) :
    ((∫⁻ x, retryCount (trialRejected n p J a b) x ∂retryBitMeasure n J) ≤
      ENNReal.ofReal ((1 - rejectionBound (n + 1))⁻¹)) ∧
    ENNReal.ofReal ((1 - rejectionBound (n + 1))⁻¹) < 2 := by
  have hr : MeasurableSet (trialRejected n p J a b) := (trialRejected n p J a b).to_countable.measurableSet
  have hN : 0 < nextPowerOfTwo (n + 1) := by unfold nextPowerOfTwo; positivity
  have hlt : rejectionBound (n + 1) < 1 / 2 := trialRejectionBound_lt_half hN
  have hnonneg : 0 ≤ rejectionBound (n + 1) := (trialRejectionBound_pos hN).le
  have hden : 0 < 1 - rejectionBound (n + 1) := by linarith
  constructor
  · rw [lintegral_retryCount _ hr, ENNReal.ofReal_inv_of_pos hden,
      ENNReal.ofReal_sub _ hnonneg, ENNReal.ofReal_one]
    gcongr
  · rw [← ENNReal.ofReal_ofNat, ENNReal.ofReal_lt_ofReal_iff (by norm_num), ← one_div,
      div_lt_iff₀ hden]
    linarith

end Execution

end NumStability.CertifiedTridiagonalEigenpairs
