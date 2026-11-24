import ComputationalMathematics.Source.CertifiedTridiagonalEigenpairs.ExactBranchExecution
import ComputationalMathematics.Source.CertifiedTridiagonalEigenpairs.AcceptedOutput.WholeRunWork

/-! The exact branches have a deterministic cost on the same scale as the normalized run. -/

open MeasureTheory
open scoped ENNReal

namespace NumStability.CertifiedTridiagonalEigenpairs

open ScalarWork FloatingPointFormat.UnboundedBinary

variable {n p : ℕ} {J : Finset ℕ} {hp : 2 ≤ p}

/-- Cost of the observed exact-branch scan, dispatch and explicit output. -/
noncomputable def exactEigenpairWork (a : Fin (n + 1) → Word p hp) (b : Fin n → Word p hp)
    (hJvalid : J ⊆ Finset.Icc 1 (n + 1)) : ℝ≥0∞ :=
  (work (runExactBranch a b (requestedRankOrder hJvalid)).trace : ℝ≥0∞)

theorem exactEigenpairWork_le (a : Fin (n + 1) → Word p hp) (b : Fin n → Word p hp)
    (hJ : J.Nonempty) (hJvalid : J ⊆ Finset.Icc 1 (n + 1)) :
    exactEigenpairWork a b hJvalid ≤ (retryTrialWorkScale n J p : ℝ≥0∞) := by
  have h := (runExactBranch_work a b (requestedRankOrder hJvalid) (Finset.card_pos.mpr hJ)).1
  apply Nat.cast_le.mpr (h.trans ?_)
  unfold retryTrialWorkScale
  calc
    _ ≤ 4000 * ((n + 1) * J.card) := Nat.mul_le_mul_right _ (by decide)
    _ ≤ 4000 * ((n + 1) * J.card) * p := Nat.le_mul_of_pos_right _ (by omega)
    _ = _ := by ring

theorem exactEigenpairWork_expectation_tail (a : Fin (n + 1) → Word p hp) (b : Fin n → Word p hp)
    (hJ : J.Nonempty) (hJvalid : J ⊆ Finset.Icc 1 (n + 1)) :
    (∫⁻ _ : ℕ → GateBits n J, exactEigenpairWork a b hJvalid ∂retryBitMeasure n J) ≤
      3 * (retryTrialWorkScale n J p : ℝ≥0∞) ∧
    ∀ m : ℕ, retryBitMeasure n J
      {_bits | (retryTrialWorkScale n J p : ℝ≥0∞) * ((m : ℝ≥0∞) + 1) < exactEigenpairWork a b hJvalid} = 0 := by
  have hb := exactEigenpairWork_le a b hJ hJvalid
  constructor
  · rw [lintegral_const, measure_univ, mul_one]
    refine hb.trans ?_
    simpa only [one_mul] using
      (mul_le_mul_left (show (1 : ℝ≥0∞) ≤ 3 from by norm_num) (retryTrialWorkScale n J p : ℝ≥0∞))
  · intro m
    have hm : (1 : ℝ≥0∞) ≤ (m : ℝ≥0∞) + 1 := by simp
    have hle := hb.trans (by simpa only [mul_one] using
      (mul_le_mul_right hm (retryTrialWorkScale n J p : ℝ≥0∞)))
    suffices {_bits : ℕ → GateBits n J |
        (retryTrialWorkScale n J p : ℝ≥0∞) * ((m : ℝ≥0∞) + 1) < exactEigenpairWork a b hJvalid} = ∅ by
      rw [this, measure_empty]
    exact Set.eq_empty_iff_forall_notMem.mpr fun _ => not_lt_of_ge hle

/-- Exact-branch work satisfies both confidence thresholds with probability one. -/
theorem exactEigenpairWork_confidence (a : Fin (n + 1) → Word p hp) (b : Fin n → Word p hp)
    (hJ : J.Nonempty) (hJvalid : J ⊆ Finset.Icc 1 (n + 1)) (m : ℕ) :
    retryBitMeasure n J
      {_bits | exactEigenpairWork a b hJvalid ≤ (retryTrialWorkScale n J p : ℝ≥0∞) * ((m : ℝ≥0∞) + 1)} = 1 := by
  have hb := exactEigenpairWork_le a b hJ hJvalid
  have hm : (1 : ℝ≥0∞) ≤ (m : ℝ≥0∞) + 1 := by simp
  have hle := hb.trans (by simpa only [mul_one] using
    (mul_le_mul_right hm (retryTrialWorkScale n J p : ℝ≥0∞)))
  suffices {_bits : ℕ → GateBits n J |
      exactEigenpairWork a b hJvalid ≤ (retryTrialWorkScale n J p : ℝ≥0∞) * ((m : ℝ≥0∞) + 1)} = Set.univ by
    rw [this, measure_univ]
  exact Set.eq_univ_of_forall fun _ => hle

end NumStability.CertifiedTridiagonalEigenpairs
