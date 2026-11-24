import ComputationalMathematics.Source.CertifiedTridiagonalEigenpairs.BidiagonalSVDGuarantee.Target
import ComputationalMathematics.Source.CertifiedTridiagonalEigenpairs.BidiagonalSVDRunResources
import ComputationalMathematics.Source.CertifiedTridiagonalEigenpairs.TridiagonalConfidence.Proof

/-! Proof of the selected bidiagonal singular triplet source theorem. -/

namespace NumStability.CertifiedTridiagonalEigenpairs

open FloatingPointFormat.UnboundedBinary BidiagonalSVDRequest
open scoped ENNReal

theorem selectedBidiagonalSingularTriplets : SourceTargets.selectedBidiagonalSingularTriplets := by
  refine ⟨200000, 500, 66000, by decide, by decide, by decide, ?_⟩
  intro n k p hp upper a b I hk hguard d B q plan μ W
  have hkn : k ≤ n + 1 := by
    simpa using Fintype.card_le_of_injective I I.injective
  refine ⟨plan.ae_returns, plan.accuracy, ?_, plan.workspaceBound_le, ?_, rfl, plan.respectsPrecision,
    plan.precision_le.2.1, fun hn => svdWorkingPrecision_le hn hkn hguard, ?_⟩
  · simpa only [d, ← mul_assoc] using plan.expectation_work_le
  · intro c hc
    rw [manuscriptWorkCutoff_polynomial _ _ _ _ hc]
    simpa only [d, μ, W, Nat.cast_succ, ← mul_assoc] using plan.work_confidence c hc
  · intro he
    have hs := (bidiagonalExactBranch_isSome_iff upper a b I).mpr he
    cases hexact : bidiagonalExactBranch a b I with
    | none => simp [hexact] at hs
    | some exactOut =>
      have hplan : plan = RunPlan.exact exactOut hexact := by
        dsimp only [plan]
        unfold prepareRun
        split
        · rename_i out h
          rw [hexact] at h
          cases Option.some.inj h
          rfl
        · rename_i h
          rw [hexact] at h
          cases h
      rw [hplan]
      exact ⟨rfl, exactOut, rfl, fun _ => rfl⟩

end NumStability.CertifiedTridiagonalEigenpairs
