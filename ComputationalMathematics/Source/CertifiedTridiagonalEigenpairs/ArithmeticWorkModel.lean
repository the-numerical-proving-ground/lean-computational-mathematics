import ComputationalMathematics.Source.CertifiedTridiagonalEigenpairs.ArithmeticWorkModelTarget

/-! The arithmetic and resource accounting laws for the paper’s scalar model. -/

namespace NumStability.CertifiedTridiagonalEigenpairs

open FloatingPointFormat.UnboundedBinary
open ScalarWork

theorem arithmeticWorkModel : SourceTargets.arithmeticWorkModel := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n p hn hguard
    exact (Nat.le_add_left 7 (Nat.clog 2 n)).trans (clog_add_le_of_precisionGuard hn hguard)
  · intro t ht x
    exact ⟨Word.exists_value_iff_native, roundToEven_nearestRoundingIn t ht x,
      roundToEven_policy_of_ne_zero t ht, abs_roundToEven_sub_le t ht x⟩
  · intro t ht operation
    exact Word.value_round t ht operation.exactValue
  · intro s t hs ht word
    exact Word.value_round t ht word.value
  · intro t ht word k
    exact ⟨word.value_scale k, word.exponent_scale k⟩
  · intro cap trace htrace
    exact ⟨fun bits h => htrace (.arithmetic bits) h,
      fun s t h => htrace (.conversion s t) h, rfl⟩
  · intro liveWords limit
    exact storage_le_iff

end NumStability.CertifiedTridiagonalEigenpairs
