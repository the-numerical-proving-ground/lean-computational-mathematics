import ComputationalMathematics.Source.CertifiedTridiagonalEigenpairs.InputPrecisionTarget

namespace NumStability.CertifiedTridiagonalEigenpairs

open FloatingPointFormat.UnboundedBinary NoisyRankCertificate

private theorem ceil_nat_div_four (m : ℕ) : ⌈(m : ℝ) / 4⌉₊ = (m + 3) / 4 := by
  apply Nat.le_antisymm
  · apply Nat.ceil_le.mpr
    rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 4)]
    exact_mod_cast (show m ≤ (m + 3) / 4 * 4 by omega)
  · by_contra! h
    have hm := Nat.le_ceil ((m : ℝ) / 4)
    have hm' : m ≤ ⌈(m : ℝ) / 4⌉₊ * 4 := by
      exact_mod_cast (show (m : ℝ) ≤ (↑⌈(m : ℝ) / 4⌉₊ : ℝ) * 4 by linarith)
    omega

/-- The tridiagonal input and output conventions and the bounds in main:precision. -/
theorem tridiagonalInputPrecision : SourceTargets.tridiagonalInputPrecision := by
  intro n p hp a b J hJ hJnonempty hguard
  dsimp only
  have hlog (m : ℕ) : ⌈Real.logb 2 (m : ℝ)⌉₊ = Nat.clog 2 m := by
    simpa using Real.natCeil_logb_natCast 2 m
  rw [hlog (n + 1), hlog J.card]
  have hk : 1 ≤ J.card := Finset.card_pos.mpr hJnonempty
  have hkn : J.card ≤ n + 1 := by
    simpa using Fintype.card_le_of_injective (requestedRankOrder hJ)
      (requestedRankOrder hJ).injective
  obtain ⟨hq, hq'⟩ := workingPrecision_bounds hk hkn hguard
  refine ⟨hk, hkn, ascendingEigenvalue_monotone _, roots_charpoly_eq_ascendingEigenvalues _,
    (requestedRankOrder hJ).strictMono, requestedRankOrder_covers hJ, rfl, rfl,
    ?_, rfl, rfl, clog_le_sub_of_precisionGuard (Nat.succ_pos n) hguard,
    Nat.clog_mono_right 2 hkn, hq, hq', ?_⟩
  · rw [ceil_nat_div_four]
    rfl
  · intro out
    cases out with
    | exact out _ =>
        exact ⟨fun i => (out.labels i).native_value, fun j i => (out.columns j i).native_value⟩
    | refined out =>
        exact ⟨fun i => (out.pairs.get i).label.native_value,
          fun j i => ((out.pairs.get i).column.get j).native_value⟩

end NumStability.CertifiedTridiagonalEigenpairs
