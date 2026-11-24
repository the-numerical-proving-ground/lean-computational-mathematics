import ComputationalMathematics.Source.CertifiedTridiagonalEigenpairs.CertifiedSturmCountTarget

/-!
# Proof of the certified Sturm count

The clipped rounded pivots satisfy an exact recurrence for a perturbed
symmetric tridiagonal. The perturbation is bounded by `13 * 2⁻ᵠ + 2s` in
operator norm. Exact inertia and Weyl's inequality transfer the count to
the two strict spectral endpoints.
-/

namespace NumStability.CertifiedTridiagonalEigenpairs

open FloatingPointFormat.UnboundedBinary

theorem certifiedSturmCount : SourceTargets.certifiedSturmCount := by
  unfold SourceTargets.certifiedSturmCount
  intro n r q hq a b x
  dsimp only
  intro _ hprec hH hb hx
  let av : Fin (n + 1) → ℝ := fun i => (a i).value
  let bv : Fin n → ℝ := fun i => (b i).value
  let d := clippedSturmPivots q hq r av bv x.value
  have hxabs : |x.value| ≤ 2 := abs_le.mpr hx
  have ha (i : Fin (n + 1)) : |av i - x.value| ≤ 4 := by
    have hai := (sturmTridiagonal_abs_diagonal_le_operatorNorm av bv i).trans hH
    exact (abs_sub _ _).trans (by linarith)
  have hd (i : Fin (n + 1)) : d i ≠ 0 := clippedSturmPivots_ne_zero av bv x.value i
  obtain ⟨a', b', ha', hb', hzero, hsucc⟩ :=
    clippedSturmPivots_backwardWitness q hq r av bv x.value ha hb
  have hD : 0 ≤ 9 * unitRoundoff q + 2 * sturmClipThreshold r := by
    linarith [unitRoundoff_pos q, sturmClipThreshold_pos r]
  have hE : 0 ≤ 2 * unitRoundoff q := by linarith [unitRoundoff_pos q]
  have hbudget : (9 * unitRoundoff q + 2 * sturmClipThreshold r) + 2 * (2 * unitRoundoff q) ≤
      unitRoundoff r := by
    linarith [sturmBackwardError_lt hprec, unitRoundoff_pos r]
  have hbracket := sturmBackwardRecurrence_count_bracket d av a' bv b' x.value
    hd ⟨hzero, hsucc⟩ hD hE ha' hb' hbudget
  have hcount := clippedSturmSweep_count q hq r a b x
  rw [← hcount] at hbracket
  obtain ⟨hwork, hallowed⟩ := clippedSturmSweep_work q hq r a b x
  exact ⟨fun i => ⟨clippedSturmPivots_native av bv x.value i,
      sturmClipThreshold_le_abs_pivots av bv x.value i, hd i⟩,
    hcount, hbracket.1, hbracket.2, hwork, hallowed, clippedSturmSweep_storage q hq r a b x⟩

end NumStability.CertifiedTridiagonalEigenpairs
