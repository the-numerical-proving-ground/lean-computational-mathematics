import ComputationalMathematics.Source.CertifiedTridiagonalEigenpairs.Section06.VectorGuarantee.Target

namespace NumStability.CertifiedTridiagonalEigenpairs

open FloatingPointFormat.UnboundedBinary

private theorem vectorGuarantee_outputPrecision {n p : ℕ} (hn : 2 ≤ n) (hp : 0 < p)
    (h : (n : ℝ) * unitRoundoff p ≤ 1 / 128) : 2 ≤ p := by
  by_contra! hlt
  have hp₁ : p = 1 := by omega
  subst p
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  norm_num [unitRoundoff] at h
  linarith

private theorem vectorGuarantee_workingPrecision {q : ℕ} (hq : 0 < q) {η : ℝ}
    (hη : η ≤ 1 / 2) (h : unitRoundoff q ≤ η / 4096) : 2 ≤ q := by
  by_contra! hlt
  have hq₁ : q = 1 := by omega
  subst q
  norm_num [unitRoundoff] at h
  linarith

private theorem vectorGuarantee_imaginaryArray {n q : ℕ} (hq : 2 ≤ q) (hn : 0 < n)
    (A : Matrix (Fin n) (Fin n) ℝ) (shift η : ℝ) (i : Fin n) :
    ((vectorComputedImaginaryArray hq hn A shift η).get i).value =
      ((vectorCachedExecution q hq n hn (vectorInputDiagonal A shift)
        (vectorInputEdge A) η).column.get i).im := by
  change ((vectorComputedImaginaryArray hq hn A shift η)[i.val]).value = _
  rw [vectorComputedImaginaryArray, Vector.getElem_ofFn, vectorImaginaryWords_value]

theorem vectorGuarantee : SourceTargets.vectorGuarantee := by
  intro n p q hn hp hq A hA j v shift η Δ eigenvalue u ω hAnorm hband hb hAWork hShiftWork
    hv heig hΔ hgap hguard hηpow hnear hη hω
  obtain ⟨hηmax, hηprec⟩ := le_min_iff.mp hη
  obtain ⟨hωη, hωrest⟩ := le_min_iff.mp hω
  obtain ⟨hωΔ, hωn⟩ := le_min_iff.mp hωrest
  have hp₂ := vectorGuarantee_outputPrecision hn hp hguard
  have hq₂ := vectorGuarantee_workingPrecision hq hηmax hωη
  have hAWork₂ (i k : Fin n) : Native q hq₂ (A i k) :=
    (nativeAt_iff_native q hq₂ _).mp (hAWork i k)
  have hShiftWork₂ : Native q hq₂ shift :=
    (nativeAt_iff_native q hq₂ _).mp hShiftWork
  have hgap' (i : Fin n) (hi : i ≠ j.rev) :
      Δ ≤ |(MatrixResolvent.isHermitian_map_ofReal hA).eigenvalues i -
        (MatrixResolvent.isHermitian_map_ofReal hA).eigenvalues j.rev| := by
    have hirev : i.rev ≠ j := fun h => hi (by simpa using congrArg Fin.rev h)
    simpa [eigenvalue] using hgap i.rev hirev
  obtain ⟨hwork, htrace, hspace, hdivs, hx, hnorm, σ, hsign, _, herror⟩ :=
    roundedTridiagonalVectorAccuracyAndWork hn hp₂ hq₂ A hA hAnorm hband hb
      hAWork₂ j.rev v hv heig hShiftWork₂ hηpow hηmax hΔ hguard hηprec hnear hgap'
      hωη hωΔ hωn
  have hn₀ : 0 < n := by omega
  refine ⟨hp₂, hq₂, vectorCachedExecution_root q hq₂ n hn₀ _ _ η,
    vectorGuarantee_imaginaryArray hq₂ hn₀ A shift η, hdivs, ?_,
    hwork, htrace, hspace, hx, hnorm, ?_⟩
  · intro i _
    exact vectorPivotDivisorsPositive_outward hdivs _ i
  · rcases hsign with rfl | rfl
    · exact (min_le_left _ _).trans (by simpa using herror)
    · exact (min_le_right _ _).trans (by simpa using herror)

end NumStability.CertifiedTridiagonalEigenpairs
