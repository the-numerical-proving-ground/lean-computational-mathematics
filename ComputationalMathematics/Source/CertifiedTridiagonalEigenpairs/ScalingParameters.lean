import ComputationalMathematics.Source.CertifiedTridiagonalEigenpairs.ScalingParametersTarget
import ComputationalMathematics.Source.CertifiedTridiagonalEigenpairs.FiniteTrial.Proof

namespace NumStability.CertifiedTridiagonalEigenpairs

open FloatingPointFormat.UnboundedBinary ScalarWork

private theorem ceil_nat_div_two (m : ℕ) : ⌈(m : ℝ) / 2⌉₊ = (m + 1) / 2 := by
  apply Nat.le_antisymm
  · apply Nat.ceil_le.mpr
    rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 2)]
    exact_mod_cast (show m ≤ (m + 1) / 2 * 2 by omega)
  · by_contra! h
    have hm := Nat.le_ceil ((m : ℝ) / 2)
    have hm' : m ≤ ⌈(m : ℝ) / 2⌉₊ * 2 := by
      exact_mod_cast (show (m : ℝ) ≤ (↑⌈(m : ℝ) / 2⌉₊ : ℝ) * 2 by linarith)
    omega

private theorem rankFlagMarkTrace_work (N rank : ℕ) :
    work (rankFlagMarkTrace N rank) ≤ 4 := by
  unfold rankFlagMarkTrace
  split <;> norm_num [work]

private theorem work_flatMap_le {α : Type} (items : List α) (trace : α → List Step)
    (bound : ℕ) (h : ∀ x, work (trace x) ≤ bound) :
    work (items.flatMap trace) ≤ items.length * bound := by
  induction items with
  | nil => simp [work]
  | cons item rest ih =>
    have hitem := h item
    simp only [List.flatMap_cons, work, List.length_append, List.length_cons, Nat.add_mul] at *
    omega

private theorem rankFlagTrace_work (N : ℕ) (J : Finset ℕ) :
    work (rankFlagTrace N J) ≤ 19 * (N + J.card) := by
  unfold rankFlagTrace
  simp only [work, List.length_append, List.length_replicate]
  have hmarks := work_flatMap_le J.toList
    (fun rank => [Step.index, .index, .index] ++ rankFlagMarkTrace N rank ++
      rankFlagMarkTrace N rank ++ rankFlagMarkTrace N (rank - 1) ++
      rankFlagMarkTrace N (rank + 1)) 19 (by
    intro rank
    have hcurrent := rankFlagMarkTrace_work N rank
    have hprev := rankFlagMarkTrace_work N (rank - 1)
    have hnext := rankFlagMarkTrace_work N (rank + 1)
    simp only [work, List.length_append, List.length_cons, List.length_nil] at *
    omega)
  have hscans := work_flatMap_le (List.finRange N)
    (fun (i : Fin N) => [Step.index, .index, .comparison, .comparison] ++
      (if (trialRequestedFlags N J)[i.val] then [.index] else []) ++
      (if (trialNeighborFlags N J)[i.val] then [.index] else [])) 6 (by
    intro i
    dsimp only
    split <;> split <;> norm_num [work])
  simp only [work, Finset.length_toList, List.length_finRange] at hmarks hscans
  omega

private theorem largestStoredEntry_singleton {p : ℕ} {hp : 2 ≤ p} (word : Word p hp) :
    largestStoredEntry (n := 0) (fun _ => word) Fin.elim0 = word := by
  cases word <;> rfl

private theorem neighbor_card_le (N : ℕ) (J : Finset ℕ) :
    (requestedNeighborRanks N J).card ≤ 3 * J.card := by
  unfold requestedNeighborRanks
  have hsub := Finset.card_le_card (Finset.inter_subset_left
    (s₁ := J ∪ J.image (· - 1) ∪ J.image (· + 1)) (s₂ := Finset.Icc 1 N))
  have hu := Finset.card_union_le (J ∪ J.image (· - 1)) (J.image (· + 1))
  have hv := Finset.card_union_le J (J.image (· - 1))
  have hleft : (J.image (· - 1)).card ≤ J.card := Finset.card_image_le
  have hright : (J.image (· + 1)).card ≤ J.card := Finset.card_image_le
  omega

/-- The setup formulas, exact scaling bounds, and ordered flag scans of §3.1. -/
theorem tridiagonalScalingParameters : SourceTargets.tridiagonalScalingParameters := by
  intro n p hp a b J _hn hnonzero _hJnonempty _hJvalid _hguard
  dsimp only
  obtain ⟨hscanWork, hscanAllowed, hscanSpace⟩ := runNormalizationScan_resources a b
  refine ⟨?_, abs_entry_le_largestStoredEntry a b, hscanWork, hscanAllowed, hscanSpace,
    ?_, rfl, rfl, gapScale_eq_scaled _ _ _, rfl, rfl, rfl, rfl, ?_, rfl, ?_, ?_,
    neighbor_card_le _ _, fun _ => mem_requestedRankScan, mem_trialRanks,
    requestedRankScan_pairwise _ _, ?_, rankFlagTrace_work _ _⟩
  · obtain ⟨i, j, h⟩ := largestStoredEntry_attained a b
    exact ⟨i, j, h.symm⟩
  · have hnone : normalizationExponent a b ≠ none :=
      mt (normalizationExponent_eq_none_iff a b).mp hnonzero
    cases he : coveringExponent (largestStoredEntry a b) with
    | none => simp [normalizationExponent, he] at hnone
    | some e =>
        have hr : normalizationExponent a b = some (e + 2) := by
          simp [normalizationExponent, he]
        obtain ⟨hentry, hnorm, hrow, hR⟩ := normalizedTridiagonal_bounds a b hr
        have hcover : (runNormalizationScan (n := 0)
            (fun _ => largestStoredEntry a b) Fin.elim0).exponent = some (e + 2) := by
          simp [runNormalizationScan_exponent, normalizationExponent,
            largestStoredEntry_singleton, he]
        refine ⟨e, e + 2, rfl, (runNormalizationScan_exponent a b).trans hr,
          hcover, ?_, (coveringExponent_bounds he).2, ?_, ?_, normalizedTridiagonal_eq a b _,
          ?_, hentry, hnorm, hrow, hR⟩
        · exact (runNormalizationScan_resources (n := 0)
            (fun _ => largestStoredEntry a b) Fin.elim0).1
        · intro l hl
          exact zpow_le_zpow_right₀ (by norm_num) ((coveringExponent_least he l).mp hl)
        · rw [zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
          norm_num [mul_comm]
        · simpa [Vector.get] using normalizedTrialMatrix_eq (J := J) a b (e + 2)
  · rw [ceil_nat_div_two]
    rfl
  · intro x hx
    have hdyadic {z : ℝ} {m : ℕ} (hz : z = unitRoundoff m) : ∃ e : ℤ, z = (2 : ℝ) ^ e :=
      ⟨-(m : ℤ), hz⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hdyadic (perturbationScale_eq_roundoff _)
    · exact hdyadic (gapScale_eq_roundoff _ _ _)
    · exact hdyadic (certifiedGap_eq_roundoff _ _ _)
    · exact hdyadic (gapLabelError_eq_roundoff _ _ _)
    · exact hdyadic (gapTolerance_eq_roundoff _ _ _)
    · exact hdyadic (vectorTolerance_eq_roundoff _ _ _)
    · exact hdyadic rfl
  · intro j
    simp only [requestedNeighborRanks, Finset.mem_inter, Finset.mem_union, Finset.mem_image]
    constructor
    · rintro ⟨(hj | ⟨i, hi, rfl⟩) | ⟨i, hi, rfl⟩, hjvalid⟩
      · exact ⟨hjvalid, j, hj, Or.inr (Or.inl rfl)⟩
      · exact ⟨hjvalid, i, hi, Or.inl rfl⟩
      · exact ⟨hjvalid, i, hi, Or.inr (Or.inr rfl)⟩
    · rintro ⟨hjvalid, i, hi, rfl | rfl | rfl⟩
      · exact ⟨Or.inl (Or.inr ⟨i, hi, rfl⟩), hjvalid⟩
      · exact ⟨Or.inl (Or.inl hi), hjvalid⟩
      · exact ⟨Or.inr ⟨i, hi, rfl⟩, hjvalid⟩
  · exact List.pairwise_filter.mpr ((List.pairwise_lt_finRange (n + 1)).imp fun h _ _ => h)

end NumStability.CertifiedTridiagonalEigenpairs
