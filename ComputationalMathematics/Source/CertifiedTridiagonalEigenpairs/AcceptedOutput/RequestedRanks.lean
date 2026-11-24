import ComputationalMathematics.Source.CertifiedTridiagonalEigenpairs.AcceptedLabels.Target
import Mathlib.Data.Finset.Sort

/-! The requested rank order obtained by one scan of the marked ranks. -/

namespace NumStability.CertifiedTridiagonalEigenpairs

private theorem markedRank_read {N : ℕ} (flags : Vector Bool N) (r : ℕ) (i : Fin N) :
    (markTrialRank flags r)[i.val] = (decide (r = i.val + 1) || flags[i.val]) := by
  have hi := i.isLt
  by_cases h : 1 ≤ r ∧ r ≤ N
  · rw [markTrialRank, dif_pos h, Vector.getElem_set]
    have he : r - 1 = i.val ↔ r = i.val + 1 := by omega
    by_cases heq : r = i.val + 1
    · simp [heq]
    · simp [heq, mt he.mp heq]
  · have hne : r ≠ i.val + 1 := by omega
    simp [markTrialRank, h, hne]

private theorem markedRanks_read {N : ℕ} (ranks : List ℕ) (flags : Vector Bool N)
    (i : Fin N) :
    (ranks.foldl markTrialRank flags)[i.val] = true ↔ i.val + 1 ∈ ranks ∨ flags[i.val] = true := by
  induction ranks generalizing flags with
  | nil => simp
  | cons r rest ih =>
    simp only [List.foldl_cons, ih, markedRank_read, Bool.or_eq_true, decide_eq_true_eq,
      List.mem_cons]
    grind

/-- Mark the requested ranks and scan increasing indices, omitting unmarked indices. -/
noncomputable def requestedRankScan (n : ℕ) (J : Finset ℕ) : List (Fin (n + 1)) :=
  let flags := trialRequestedFlags (n + 1) J
  (List.finRange (n + 1)).filter fun j => flags[j.val]

@[simp] theorem mem_requestedRankScan {n : ℕ} {J : Finset ℕ} {i : Fin (n + 1)} :
    i ∈ requestedRankScan n J ↔ i.val + 1 ∈ J := by
  simp [requestedRankScan, trialRequestedFlags, markedRanks_read]

theorem requestedRankScan_pairwise (n : ℕ) (J : Finset ℕ) :
    (requestedRankScan n J).Pairwise (· < ·) :=
  List.pairwise_filter.mpr ((List.pairwise_lt_finRange (n + 1)).imp fun h _ _ => h)

theorem requestedRankScan_length {n : ℕ} {J : Finset ℕ} (hJ : J ⊆ Finset.Icc 1 (n + 1)) :
    (requestedRankScan n J).length = J.card := by
  let ranks := (requestedRankScan n J).map (fun i => i.val + 1)
  have hranks : ranks.toFinset = J := by
    ext r
    simp only [ranks, List.mem_toFinset, List.mem_map, mem_requestedRankScan]
    constructor
    · rintro ⟨i, hi, rfl⟩
      exact hi
    · intro hr
      have ⟨hl, hu⟩ := Finset.mem_Icc.mp (hJ hr)
      let i : Fin (n + 1) := ⟨r - 1, by omega⟩
      have heq : i.val + 1 = r := by dsimp [i]; omega
      exact ⟨i, heq ▸ hr, heq⟩
  have hnodup : ranks.Nodup := by
    apply List.Nodup.map
    swap
    · exact (requestedRankScan_pairwise n J).imp fun h => ne_of_lt h
    intro i j h
    exact Fin.ext (Nat.add_right_cancel h)
  calc
    _ = ranks.length := by simp [ranks]
    _ = J.card := by rw [← List.toFinset_card_of_nodup hnodup, hranks]

/-- Materialize the scan in an array so each requested rank is read by direct indexing. -/
noncomputable def requestedRankArray {n : ℕ} (J : Finset ℕ)
    (hJ : J ⊆ Finset.Icc 1 (n + 1)) : Vector (RequestedTrialRank n J) J.card :=
  ⟨((requestedRankScan n J).attachWith _ (fun _ h => mem_requestedRankScan.mp h)).toArray,
    by simp [requestedRankScan_length hJ]⟩

theorem requestedRankArray_get_val {n : ℕ} {J : Finset ℕ}
    (hJ : J ⊆ Finset.Icc 1 (n + 1)) (i : Fin J.card) :
    ((requestedRankArray J hJ).get i).val =
      (requestedRankScan n J).get (Fin.cast (requestedRankScan_length hJ).symm i) := by
  simp [requestedRankArray, Vector.get]

/-- The increasing embedding given by the stored requested rank array. -/
noncomputable def requestedRankOrder {n : ℕ} {J : Finset ℕ}
    (hJ : J ⊆ Finset.Icc 1 (n + 1)) : Fin J.card ↪o Fin (n + 1) :=
  OrderEmbedding.ofStrictMono (fun i => ((requestedRankArray J hJ).get i).val) fun i j hij => by
    change ((requestedRankArray J hJ).get i).val < ((requestedRankArray J hJ).get j).val
    rw [requestedRankArray_get_val, requestedRankArray_get_val]
    exact (requestedRankScan_pairwise n J).rel_get_of_lt hij

@[simp] theorem requestedRankOrder_apply {n : ℕ} {J : Finset ℕ}
    (hJ : J ⊆ Finset.Icc 1 (n + 1)) (i : Fin J.card) :
    requestedRankOrder hJ i = ((requestedRankArray J hJ).get i).val := rfl

/-- The scan contains every requested rank exactly once, by strict monotonicity. -/
theorem requestedRankOrder_covers {n : ℕ} {J : Finset ℕ}
    (hJ : J ⊆ Finset.Icc 1 (n + 1)) (j : Fin (n + 1)) :
    (∃ i, requestedRankOrder hJ i = j) ↔ j.val + 1 ∈ J := by
  constructor
  · rintro ⟨i, rfl⟩
    exact ((requestedRankArray J hJ).get i).property
  · intro hj
    obtain ⟨i, hi⟩ := List.mem_iff_get.mp (mem_requestedRankScan.mpr hj)
    refine ⟨Fin.cast (requestedRankScan_length hJ) i, ?_⟩
    rw [requestedRankOrder_apply, requestedRankArray_get_val]
    simpa using hi

end NumStability.CertifiedTridiagonalEigenpairs
