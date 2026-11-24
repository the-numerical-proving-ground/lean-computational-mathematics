import ComputationalMathematics.Source.CertifiedTridiagonalEigenpairs.BidiagonalSVDOracleParities

/-!
# Native signed ranks and parity positions

Negative requests occupy the first block in reverse original order. Positive
requests occupy the second block in original order. A single indexed traversal
of the negative block fills its inverse lookup table in original slot order.
-/

namespace NumStability.CertifiedTridiagonalEigenpairs.BidiagonalSVDRequest

open ScalarWork FloatingPointFormat.UnboundedBinary

variable {n k p : ℕ}

private def selectLow (low : Fin k → Bool) (j : Fin k) : Option {i : Fin k // low i = true} :=
  if h : low j = true then some ⟨j, h⟩ else none

private theorem selectLow_val {low : Fin k → Bool} {i : Fin k} {j : {i // low i = true}}
    (h : selectLow low i = some j) : i = j.val := by
  unfold selectLow at h
  split at h
  · exact congrArg Subtype.val (Option.some.inj h)
  · contradiction

/-- Low slots in the order of their negative oracle ranks. -/
def negativeSlots (low : Fin k → Bool) : List {j : Fin k // low j = true} :=
  (List.ofFn (fun j : Fin k => j.rev)).filterMap (selectLow low)

private theorem mem_negativeSlots (low : Fin k → Bool) (j : {i // low i = true}) :
    j ∈ negativeSlots low := by
  rw [negativeSlots, List.mem_filterMap]
  exact ⟨j.val, List.mem_ofFn.mpr ⟨j.val.rev, j.val.rev_rev⟩, dif_pos j.property⟩

private theorem negativeSlots_descending (low : Fin k → Bool) :
    (negativeSlots low).Pairwise (fun x y => y.val < x.val) := by
  rw [negativeSlots, List.pairwise_filterMap, List.pairwise_ofFn]
  intro i j hij x hx y hy
  rw [← selectLow_val hx, ← selectLow_val hy]
  exact Fin.rev_lt_rev.mpr hij

/-- The two signed blocks are already in the oracle's ascending rank order. -/
def nativeSources (low : Fin k → Bool) : List (Column low) :=
  (negativeSlots low).map Sum.inr ++ List.ofFn Sum.inl

@[simp] theorem mem_nativeSources (low : Fin k → Bool) (j : Column low) :
    j ∈ nativeSources low := by
  cases j with
  | inl j => exact List.mem_append_right _ (List.mem_ofFn.mpr ⟨j, rfl⟩)
  | inr j => exact List.mem_append_left _ (List.mem_map_of_mem (mem_negativeSlots low j))

namespace TridiagonalCall

/-- Ascending one-based request rank array, computed without comparison sorting. -/
def nativeRankList (call : TridiagonalCall n k p) : List ℕ :=
  (nativeSources call.low).map fun j => (rank call.slots call.low j).val + 1

def nativeRankArray (call : TridiagonalCall n k p) : Array ℕ := call.nativeRankList.toArray

private theorem nativeRankList_sorted (call : TridiagonalCall n k p) (hI : StrictMono call.slots) :
    call.nativeRankList.Pairwise (· < ·) := by
  unfold nativeRankList nativeSources
  rw [List.map_append, List.map_map, ← List.ofFn_comp', List.pairwise_append]
  refine ⟨(negativeSlots_descending call.low).map _ ?_, List.pairwise_ofFn.mpr ?_, ?_⟩
  · intro i j hij
    show (call.slots i.val).rev.val + 1 < (call.slots j.val).rev.val + 1
    exact Nat.add_lt_add_right (Fin.rev_lt_rev.mpr (hI hij)) _
  · intro i j hij
    show n + 1 + (call.slots i).val + 1 < n + 1 + (call.slots j).val + 1
    exact Nat.add_lt_add_right (Nat.add_lt_add_left (hI hij) _) _
  · intro a ha b hb
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp ha
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hb
    show (call.slots i.val).rev.val + 1 < n + 1 + (call.slots j).val + 1
    have h := (call.slots i.val).rev.isLt
    omega

@[simp] theorem mem_nativeRankList (call : TridiagonalCall n k p) (r : ℕ) :
    r ∈ call.nativeRankList ↔ r ∈ call.oneBasedRanks := by
  rw [nativeRankList, List.mem_map, TridiagonalCall.oneBasedRanks, Finset.mem_map]
  constructor
  · rintro ⟨j, _, rfl⟩
    exact ⟨_, Finset.mem_map.mpr ⟨j, Finset.mem_univ _, rfl⟩, rfl⟩
  · rintro ⟨i, hi, hr⟩
    obtain ⟨j, _, rfl⟩ := Finset.mem_map.mp hi
    exact ⟨j, mem_nativeSources _ _, hr⟩

/-- The stored rank array enumerates exactly the ranks the solver consumes. -/
theorem nativeRankList_eq (call : TridiagonalCall n k p) (hI : StrictMono call.slots) :
    call.nativeRankList = List.ofFn (fun j : Fin call.oneBasedRanks.card =>
      (requestedRankOrder call.oneBasedRanks_subset j).val + 1) := by
  let s := fun j : Fin call.oneBasedRanks.card =>
    (requestedRankOrder call.oneBasedRanks_subset j).val + 1
  have h₁ := nativeRankList_sorted call hI
  have h₂ : (List.ofFn s).Pairwise (· < ·) := List.pairwise_ofFn.mpr fun _ _ hij =>
    Nat.add_lt_add_right ((requestedRankOrder call.oneBasedRanks_subset).strictMono hij) 1
  have hp : call.nativeRankList.Perm (List.ofFn s) := by
    apply (List.perm_ext_iff_of_nodup (h₁.imp fun h => ne_of_lt h)
      (h₂.imp fun h => ne_of_lt h)).mpr
    intro r
    rw [mem_nativeRankList, List.mem_ofFn]
    constructor
    · intro hr
      have hbound := Finset.mem_Icc.mp (call.oneBasedRanks_subset hr)
      let i : Fin (edgeCount n + 1) := ⟨r - 1, by omega⟩
      have he : i.val + 1 = r := by dsimp [i]; omega
      obtain ⟨j, hj⟩ := (requestedRankOrder_covers call.oneBasedRanks_subset i).mpr (he ▸ hr)
      exact ⟨j, by simp only [s, hj, he]⟩
    · rintro ⟨j, rfl⟩
      exact (requestedRankOrder_covers call.oneBasedRanks_subset _).mp ⟨j, rfl⟩
  exact hp.eq_of_pairwise' h₁ h₂

theorem nativeRankArray_size (call : TridiagonalCall n k p) (hI : StrictMono call.slots) :
    call.nativeRankArray.size = call.oneBasedRanks.card := by
  simp [nativeRankArray, nativeRankList_eq call hI]

end TridiagonalCall

private def inverseScan {k : ℕ} (entries : List (Fin k × ℕ)) (acc : Array ℕ) : Array ℕ :=
  match entries with
  | [] => acc
  | (j, i) :: rest => inverseScan rest (acc.setIfInBounds j.val i)

private theorem inverseScan_size {k : ℕ} (entries : List (Fin k × ℕ)) (acc : Array ℕ) :
    (inverseScan entries acc).size = acc.size := by
  induction entries generalizing acc with
  | nil => rfl
  | cons e rest ih =>
    obtain ⟨j, i⟩ := e
    simp only [inverseScan, ih, Array.size_setIfInBounds]

private theorem inverseScan_read {k : ℕ} (entries : List (Fin k × ℕ)) (acc : Array ℕ)
    (h : ∀ e ∈ entries, e.1.val ≠ j) :
    (inverseScan entries acc)[j]? = acc[j]? := by
  induction entries generalizing acc with
  | nil => rfl
  | cons e es ih =>
    obtain ⟨i, p⟩ := e
    rw [inverseScan, ih (acc.setIfInBounds i.val p) (fun e he => h e (List.mem_cons_of_mem _ he))]
    exact Array.getElem?_setIfInBounds_ne (h _ List.mem_cons_self)

private theorem inverseScan_get {k : ℕ} (entries : List (Fin k × ℕ)) (acc : Array ℕ)
    (hacc : acc.size = k) (h : entries.Pairwise fun e f => e.1 ≠ f.1)
    (j : Fin k) (q : ℕ) (hj : (j, q) ∈ entries) :
    (inverseScan entries acc)[j.val]? = some q := by
  induction entries generalizing acc with
  | nil => simp at hj
  | cons e es ih =>
    obtain ⟨i, p⟩ := e
    rw [List.pairwise_cons] at h
    rcases List.mem_cons.mp hj with he | hr
    · cases he
      rw [inverseScan, inverseScan_read]
      · exact Array.getElem?_setIfInBounds_self_of_lt (by simp [hacc, j.isLt])
      · intro e he heq
        exact h.1 _ he (Fin.ext heq.symm)
    · exact ih _ (by simpa using hacc) h.2 hr

/-- A fixed-size inverse table for the low negative requests. The unused
entries belong to high slots and are never read. -/
def negativeLookup (low : Fin k → Bool) : Array ℕ :=
  inverseScan (((negativeSlots low).zipIdx).map fun (j, i) => (j.val, i)) (Array.replicate k 0)

private theorem negativeLookup_size (low : Fin k → Bool) : (negativeLookup low).size = k := by
  simp [negativeLookup, inverseScan_size]

/-- Position of the positive column in the actual native oracle return. -/
def nativeLeftSlot (low : Fin k → Bool) (j : Fin k) : ℕ :=
  (negativeSlots low).length + j.val

/-- All right positions are computed using the precomputed inverse table. -/
def nativeRightArray (low : Fin k → Bool) : Array ℕ :=
  let inv := negativeLookup low
  let l := (negativeSlots low).length
  (List.ofFn fun j : Fin k => if low j then
    inv[j.val]'(by simpa only [inv, negativeLookup_size] using j.isLt)
  else l + j.val).toArray

private theorem indexed_keys_distinct {α : Type} (key : α → Fin k) (xs : List α)
    (h : xs.Pairwise fun a b => key a ≠ key b) (q : ℕ) :
    ((xs.zipIdx q).map fun (a, i) => (key a, i)).Pairwise fun a b => a.1 ≠ b.1 := by
  induction xs generalizing q with
  | nil => simp
  | cons x xs ih =>
    simp only [List.zipIdx_cons, List.map_cons, List.pairwise_cons] at h ⊢
    constructor
    · rintro _ hz
      obtain ⟨z, hz', he⟩ := List.mem_map.mp hz
      rw [← he]
      exact h.1 _ (List.fst_mem_of_mem_zipIdx hz')
    · exact ih h.2 _

private theorem negativeLookup_get (low : Fin k → Bool) (j : {j // low j = true})
    (i : ℕ) (hi : (negativeSlots low)[i]? = some j) :
    (negativeLookup low)[j.val.val]? = some i := by
  apply inverseScan_get _ _ (by simp)
  · exact indexed_keys_distinct Subtype.val _ ((negativeSlots_descending low).imp
      fun h => (ne_of_lt h).symm) 0
  · exact List.mem_map.mpr ⟨(j, i), List.mk_mem_zipIdx_iff_getElem?.mpr hi, rfl⟩

private theorem positiveSource_get (low : Fin k → Bool) (j : Fin k) :
    (nativeSources low)[nativeLeftSlot low j]? = some (Sum.inl j) := by
  unfold nativeSources nativeLeftSlot
  rw [List.getElem?_append_right (by simp), List.length_map, Nat.add_sub_cancel_left]
  simp [j.isLt]

private theorem negativeSource_get (low : Fin k → Bool) (j : {j // low j = true}) (i : ℕ)
    (hi : (negativeSlots low)[i]? = some j) :
    (nativeSources low)[i]? = some (Sum.inr j) := by
  have hil : i < (negativeSlots low).length := (List.getElem?_eq_some_iff.mp hi).1
  unfold nativeSources
  rw [List.getElem?_append_left (by simpa using hil), List.getElem?_map, hi]
  rfl

namespace TridiagonalCall

private theorem source_position (call : TridiagonalCall n k p) (hI : StrictMono call.slots)
    (i : ℕ) (j : Column call.low) (h : (nativeSources call.low)[i]? = some j) :
    i = (call.oracleSlot j).val := by
  have hget : call.nativeRankList[i]? = some ((rank call.slots call.low j).val + 1) := by
    rw [nativeRankList, List.getElem?_map, h]
    rfl
  have hi : i < call.oneBasedRanks.card := by
    obtain ⟨hlt, _⟩ := List.getElem?_eq_some_iff.mp hget
    rwa [nativeRankList_eq call hI, List.length_ofFn] at hlt
  rw [nativeRankList_eq call hI, List.getElem?_ofFn, dif_pos hi, Option.some.injEq] at hget
  have hRank : requestedRankOrder call.oneBasedRanks_subset ⟨i, hi⟩ =
      requestedRankOrder call.oneBasedRanks_subset (call.oracleSlot j) := by
    rw [call.requestedRankOrder_oracleSlot]
    apply Fin.ext
    change (requestedRankOrder call.oneBasedRanks_subset ⟨i, hi⟩).val =
      (orderedRanks call.slots call.low (outputIndex call.slots call.low j)).val
    rw [orderedRanks_outputIndex]
    omega
  exact congrArg Fin.val ((requestedRankOrder call.oneBasedRanks_subset).injective hRank)

theorem nativeLeftSlot_eq (call : TridiagonalCall n k p) (hI : StrictMono call.slots) (j : Fin k) :
    nativeLeftSlot call.low j = (call.positiveSlot j).val :=
  call.source_position hI _ _ (positiveSource_get call.low j)

theorem negativeLookup_eq (call : TridiagonalCall n k p) (hI : StrictMono call.slots)
    (j : {j // call.low j = true}) :
    (negativeLookup call.low)[j.val.val]? = some (call.negativeSlot j).val := by
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp (mem_negativeSlots call.low j)
  rw [negativeLookup_get call.low j i hi]
  congr 1
  exact call.source_position hI i _ (negativeSource_get call.low j i hi)

theorem nativeRightArray_get (call : TridiagonalCall n k p) (hI : StrictMono call.slots)
    (j : Fin k) : (nativeRightArray call.low)[j.val]? = some (call.rightSlot j).val := by
  unfold nativeRightArray
  rw [List.getElem?_toArray, List.getElem?_ofFn, dif_pos j.isLt]
  cases hj : call.low j
  · simpa [hj, nativeLeftSlot] using call.nativeLeftSlot_eq hI j
  · have he := call.negativeLookup_eq hI ⟨j, hj⟩
    rw [call.rightSlot_low j hj]
    have hi : j.val < (negativeLookup call.low).size := by
      rw [negativeLookup_size]
      exact j.isLt
    rw [Array.getElem?_eq_getElem hi, Option.some.injEq] at he
    simp only [if_true, he]

end TridiagonalCall

/-- A counted, tail-recursive binary ceiling logarithm. -/
private def ceilLogLoop (m count : ℕ) : ℕ :=
  if h : 1 < m then ceilLogLoop ((m + 1) / 2) (count + 1) else count
termination_by m
decreasing_by omega

private theorem ceilLogLoop_eq (m count : ℕ) :
    ceilLogLoop m count = count + Nat.clog 2 m := by
  by_cases h : 1 < m
  · rw [ceilLogLoop, dif_pos h, ceilLogLoop_eq ((m + 1) / 2) (count + 1),
      Nat.clog_of_two_le (b := 2) (by decide) (show 2 ≤ m from h)]
    rw [show m + 2 - 1 = m + 1 by omega]
    omega
  · rw [ceilLogLoop, dif_neg h, Nat.clog_of_right_le_one (by omega : m ≤ 1), Nat.add_zero]
termination_by m
decreasing_by omega

/-- The arrays used for the packed ranks and inverse lookup, and the working
precision selected from the actual number of distinct requested ranks. -/
structure NativeRankPlan where
  ranks : Array ℕ
  leftSlots : Array ℕ
  rightSlots : Array ℕ
  workingBits : ℕ

private def lowFlagsList (cmp : EmptyBinScan.Comparison (svdLabelPrecision k p)
    (svdLabelPrecision_ge_two k p)) (pre : BidiagonalPreprocessing k p) : List Bool :=
  pre.cache.labels.map fun s => cmp.lt s pre.cutExecution.result.state.lower

/-- Materialize the comparison against the cached cut once per original slot. -/
def assembleLowFlags (cmp : EmptyBinScan.Comparison (svdLabelPrecision k p)
    (svdLabelPrecision_ge_two k p)) (pre : BidiagonalPreprocessing k p)
    (hlen : pre.cache.labels.length = k) : Vector Bool k :=
  ⟨(lowFlagsList cmp pre).toArray, by simp [lowFlagsList, hlen]⟩

private theorem assembleLowFlags_get (cmp : EmptyBinScan.Comparison (svdLabelPrecision k p)
    (svdLabelPrecision_ge_two k p)) (pre : BidiagonalPreprocessing k p)
    (hlen : pre.cache.labels.length = k) (j : Fin k) :
    (assembleLowFlags cmp pre hlen).get j =
      cmp.lt (pre.cache.labels.get (Fin.cast hlen.symm j)) pre.cutExecution.result.state.lower := by
  simp [assembleLowFlags, lowFlagsList, Vector.get]

open FloatingPointFormat.UnboundedBinary in
theorem prepareLowFlags_spec {hp : 2 ≤ p} (upper : Bool) (a : Fin (n + 1) → Word p hp)
    (b : Fin n → Word p hp) (I : Fin k → Fin (n + 1))
    (cmp : EmptyBinScan.Comparison (svdLabelPrecision k p) (svdLabelPrecision_ge_two k p))
    (hn : 2 ≤ n + 1) (hk : 1 ≤ k) (hguard : precisionGuard (n + 1) p)
    (hI : StrictMono I) (call : TridiagonalCall n k p)
    (hcall : prepareTridiagonalCall upper a b I cmp hn hk hguard hI = some call) :
    (assembleLowFlags cmp call.preprocessing call.labelCount).get = call.low := by
  simp only [prepareTridiagonalCall] at hcall
  obtain ⟨pre, hlen, _, rfl⟩ := Option.pmap_eq_some_iff.mp hcall
  funext j
  exact assembleLowFlags_get cmp pre hlen j

/-- Work to materialize the low flags from the cached label stream, with
one comparison, one saved flag and one traversal step per label. -/
def lowFlagsTrace (k : ℕ) : List Step :=
  (List.replicate k [.index, .comparison, .index]).flatten

theorem lowFlagsTrace_resources (cap k : ℕ) :
    work (lowFlagsTrace k) = 3 * k ∧ TraceAllowed cap (lowFlagsTrace k) := by
  constructor
  · simp [work, lowFlagsTrace, List.length_flatten, Nat.mul_comm]
  · intro step hs
    unfold lowFlagsTrace at hs
    obtain ⟨l, hl, hm⟩ := List.mem_flatten.mp hs
    rw [(List.mem_replicate.mp hl).2] at hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl <;> trivial

private def rankArrayFrom {m : ℕ} (I : Fin k ↪ Fin m) (low : Fin k → Bool)
    (negatives : List {j // low j = true}) : Array ℕ :=
  ((negatives.map Sum.inr ++ List.ofFn Sum.inl).map fun j => (rank I low j).val + 1).toArray

namespace TridiagonalCall

/-- Read the native flag vector by index, form both sorted rank blocks and
fill the lookup, then choose the actual tridiagonal working precision. The
charged passes include list construction, conversion into arrays, and table
initialization and writes. Input bands and retained output columns belong to
the enclosing execution's storage account. -/
def nativeRankPlan (call : TridiagonalCall n k p) (flags : Vector Bool k) : NativeRankPlan :=
  let low := flags.get
  let negatives := negativeSlots low
  let l := negatives.length
  let ranks := rankArrayFrom call.slots low negatives
  let inv := inverseScan ((negatives.zipIdx).map fun (j, i) => (j.val, i)) (Array.replicate k 0)
  let left := Array.ofFn fun j : Fin k => l + j.val
  let right := (List.ofFn fun j : Fin k => if low j then
    inv[j.val]'(by simpa only [inv, inverseScan_size, Array.size_replicate] using j.isLt)
  else l + j.val).toArray
  let r := ranks.size
  let logK := ceilLogLoop k 0
  let logR := ceilLogLoop r 0
  let logN := ceilLogLoop (edgeCount n + 1) 0
  let aux := 2 * p + logK + 10
  let w := 2 * aux + 3 * logN + logR + 32
  ⟨ranks, left, right, w⟩

/-- Account for the three bounded flag, rank and inverse-table traversals,
and the binary ceiling-log loops. The trace is not allocated by the solver. -/
def nativeRankPlanTrace (call : TridiagonalCall n k p) (flags : Vector Bool k) : List Step :=
  let l := (negativeSlots flags.get).length
  let r := (call.nativeRankPlan flags).ranks.size
  let logs := ceilLogLoop k 0 + ceilLogLoop r 0 + ceilLogLoop (edgeCount n + 1) 0
  List.replicate (12 * k + 12 * l + 4 * r) .index ++
    List.replicate (2 * k + 3 + logs) .comparison ++ List.replicate (8 + 4 * logs) .index

/-- Peak live words in each phase of the rank plan. -/
def nativeRankPlanLiveWords (call : TridiagonalCall n k p) (flags : Vector Bool k) : List ℕ :=
  let l := (negativeSlots flags.get).length
  let r := (call.nativeRankPlan flags).ranks.size
  [3 * k + 4, 8 * k + 4 * l + 4 * r + 12, k + l + 3 * r + 12, 2 * k + r + 12]

theorem nativeRankPlan_ranks (call : TridiagonalCall n k p) (flags : Vector Bool k)
    (hf : flags.get = call.low) :
    (call.nativeRankPlan flags).ranks = call.nativeRankArray := by
  change rankArrayFrom call.slots flags.get (negativeSlots flags.get) = _
  have he := congrArg (fun low => rankArrayFrom call.slots low (negativeSlots low)) hf
  simpa only [rankArrayFrom, nativeRankArray, nativeRankList, nativeSources, List.map_toArray] using he

theorem nativeRankPlan_leftSlots (call : TridiagonalCall n k p) (flags : Vector Bool k)
    (hf : flags.get = call.low) (hI : StrictMono call.slots) (j : Fin k) :
    (call.nativeRankPlan flags).leftSlots[j.val]? = some (call.positiveSlot j).val := by
  change (Array.ofFn (fun j : Fin k => (negativeSlots flags.get).length + j.val))[j.val]? = _
  rw [hf]
  simpa [nativeLeftSlot, j.isLt] using call.nativeLeftSlot_eq hI j

theorem nativeRankPlan_rightSlots (call : TridiagonalCall n k p) (flags : Vector Bool k)
    (hf : flags.get = call.low) (hI : StrictMono call.slots) (j : Fin k) :
    (call.nativeRankPlan flags).rightSlots[j.val]? = some (call.rightSlot j).val := by
  change (nativeRightArray flags.get)[j.val]? = _
  rw [hf]
  exact call.nativeRightArray_get hI j

theorem nativeRankPlan_workingBits (call : TridiagonalCall n k p) (flags : Vector Bool k)
    (hf : flags.get = call.low) (hI : StrictMono call.slots) :
    (call.nativeRankPlan flags).workingBits =
      workingPrecision (edgeCount n + 1) call.oneBasedRanks.card (svdAuxiliaryPrecision k p) := by
  change 2 * (2 * p + ceilLogLoop k 0 + 10) + 3 * ceilLogLoop (edgeCount n + 1) 0 +
    ceilLogLoop (call.nativeRankPlan flags).ranks.size 0 + 32 = _
  simp [ceilLogLoop_eq, nativeRankPlan_ranks call flags hf, nativeRankArray_size call hI,
    workingPrecision, svdAuxiliaryPrecision]

/-- The native precision is the tridiagonal algorithm's required precision
and is bounded by the outer SVD budget. -/
theorem nativeRankPlan_workingBits_le (call : TridiagonalCall n k p) (flags : Vector Bool k)
    (hf : flags.get = call.low) (hI : StrictMono call.slots) (hk : 1 ≤ k)
    (hguard : precisionGuard (n + 1) p) :
    (call.nativeRankPlan flags).workingBits ≤ svdWorkingPrecision (n + 1) k p := by
  rw [nativeRankPlan_workingBits call flags hf hI]
  exact (call.admissible hk hguard).2.2.2.2.2.2

private theorem length_negativeSlots_le (low : Fin k → Bool) : (negativeSlots low).length ≤ k := by
  unfold negativeSlots
  exact (List.length_filterMap_le _ _).trans_eq List.length_ofFn

private theorem clog_two_le (r : ℕ) : Nat.clog 2 r ≤ r := by
  exact Nat.clog_le_of_le_pow (Nat.lt_two_pow_self (n := r)).le

/-- Additional bounded work and live words for the native rank-and-slot
schedule, given the stored flags. No floating-point rounding occurs in it. -/
theorem nativeRankPlan_resources (call : TridiagonalCall n k p) (flags : Vector Bool k)
    (cap : ℕ) :
    work (call.nativeRankPlanTrace flags) ≤ 50 * k + 20 * (n + 1) + 40 ∧
    storage (call.nativeRankPlanLiveWords flags) ≤ 40 * k + 20 ∧
    TraceAllowed cap (call.nativeRankPlanTrace flags) := by
  let l := (negativeSlots flags.get).length
  let r := (call.nativeRankPlan flags).ranks.size
  let ln := Nat.clog 2 (edgeCount n + 1)
  let lk := Nat.clog 2 k
  let lr := Nat.clog 2 r
  have hl : l ≤ k := length_negativeSlots_le _
  have hr : r = l + k := by simp [r, l, nativeRankPlan, rankArrayFrom]
  have hd : edgeCount n + 1 = 2 * (n + 1) := by unfold edgeCount; omega
  have hln : ln ≤ 2 * (n + 1) := hd ▸ clog_two_le (edgeCount n + 1)
  have hlk : lk ≤ k := clog_two_le _
  have hlr : lr ≤ l + k := hr ▸ clog_two_le r
  constructor
  · change work (List.replicate (12 * k + 12 * l + 4 * r) .index ++
      List.replicate (2 * k + 3 + (ceilLogLoop k 0 + ceilLogLoop r 0 +
        ceilLogLoop (edgeCount n + 1) 0)) .comparison ++
      List.replicate (8 + 4 * (ceilLogLoop k 0 + ceilLogLoop r 0 +
        ceilLogLoop (edgeCount n + 1) 0)) .index) ≤ _
    simp only [work, List.length_append, List.length_replicate, ceilLogLoop_eq, Nat.zero_add]
    change 12 * k + 12 * l + 4 * r + (2 * k + 3 + (lk + lr + ln)) +
      (8 + 4 * (lk + lr + ln)) ≤ _
    omega
  constructor
  · rw [storage_le_iff]
    change ∀ w ∈ [3 * k + 4, 8 * k + 4 * l + 4 * r + 12,
      k + l + 3 * r + 12, 2 * k + r + 12], w ≤ _
    intro w hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl | rfl <;> omega
  · intro step hs
    simp only [nativeRankPlanTrace, List.mem_append, List.mem_replicate] at hs
    rcases hs with (⟨_, rfl⟩ | ⟨_, rfl⟩) | ⟨_, rfl⟩ <;> trivial


private theorem nativeRankPlan_leftSize (call : TridiagonalCall n k p) (flags : Vector Bool k) :
    (call.nativeRankPlan flags).leftSlots.size = k := by
  simp [nativeRankPlan]

private theorem nativeRankPlan_rightSize (call : TridiagonalCall n k p) (flags : Vector Bool k) :
    (call.nativeRankPlan flags).rightSlots.size = k := by
  simp [nativeRankPlan]

private theorem getSlot_eq {positions : Array ℕ} {j slot : ℕ} {hj : j < positions.size}
    (h : positions[j]? = some slot) : positions[j]'hj = slot := by
  rw [Array.getElem?_eq_getElem hj, Option.some.injEq] at h
  exact h

/-- Read the two stored position arrays to materialize both auxiliary-parity
arrays. Each output column lookup is a direct native array read. -/
def extractParitiesWithRankPlan (call : TridiagonalCall n k p) (upper : Bool)
    (flags : Vector Bool k) (hf : flags.get = call.low) (hI : StrictMono call.slots)
    (out : call.OracleOutput) : call.NativeParities :=
  let plan := call.nativeRankPlan flags
  let rows := (parityRows n upper).symm
  have hl (j : Fin k) : j.val < plan.leftSlots.size := by
    simpa only [plan, call.nativeRankPlan_leftSize flags] using j.isLt
  have hr (j : Fin k) : j.val < plan.rightSlots.size := by
    simpa only [plan, call.nativeRankPlan_rightSize flags] using j.isLt
  let left := Vector.ofFn fun j =>
    let slot : Fin call.oneBasedRanks.card := ⟨plan.leftSlots[j.val]' (hl j), by
      rw [getSlot_eq (call.nativeRankPlan_leftSlots flags hf hI j)]
      exact (call.positiveSlot j).isLt⟩
    let column := (out.pairs.get slot).column
    Vector.ofFn fun i => column.get (rows (Sum.inl i))
  let right := Vector.ofFn fun j =>
    let slot : Fin call.oneBasedRanks.card := ⟨plan.rightSlots[j.val]' (hr j), by
      rw [getSlot_eq (call.nativeRankPlan_rightSlots flags hf hI j)]
      exact (call.rightSlot j).isLt⟩
    let column := (out.pairs.get slot).column
    Vector.ofFn fun i => column.get (rows (Sum.inr i))
  ⟨out, left, right⟩

theorem extractParitiesWithRankPlan_eq (call : TridiagonalCall n k p) (upper : Bool)
    (flags : Vector Bool k) (hf : flags.get = call.low) (hI : StrictMono call.slots)
    (out : call.OracleOutput) :
    call.extractParitiesWithRankPlan upper flags hf hI out = call.extractParities upper out := by
  unfold extractParitiesWithRankPlan extractParities
  have hL : ∀ j : Fin k, ∀ h, (⟨(call.nativeRankPlan flags).leftSlots[j.val]'(by
      rw [call.nativeRankPlan_leftSize]; exact j.isLt), h⟩ :
      Fin call.oneBasedRanks.card) = call.positiveSlot j := fun j _ =>
    Fin.ext (getSlot_eq (call.nativeRankPlan_leftSlots flags hf hI j))
  have hR : ∀ j : Fin k, ∀ h, (⟨(call.nativeRankPlan flags).rightSlots[j.val]'(by
      rw [call.nativeRankPlan_rightSize]; exact j.isLt), h⟩ :
      Fin call.oneBasedRanks.card) = call.rightSlot j := fun j _ =>
    Fin.ext (getSlot_eq (call.nativeRankPlan_rightSlots flags hf hI j))
  simp only [hL, hR]

/-- One auxiliary solve followed by the indexed native parity reads. -/
noncomputable def solveParitiesWithRankPlan (call : TridiagonalCall n k p) (upper : Bool)
    (flags : Vector Bool k) (hf : flags.get = call.low) (hI : StrictMono call.slots)
    (hk : 1 ≤ k) (hguard : precisionGuard (n + 1) p)
    (bits : ℕ → GateBits (edgeCount n) call.oneBasedRanks) : Option call.NativeParities :=
  (call.solve hk hguard bits).map (call.extractParitiesWithRankPlan upper flags hf hI)

theorem solveParitiesWithRankPlan_eq (call : TridiagonalCall n k p) (upper : Bool)
    (flags : Vector Bool k) (hf : flags.get = call.low) (hI : StrictMono call.slots)
    (hk : 1 ≤ k) (hguard : precisionGuard (n + 1) p)
    (bits : ℕ → GateBits (edgeCount n) call.oneBasedRanks) :
    call.solveParitiesWithRankPlan upper flags hf hI hk hguard bits =
      call.solveParities upper hk hguard bits := by
  unfold solveParitiesWithRankPlan solveParities
  rw [show call.extractParitiesWithRankPlan upper flags hf hI = call.extractParities upper from
    funext (call.extractParitiesWithRankPlan_eq upper flags hf hI)]

end TridiagonalCall
end NumStability.CertifiedTridiagonalEigenpairs.BidiagonalSVDRequest
