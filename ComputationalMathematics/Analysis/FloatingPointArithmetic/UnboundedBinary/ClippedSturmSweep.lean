import ComputationalMathematics.Algorithms.Arithmetic.ScalarWork
import ComputationalMathematics.Analysis.FloatingPointArithmetic.UnboundedBinary.ClippedSturm
import ComputationalMathematics.Analysis.FloatingPointArithmetic.UnboundedBinary.ScalarOperations
import Mathlib.Order.Interval.Finset.Fin

/-!
# Fixed-precision sweep for the clipped Sturm count

The loop retains the previous native pivot and the number of negative pivots
seen so far. Proof instrumentation accounts for scalar operations, index
work, and additional live scalar words in this loop. The input arrays are
read in place.
-/

namespace NumStability.FloatingPointFormat.UnboundedBinary

open ScalarWork

noncomputable section

variable {q : ℕ} {hq : 2 ≤ q}

private def oneWord (q : ℕ) (hq : 2 ≤ q) : Word q hq :=
  .normal false (format q hq).minNormalMantissa 1 (format q hq).minNormalMantissa_normalized

private theorem value_oneWord (q : ℕ) (hq : 2 ≤ q) : (oneWord q hq).value = 1 := by
  rw [oneWord, Word.value, (format q hq).normalizedValue_false_minNormalMantissa_eq]
  change (2 : ℝ) ^ ((1 : ℤ) - 1) = 1
  norm_num

/-- The clipping threshold, implemented as exact binary scaling of the word one. -/
def sturmClipWord (q : ℕ) (hq : 2 ≤ q) (r : ℕ) : Word q hq :=
  (oneWord q hq).scale (-(r : ℤ) + (-4))

@[simp] theorem value_sturmClipWord (q : ℕ) (hq : 2 ≤ q) (r : ℕ) :
    (sturmClipWord q hq r).value = sturmClipThreshold r := by
  rw [sturmClipWord, Word.value_scale, value_oneWord, mul_one, sturmClipThreshold_eq_zpow]

private def clipSturmWord (s raw : Word q hq) : Word q hq :=
  if s.value ≤ |raw.value| then raw else s

private theorem value_clipSturmWord (s raw : Word q hq) :
    (clipSturmWord s raw).value = clipSturmPivot s.value raw.value := by
  unfold clipSturmWord clipSturmPivot
  split_ifs <;> rfl

private theorem clipSturmWord_ne_zero (s raw : Word q hq) (hs : 0 < s.value) :
    (clipSturmWord s raw).value ≠ 0 := by
  rw [value_clipSturmWord]
  intro h
  have habs := le_abs_clipSturmPivot hs.le raw.value
  rw [h, abs_zero] at habs
  exact hs.not_ge habs

/-- The live pivot and count, with the accumulated arithmetic-model trace. -/
structure ClippedSturmSweepResult (q : ℕ) (hq : 2 ≤ q) where
  pivot : Word q hq
  pivot_ne_zero : pivot.value ≠ 0
  count : ℕ
  trace : List Step
  liveWords : List ℕ

/-- Allow one sign test, one exact negation, and one threshold comparison
for the magnitude test, followed by the pivot sign test and counter update. -/
private def sturmClipAndCountTrace (q : ℕ) : List Step :=
  [.comparison, .arithmetic q, .comparison, .comparison, .index]

private def sturmFirstTrace (q : ℕ) : List Step :=
  [.scaleByPowerOfTwo, .index, .arithmetic q] ++ sturmClipAndCountTrace q

/-- The loop condition and cursor increment, two input reads, and four
nearest-even operations precede clipping and counting at each later row. -/
private def sturmStepTrace (q : ℕ) : List Step :=
  [.comparison, .index, .index, .index,
    .arithmetic q, .arithmetic q, .arithmetic q, .arithmetic q] ++ sturmClipAndCountTrace q

/-- Additional words while setting up the threshold, computing the first
pivot, and initializing the sign count. -/
private def sturmFirstLiveWords : List ℕ := [8, 10, 9]

/-- Additional words for the loop state and the phases that read both row
entries, evaluate the rounded operations, clip, and update the count. -/
private def sturmStepLiveWords : List ℕ := [9, 12, 14, 11, 9]

private def sturmSweepFirst (s : Word q hq) (hs : 0 < s.value) (a x : Word q hq) :
    ClippedSturmSweepResult q hq :=
  let raw := (ScalarOperation.sub a x).eval
  let pivot := clipSturmWord s raw
  ⟨pivot, clipSturmWord_ne_zero s raw hs, if pivot.value < 0 then 1 else 0, (sturmFirstTrace q).reverse, sturmFirstLiveWords.reverse⟩

private def sturmSweepStep (s : Word q hq) (hs : 0 < s.value) (a b x : Word q hq)
    (state : ClippedSturmSweepResult q hq) : ClippedSturmSweepResult q hq :=
  let c := (ScalarOperation.sub a x).eval
  let z := (ScalarOperation.mul b b).eval
  let v := (ScalarOperation.div z state.pivot state.pivot_ne_zero).eval
  let raw := (ScalarOperation.sub c v).eval
  let pivot := clipSturmWord s raw
  ⟨pivot, clipSturmWord_ne_zero s raw hs,
    state.count + (if pivot.value < 0 then 1 else 0),
    (sturmStepTrace q).reverse ++ state.trace, sturmStepLiveWords.reverse ++ state.liveWords⟩

/-- A single forward pass over the rows. All divisions carry an explicit proof
that the previous stored pivot is nonzero. The trace is proof instrumentation
for this pass. -/
def clippedSturmSweep {n : ℕ} (q : ℕ) (hq : 2 ≤ q) (r : ℕ)
    (a : Fin (n + 1) → Word q hq) (b : Fin n → Word q hq) (x : Word q hq) :
    ClippedSturmSweepResult q hq :=
  let s := sturmClipWord q hq r
  have hs : 0 < s.value := (value_sturmClipWord q hq r).symm ▸ sturmClipThreshold_pos r
  let result := Fin.foldl n (fun state i => sturmSweepStep s hs (a i.succ) (b i) x state)
    (sturmSweepFirst s hs (a 0) x)
  { result with
    trace := (.comparison :: result.trace).reverse
    liveWords := (9 :: result.liveWords).reverse }

private theorem sturmSweepFirst_value (s : Word q hq) (hs : 0 < s.value) (a x : Word q hq) :
    (sturmSweepFirst s hs a x).pivot.value = clippedSturmFirst q hq s.value a.value x.value := by
  simp only [sturmSweepFirst, value_clipSturmWord, clippedSturmFirst,
    ScalarOperation.eval, Word.value_round, ScalarOperation.exactValue]

private theorem sturmSweepStep_value (s : Word q hq) (hs : 0 < s.value) (a b x : Word q hq)
    (state : ClippedSturmSweepResult q hq) :
    (sturmSweepStep s hs a b x state).pivot.value =
      clippedSturmStep q hq s.value a.value b.value x.value state.pivot.value := by
  simp only [sturmSweepStep, value_clipSturmWord, clippedSturmStep, clippedSturmRaw,
    ScalarOperation.eval, Word.value_round, ScalarOperation.exactValue, pow_two]

private theorem fin_foldl_invariant {α : Type*} {n : ℕ}
    (f : α → Fin n → α) (init : α) (P : Fin (n + 1) → α → Prop)
    (hinit : P 0 init) (hstep : ∀ i s, P i.castSucc s → P i.succ (f s i)) :
    P (Fin.last n) (Fin.foldl n f init) := by
  induction n with
  | zero => simpa only [Fin.foldl_zero] using hinit
  | succ n ih =>
    rw [Fin.foldl_succ_last]
    have hprefix := ih (fun s i => f s i.castSucc) (fun i => P i.castSucc)
      (by simpa only [Fin.castSucc_zero] using hinit)
      (fun i s h => by
        dsimp only
        rw [Fin.castSucc_succ]
        exact hstep i.castSucc s h)
    simpa only [Fin.succ_last] using hstep (Fin.last n) _ hprefix

private theorem clippedSturmSweep_spec {n : ℕ} (q : ℕ) (hq : 2 ≤ q) (r : ℕ)
    (a : Fin (n + 1) → Word q hq) (b : Fin n → Word q hq) (x : Word q hq) :
    let d := clippedSturmPivots q hq r (fun i => (a i).value) (fun i => (b i).value) x.value
    let result := clippedSturmSweep q hq r a b x
    result.count = (Finset.univ.filter (fun i => d i < 0)).card ∧
      work result.trace ≤ 13 * (n + 1) ∧ TraceAllowed q result.trace ∧
      storage result.liveWords ≤ 14 := by
  let d := clippedSturmPivots q hq r (fun i => (a i).value) (fun i => (b i).value) x.value
  let s := sturmClipWord q hq r
  have hs : 0 < s.value := (value_sturmClipWord q hq r).symm ▸ sturmClipThreshold_pos r
  let P (i : Fin (n + 1)) (state : ClippedSturmSweepResult q hq) :=
    state.pivot.value = d i ∧ state.count = ((Finset.Iic i).filter (fun j => d j < 0)).card ∧
      work state.trace = 8 + 13 * i.val ∧ TraceAllowed q state.trace ∧
      storage state.liveWords ≤ 14
  have hfirst : (sturmSweepFirst s hs (a 0) x).pivot.value = d 0 := by
    rw [sturmSweepFirst_value]
    simp only [d, s, clippedSturmPivots_zero, value_sturmClipWord]
  have hinit : P 0 (sturmSweepFirst s hs (a 0) x) := by
    have hIic : Finset.Iic (0 : Fin (n + 1)) = {0} := Finset.Iic_bot
    refine ⟨hfirst, ?_, by rfl, ?_, ?_⟩
    · change (if (sturmSweepFirst s hs (a 0) x).pivot.value < 0 then 1 else 0) =
        ((Finset.Iic (0 : Fin (n + 1))).filter (fun j => d j < 0)).card
      rw [hfirst, hIic, Finset.filter_singleton]
      by_cases h : d 0 < 0 <;> simp [h]
    · simp [sturmSweepFirst, TraceAllowed, sturmFirstTrace, sturmClipAndCountTrace, Step.Allowed, hq]
    · simp [sturmSweepFirst, storage_le_iff, sturmFirstLiveWords]
  have hstep (i : Fin n) (state : ClippedSturmSweepResult q hq) (h : P i.castSucc state) :
      P i.succ (sturmSweepStep s hs (a i.succ) (b i) x state) := by
    obtain ⟨hpivot, hcount, hwork, hallowed, hstorage⟩ := h
    have hpivot' : (sturmSweepStep s hs (a i.succ) (b i) x state).pivot.value = d i.succ := by
      rw [sturmSweepStep_value, hpivot]
      simp only [d, s, clippedSturmPivots_succ, value_sturmClipWord]
    have hIic : Finset.Iic i.succ = insert i.succ (Finset.Iic i.castSucc) := by
      ext j
      simp only [Finset.mem_Iic, Finset.mem_insert, Fin.le_def, Fin.val_succ, Fin.val_castSucc]
      rw [← Fin.val_inj]
      simp only [Fin.val_succ]
      omega
    have hnot : i.succ ∉ (Finset.Iic i.castSucc).filter (fun j => d j < 0) := by
      simp only [Finset.mem_filter, Finset.mem_Iic, Fin.le_def, Fin.val_succ, Fin.val_castSucc]
      omega
    refine ⟨hpivot', ?_, ?_, ?_, ?_⟩
    · change state.count + (if (sturmSweepStep s hs (a i.succ) (b i) x state).pivot.value < 0
        then 1 else 0) = ((Finset.Iic i.succ).filter (fun j => d j < 0)).card
      rw [hcount, hpivot', hIic, Finset.filter_insert]
      by_cases h : d i.succ < 0 <;> simp [h, Finset.card_insert_of_notMem hnot]
    · change work ((sturmStepTrace q).reverse ++ state.trace) = 8 + 13 * i.succ.val
      change state.trace.length = _ at hwork
      rw [work, List.length_append, List.length_reverse, hwork]
      simp [sturmStepTrace, sturmClipAndCountTrace]
      omega
    · change TraceAllowed q ((sturmStepTrace q).reverse ++ state.trace)
      intro step hmem
      rcases List.mem_append.mp hmem with hmem | hmem
      · have htrace : TraceAllowed q (sturmStepTrace q) := by
          simp [TraceAllowed, sturmStepTrace, sturmClipAndCountTrace, Step.Allowed, hq]
        exact htrace step (List.mem_reverse.mp hmem)
      · exact hallowed step hmem
    · change storage (sturmStepLiveWords.reverse ++ state.liveWords) ≤ 14
      rw [storage_le_iff] at hstorage ⊢
      intro words hmem
      rcases List.mem_append.mp hmem with hmem | hmem
      · have hstage : ∀ k ∈ sturmStepLiveWords, k ≤ 14 := by simp [sturmStepLiveWords]
        exact hstage words (List.mem_reverse.mp hmem)
      · exact hstorage words hmem
  obtain ⟨_, hcount, hwork, hallowed, hstorage⟩ :=
    fin_foldl_invariant _ _ P hinit hstep
  have hIic : Finset.Iic (Fin.last n) = Finset.univ := Finset.Iic_top
  refine ⟨hcount.trans (congrArg (fun u => (Finset.filter (fun j => d j < 0) u).card) hIic), ?_, ?_, ?_⟩
  · rw [clippedSturmSweep]
    dsimp only
    rw [work, List.length_reverse, List.length_cons, ← work, hwork, Fin.val_last]
    omega
  · rw [clippedSturmSweep]
    intro step hmem
    rcases List.mem_cons.mp (List.mem_reverse.mp hmem) with rfl | hmem
    · trivial
    · exact hallowed step hmem
  · rw [clippedSturmSweep, storage_le_iff]
    rw [storage_le_iff] at hstorage
    intro words hmem
    rcases List.mem_cons.mp (List.mem_reverse.mp hmem) with rfl | hmem
    · norm_num
    · exact hstorage words hmem

/-- The forward sweep counts precisely the negative entries of the rounded
pivot recurrence. -/
theorem clippedSturmSweep_count {n : ℕ} (q : ℕ) (hq : 2 ≤ q) (r : ℕ)
    (a : Fin (n + 1) → Word q hq) (b : Fin n → Word q hq) (x : Word q hq) :
    let d := clippedSturmPivots q hq r (fun i => (a i).value) (fun i => (b i).value) x.value
    (clippedSturmSweep q hq r a b x).count = (Finset.univ.filter (fun i => d i < 0)).card :=
  (clippedSturmSweep_spec q hq r a b x).1

/-- The same sweep has at most thirteen charged operations per row, including
clipping, sign counting, control, and the final loop test. -/
theorem clippedSturmSweep_work {n : ℕ} (q : ℕ) (hq : 2 ≤ q) (r : ℕ)
    (a : Fin (n + 1) → Word q hq) (b : Fin n → Word q hq) (x : Word q hq) :
    let trace := (clippedSturmSweep q hq r a b x).trace
    work trace ≤ 13 * (n + 1) ∧ TraceAllowed q trace :=
  ⟨(clippedSturmSweep_spec q hq r a b x).2.1, (clippedSturmSweep_spec q hq r a b x).2.2.1⟩

/-- The sweep needs at most fourteen words beyond the resident input arrays.
The execution instrumentation is excluded from this accounting. -/
theorem clippedSturmSweep_storage {n : ℕ} (q : ℕ) (hq : 2 ≤ q) (r : ℕ)
    (a : Fin (n + 1) → Word q hq) (b : Fin n → Word q hq) (x : Word q hq) :
    storage (clippedSturmSweep q hq r a b x).liveWords ≤ 14 :=
  (clippedSturmSweep_spec q hq r a b x).2.2.2

end
end NumStability.FloatingPointFormat.UnboundedBinary
