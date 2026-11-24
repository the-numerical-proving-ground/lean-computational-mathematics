import ComputationalMathematics.Algorithms.Arithmetic.ScalarWork
import ComputationalMathematics.Source.CertifiedTridiagonalEigenpairs.TrivialBranchesTarget

/-!
# Executed work and storage of the exact tridiagonal branches

The counters describe scalar operations and simultaneous scalar-word usage.
The event and storage logs are observations of the execution, rather than
additional numerical arrays required by the eigensolver.
-/

namespace NumStability.CertifiedTridiagonalEigenpairs

open FloatingPointFormat.UnboundedBinary
open ScalarWork

variable {p n k : ℕ} {hp : 2 ≤ p}

/-- Local workspace observations, allowing four retained words per pending
frame for its word and traversal indices. -/
private def retain (live : List ℕ) : List ℕ := live.map (· + 4)

/-- Absolute-magnitude selection by the stored fields. Each branch records the
field reads and tests it actually performs. -/
private def compareMagnitude (x y : Word p hp) : Word p hp × List Step :=
  match x, y with
  | .zero, y => (y, [.comparison])
  | x, .zero => (x, [.comparison, .comparison])
  | x@(.normal _ m e _), y@(.normal _ m' e' _) =>
      let tests := [.comparison, .comparison, .readExponent, .readExponent, .comparison]
      if e < e' then (y, tests)
      else if e = e' then
        (if m ≤ m' then y else x, tests ++ [.comparison, .comparison])
      else (x, tests ++ [.comparison])

private theorem compareMagnitude_work (x y : Word p hp) : work (compareMagnitude x y).2 ≤ 7 := by
  cases x <;> cases y <;> simp only [compareMagnitude] <;>
    (repeat' split) <;> simp [work]

private theorem compareMagnitude_allowed (x y : Word p hp) (cap : ℕ) :
    TraceAllowed cap (compareMagnitude x y).2 := by
  cases x <;> cases y <;> simp only [compareMagnitude] <;>
    (repeat' split) <;> simp [TraceAllowed, Step.Allowed]

private structure ExactScan (p : ℕ) (hp : 2 ≤ p) where
  largest : Word p hp
  trace : List Step
  live : List ℕ

/-- Traverse the packed diagonal and edge words. The pending scan frame retains
its input word and traversal state. The comparison uses at most seven transient words after
the recursive scan returns. -/
private def scanWords : List (Word p hp) → ExactScan p hp
  | [] => ⟨.zero, [.index], [1]⟩
  | x :: xs =>
    let tail := scanWords xs
    let next := compareMagnitude x tail.largest
    ⟨next.1, .index :: (tail.trace ++ next.2), 1 :: (retain tail.live ++ [7])⟩

private theorem scanWords_work (xs : List (Word p hp)) :
    work (scanWords xs).trace ≤ 8 * xs.length + 1 := by
  induction xs with
  | nil => simp [scanWords, work]
  | cons x xs ih =>
    have h := compareMagnitude_work x (scanWords xs).largest
    simp only [scanWords, work, List.length_cons, List.length_append] at *
    omega

private theorem scanWords_allowed (xs : List (Word p hp)) (cap : ℕ) :
    TraceAllowed cap (scanWords xs).trace := by
  induction xs with
  | nil => simp [scanWords, TraceAllowed, Step.Allowed]
  | cons x xs ih =>
    intro step hs
    have h := compareMagnitude_allowed x (scanWords xs).largest cap
    simp only [scanWords, List.mem_cons, List.mem_append] at hs
    rcases hs with rfl | hs | hs
    · trivial
    · exact ih step hs
    · exact h step hs

private theorem scanWords_space (xs : List (Word p hp)) :
    storage (scanWords xs).live ≤ 4 * xs.length + 7 := by
  rw [storage_le_iff]
  induction xs with
  | nil => simp [scanWords]
  | cons x xs ih =>
    intro words h
    simp only [scanWords, retain, List.mem_cons, List.mem_append, List.mem_map,
      List.not_mem_nil, or_false] at h
    rcases h with rfl | ⟨words, hmem, rfl⟩ | rfl
    · simp
    · have := ih _ hmem
      simp only [List.length_cons]
      omega
    · omega

private theorem scanWords_largest (a : Fin (n + 1) → Word p hp) (b : Fin n → Word p hp) :
    (scanWords (List.ofFn a ++ List.ofFn b)).largest = largestStoredEntry a b := by
  unfold largestStoredEntry
  generalize List.ofFn a ++ List.ofFn b = xs
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [scanWords, List.foldr_cons, ← ih]
    generalize (scanWords xs).largest = y
    cases x <;> cases y <;> first | rfl | skip
    rename_i neg m e hm neg' m' e' hm'
    let x := Word.normal neg m e hm
    let y := Word.normal neg' m' e' hm'
    change (compareMagnitude x y).1 = (if e < e' ∨ (e = e' ∧ m ≤ m') then y else x)
    dsimp [compareMagnitude, x, y]
    by_cases he : e < e'
    · simp [he]
    · by_cases heq : e = e'
      · subst e'
        by_cases hmle : m ≤ m' <;> simp [hmle]
      · simp [he, heq]

private def dispatchExact (a : Fin (n + 1) → Word p hp) :
    Word p hp → Option (Word p hp) × List Step
  | .zero => (some .zero, [.comparison])
  | .normal .. =>
    if n = 0 then (some (a 0), [.comparison, .comparison, .index])
    else (none, [.comparison, .comparison])

private structure ExactWrites (p : ℕ) (hp : 2 ≤ p) where
  words : List (Word p hp)
  trace : List Step
  live : List ℕ

/-- Visit cells with a fixed input accessor and an increasing offset.
Each cell operation supplies the computed native word and its own trace. -/
private def writeFrom {m : ℕ} (cell : Fin m → Word p hp × List Step) :
    (count offset : ℕ) → offset + count ≤ m → ExactWrites p hp
  | 0, _, _ => ⟨[], [.index], [0]⟩
  | count + 1, offset, h =>
    let here := cell ⟨offset, by omega⟩
    let rest := writeFrom cell count (offset + 1) (by omega)
    ⟨here.1 :: rest.words, .index :: (here.2 ++ .index :: rest.trace),
      5 :: retain rest.live⟩

private def writeWords {m : ℕ} (cell : Fin m → Word p hp × List Step) : ExactWrites p hp :=
  writeFrom cell m 0 (by omega)

private theorem writeFrom_words {m : ℕ} (cell : Fin m → Word p hp × List Step)
    (count offset : ℕ) (h : offset + count ≤ m) :
    (writeFrom cell count offset h).words =
      List.ofFn (fun i : Fin count => (cell ⟨offset + i.val, by omega⟩).1) := by
  induction count generalizing offset with
  | zero => simp [writeFrom]
  | succ count ih =>
    simp only [writeFrom, List.ofFn_succ, Fin.val_zero, Nat.add_zero, ih, Fin.val_succ,
      List.cons.injEq, true_and]
    congr 1
    ext i
    congr 2
    exact Fin.ext (by change offset + 1 + i.val = offset + (i.val + 1); omega)

private theorem writeWords_words {m : ℕ} (cell : Fin m → Word p hp × List Step) :
    (writeWords cell).words = List.ofFn (fun i => (cell i).1) := by
  simp [writeWords, writeFrom_words]

private theorem writeFrom_work {m limit : ℕ} (cell : Fin m → Word p hp × List Step)
    (hcell : ∀ i, work (cell i).2 ≤ limit) (count offset : ℕ) (h : offset + count ≤ m) :
    work (writeFrom cell count offset h).trace ≤ (limit + 2) * count + 1 := by
  induction count generalizing offset with
  | zero => simp [writeFrom, work]
  | succ count ih =>
    have H := ih (offset + 1) (by omega)
    have hh := hcell ⟨offset, by omega⟩
    simp only [writeFrom, work, List.length_cons, List.length_append, Nat.mul_succ] at *
    omega

private theorem writeWords_work {m limit : ℕ} (cell : Fin m → Word p hp × List Step)
    (hcell : ∀ i, work (cell i).2 ≤ limit) : work (writeWords cell).trace ≤ (limit + 2) * m + 1 :=
  writeFrom_work cell hcell m 0 _

private theorem writeFrom_space {m : ℕ} (cell : Fin m → Word p hp × List Step)
    (count offset : ℕ) (h : offset + count ≤ m) :
    storage (writeFrom cell count offset h).live ≤ 4 * count + 5 := by
  rw [storage_le_iff]
  induction count generalizing offset with
  | zero => simp [writeFrom]
  | succ count ih =>
    intro words hw
    simp only [writeFrom, retain, List.mem_cons, List.mem_map] at hw
    rcases hw with rfl | ⟨words, hmem, rfl⟩
    · omega
    · have := ih (offset + 1) (by omega) _ hmem
      omega

private theorem writeWords_space {m : ℕ} (cell : Fin m → Word p hp × List Step) :
    storage (writeWords cell).live ≤ 4 * m + 5 := writeFrom_space cell m 0 _

private theorem writeFrom_allowed {m cap : ℕ} (cell : Fin m → Word p hp × List Step)
    (hcell : ∀ i, TraceAllowed cap (cell i).2) (count offset : ℕ) (h : offset + count ≤ m) :
    TraceAllowed cap (writeFrom cell count offset h).trace := by
  induction count generalizing offset with
  | zero => simp [writeFrom, TraceAllowed, Step.Allowed]
  | succ count ih =>
    intro step hs
    simp only [writeFrom, List.mem_cons, List.mem_append] at hs
    rcases hs with rfl | hs | rfl | hs
    · trivial
    · exact hcell ⟨offset, by omega⟩ step hs
    · trivial
    · exact ih (offset + 1) (by omega) step hs

private theorem writeWords_allowed {m cap : ℕ} (cell : Fin m → Word p hp × List Step)
    (hcell : ∀ i, TraceAllowed cap (cell i).2) : TraceAllowed cap (writeWords cell).trace :=
  writeFrom_allowed cell hcell m 0 _

private def labelCell (out : ExactBranchOutput p hp n k) (j : Fin k) : Word p hp × List Step :=
  (out.labels j, [])

private def coordinateCell (out : ExactBranchOutput p hp n k) (pos : Fin (k * (n + 1))) :
    Word p hp × List Step :=
  let ji := (finProdFinEquiv (m := k) (n := n + 1)).symm pos
  -- Decode the dense position, read the requested rank, and compare coordinates.
  (out.columns ji.2 ji.1, [.index, .index, .index, .comparison])

private def joinWrites : List (Word p hp) → List (Word p hp) → List (Word p hp) × List Step
  | [], columns => (columns, [.index])
  | label :: labels, columns =>
    let rest := joinWrites labels columns
    (label :: rest.1, .index :: .index :: rest.2)

private theorem joinWrites_words (labels columns : List (Word p hp)) :
    (joinWrites labels columns).1 = labels ++ columns := by
  induction labels with
  | nil => rfl
  | cons _ _ ih => simp [joinWrites, ih]

private theorem joinWrites_work (labels columns : List (Word p hp)) :
    work (joinWrites labels columns).2 ≤ 2 * labels.length + 1 := by
  induction labels with
  | nil => simp [joinWrites, work]
  | cons a xs ih =>
    simp only [joinWrites, work, List.length_cons] at *
    omega

private theorem joinWrites_allowed (labels columns : List (Word p hp)) (cap : ℕ) :
    TraceAllowed cap (joinWrites labels columns).2 := by
  induction labels with
  | nil => simp [joinWrites, TraceAllowed, Step.Allowed]
  | cons a xs ih =>
    intro step h
    simp only [joinWrites, List.mem_cons] at h
    rcases h with rfl | rfl | h
    · trivial
    · trivial
    · exact ih step h

/-- Materialize the two packed bands before traversing the scan. -/
private def packInputs (a : Fin (n + 1) → Word p hp) (b : Fin n → Word p hp) : ExactWrites p hp :=
  let diagonal := writeWords (fun i => (a i, [.index]))
  let edges := writeWords (fun i => (b i, [.index]))
  let joined := joinWrites diagonal.words edges.words
  ⟨joined.1, diagonal.trace ++ edges.trace ++ joined.2,
    diagonal.live ++ edges.live.map (diagonal.words.length + ·) ++ [4 * joined.1.length]⟩

private theorem packInputs_words (a : Fin (n + 1) → Word p hp) (b : Fin n → Word p hp) :
    (packInputs a b).words = List.ofFn a ++ List.ofFn b := by
  simp [packInputs, joinWrites_words, writeWords_words]

/-- The exact branch, including the explicitly written native output and the
arithmetic model observations. A nontrivial input dispatches with empty output. -/
structure ExactBranchExecution (p : ℕ) (hp : 2 ≤ p) (n k : ℕ) where
  output : Option (ExactBranchOutput p hp n k)
  words : List (Word p hp)
  trace : List Step
  liveWords : List ℕ

/-- The packed input, rank list, scan frames, and output occupy separate
storage. The base retains the caller's packed arrays and a packed scan view.
Write observations include the completed labels during the column writes.
The final observation includes both output buffers and the joined dense result. -/
def runExactBranch (a : Fin (n + 1) → Word p hp) (b : Fin n → Word p hp)
    (J : Fin k ↪o Fin (n + 1)) : ExactBranchExecution p hp n k :=
  let packed := packInputs a b
  let callerWords := packed.words.length + k + 8
  let base := callerWords + packed.words.length
  let scanned := scanWords packed.words
  let (branch, dispatch) := dispatchExact a scanned.largest
  let scanTrace := packed.trace ++ scanned.trace ++ dispatch
  let initial := callerWords :: (packed.live.map (callerWords + ·) ++
    scanned.live.map (base + ·))
  match branch with
  | none => ⟨none, [], scanTrace, initial⟩
  | some label =>
    let out : ExactBranchOutput p hp n k :=
      ⟨fun _ => label, fun i j => coordinateWord p hp i (J j), 0⟩
    let labels := writeWords (labelCell out)
    let columns := writeWords (coordinateCell out)
    let joined := joinWrites labels.words columns.words
    ⟨some out, joined.1, scanTrace ++ labels.trace ++ columns.trace ++ joined.2,
      initial ++ labels.live.map (base + ·) ++ columns.live.map (base + k + ·) ++
        [base + 4 * joined.1.length]⟩


/-- Observing the operations preserves the branch and every returned word. -/
theorem runExactBranch_output (a : Fin (n + 1) → Word p hp) (b : Fin n → Word p hp)
    (J : Fin k ↪o Fin (n + 1)) :
    (runExactBranch a b J).output = exactBranch a b J ∧
    (runExactBranch a b J).words = ((exactBranch a b J).map exactBranchOutputWords).getD [] := by
  simp only [runExactBranch, packInputs_words, scanWords_largest, exactBranch, exactBranchLabel]
  cases H : largestStoredEntry a b with
  | zero =>
    simp [dispatchExact, joinWrites_words, writeWords_words, labelCell, coordinateCell,
      exactBranchOutputWords]
  | normal sign m exponent hm =>
    by_cases hn : n = 0 <;>
      simp [dispatchExact, hn, joinWrites_words, writeWords_words, labelCell, coordinateCell,
        exactBranchOutputWords]

private theorem append_allowed {cap : ℕ} {left right : List Step}
    (hl : TraceAllowed cap left) (hr : TraceAllowed cap right) :
    TraceAllowed cap (left ++ right) := by
  intro step h
  exact (List.mem_append.mp h).elim (hl step) (hr step)

private theorem packInputs_work (a : Fin (n + 1) → Word p hp) (b : Fin n → Word p hp) :
    work (packInputs a b).trace ≤ 8 * (2 * n + 1) + 3 := by
  have hd := writeWords_work (limit := 1) (fun i => (a i, [.index]))
    (fun _ => by simp [work])
  have hb := writeWords_work (limit := 1) (fun i => (b i, [.index]))
    (fun _ => by simp [work])
  have hj := joinWrites_work (writeWords (fun i => (a i, [.index]))).words
    (writeWords (fun i => (b i, [.index]))).words
  simp only [packInputs, work, List.length_append, writeWords_words, List.length_ofFn] at *
  omega

private theorem packInputs_allowed (a : Fin (n + 1) → Word p hp) (b : Fin n → Word p hp) :
    TraceAllowed p (packInputs a b).trace := by
  apply append_allowed (append_allowed (writeWords_allowed _ _) (writeWords_allowed _ _))
    (joinWrites_allowed _ _ p) <;>
    simp [TraceAllowed, Step.Allowed]

private theorem output_work_data (out : ExactBranchOutput p hp n k) :
    work (writeWords (labelCell out)).trace ≤ 2 * k + 1 ∧
    work (writeWords (coordinateCell out)).trace ≤ 6 * (k * (n + 1)) + 1 ∧
    work (joinWrites (writeWords (labelCell out)).words (writeWords (coordinateCell out)).words).2
      ≤ 2 * k + 1 := by
  refine ⟨?_, ?_, ?_⟩
  · exact writeWords_work (limit := 0) _ (fun _ => by simp [labelCell, work])
  · exact writeWords_work (limit := 4) _ (fun _ => by simp [coordinateCell, work])
  · simpa only [writeWords_words, List.length_ofFn] using
      joinWrites_work (writeWords (labelCell out)).words (writeWords (coordinateCell out)).words

private theorem output_space_data (out : ExactBranchOutput p hp n k) :
    storage (writeWords (labelCell out)).live ≤ 4 * k + 5 ∧
    storage (writeWords (coordinateCell out)).live ≤ 4 * (k * (n + 1)) + 5 ∧
    (joinWrites (writeWords (labelCell out)).words (writeWords (coordinateCell out)).words).1.length =
      k + k * (n + 1) := by
  exact ⟨writeWords_space _, writeWords_space _,
    by simp only [joinWrites_words, writeWords_words, List.length_append, List.length_ofFn]⟩

private theorem output_allowed (out : ExactBranchOutput p hp n k) (t : List Step)
    (ht : TraceAllowed p t) :
    TraceAllowed p (t ++ (writeWords (labelCell out)).trace ++
      (writeWords (coordinateCell out)).trace ++
      (joinWrites (writeWords (labelCell out)).words (writeWords (coordinateCell out)).words).2) := by
  refine append_allowed (append_allowed (append_allowed ht ?_) ?_) (joinWrites_allowed _ _ p)
  · exact writeWords_allowed _ (fun _ => by simp [labelCell, TraceAllowed])
  · exact writeWords_allowed _ (fun _ => by simp [coordinateCell, TraceAllowed, Step.Allowed])

/-- Uniform deterministic work bound from the observed scan, dispatch and
per-cell output writes. The bound holds for successful exact paths and for
inputs passed on to the nontrivial branch. -/
theorem runExactBranch_work (a : Fin (n + 1) → Word p hp) (b : Fin n → Word p hp)
    (J : Fin k ↪o Fin (n + 1)) (hk : 0 < k) :
    work (runExactBranch a b J).trace ≤ 56 * ((n + 1) * k) ∧
    TraceAllowed p (runExactBranch a b J).trace := by
  let input := List.ofFn a ++ List.ofFn b
  let scanned := scanWords input
  have hscan : work scanned.trace ≤ 8 * (2 * n + 1) + 1 := by
    have h := scanWords_work input
    simp only [input, List.length_append, List.length_ofFn] at h
    dsimp only [scanned, input]
    omega
  have hscanA := append_allowed (packInputs_allowed a b) (scanWords_allowed input p)
  have hpack := packInputs_work a b
  have hN : n + 1 ≤ (n + 1) * k := Nat.le_mul_of_pos_right _ hk
  have hkN : k ≤ (n + 1) * k := Nat.le_mul_of_pos_left _ (Nat.succ_pos _)
  simp only [runExactBranch, packInputs_words]
  have hdispatch : work (dispatchExact a scanned.largest).2 ≤ 3 ∧
      TraceAllowed p (dispatchExact a scanned.largest).2 := by
    cases scanned.largest <;> by_cases hn : n = 0 <;>
      simp [dispatchExact, hn, work, TraceAllowed, Step.Allowed]
  generalize H : dispatchExact a (scanWords (List.ofFn a ++ List.ofFn b)).largest = decoded
  cases decoded with
  | mk branch dispatch =>
    change work (dispatchExact a (scanWords (List.ofFn a ++ List.ofFn b)).largest).2 ≤ 3 ∧
      TraceAllowed p (dispatchExact a (scanWords (List.ofFn a ++ List.ofFn b)).largest).2 at hdispatch
    rw [H] at hdispatch
    have hbase := append_allowed hscanA hdispatch.2
    cases branch with
    | none =>
      refine ⟨?_, hbase⟩
      change work ((packInputs a b).trace ++ scanned.trace ++ dispatch) ≤ _
      simp only [work, List.length_append] at *
      omega
    | some label =>
      let out : ExactBranchOutput p hp n k :=
        ⟨fun _ => label, fun i j => coordinateWord p hp i (J j), 0⟩
      refine ⟨?_, output_allowed out _ hbase⟩
      have ⟨hlabels, hcolumns, hjoin⟩ := output_work_data out
      change work ((packInputs a b).trace ++ scanned.trace ++ dispatch ++ (writeWords (labelCell out)).trace ++
        (writeWords (coordinateCell out)).trace ++
        (joinWrites (writeWords (labelCell out)).words (writeWords (coordinateCell out)).words).2)
        ≤ _
      simp only [work, List.length_append, Nat.mul_comm k (n + 1)] at *
      omega


private theorem storage_append_le {left right : List ℕ} {bound : ℕ}
    (hl : storage left ≤ bound) (hr : storage right ≤ bound) :
    storage (left ++ right) ≤ bound := by
  rw [storage_le_iff] at *
  intro w hw
  exact (List.mem_append.mp hw).elim (hl w) (hr w)

private theorem shifted_storage_le (base : ℕ) {live : List ℕ} {bound : ℕ}
    (h : storage live ≤ bound) : storage (live.map (base + ·)) ≤ base + bound := by
  rw [storage_le_iff] at *
  intro w hw
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hw
  exact Nat.add_le_add_left (h s hs) base

private theorem packInputs_space (a : Fin (n + 1) → Word p hp) (b : Fin n → Word p hp) :
    storage (packInputs a b).live ≤ 4 * (2 * n + 1) + 5 := by
  let dl := writeWords (fun i => (a i, [.index]))
  let el := writeWords (fun i => (b i, [.index]))
  have hjoin : (joinWrites dl.words el.words).1.length = 2 * n + 1 := by
    dsimp only [dl, el]
    rw [joinWrites_words]
    simp only [writeWords_words, List.length_append, List.length_ofFn]
    omega
  have hdword : dl.words.length = n + 1 := by
    simp only [dl, writeWords_words, List.length_ofFn]
  change storage (dl.live ++ el.live.map (dl.words.length + ·) ++
    [4 * (joinWrites dl.words el.words).1.length]) ≤ _
  rw [hjoin, hdword]
  have hd : storage dl.live ≤ 4 * (n + 1) + 5 := writeWords_space _
  have he : storage el.live ≤ 4 * n + 5 := writeWords_space _
  refine storage_append_le (storage_append_le ?_ ?_) ?_
  · exact hd.trans (by omega)
  · exact (shifted_storage_le (n + 1) he).trans (by omega)
  · change max (4 * (2 * n + 1)) 0 ≤ _
    omega

/-- The observed peak includes the stored input and requested ranks, the
packing and scan workspace, and the native output buffers even while joined. -/
theorem runExactBranch_space (a : Fin (n + 1) → Word p hp) (b : Fin n → Word p hp)
    (J : Fin k ↪o Fin (n + 1)) :
    storage (runExactBranch a b J).liveWords ≤ 24 * (n + 1 + (n + 1) * k) := by
  let input := List.ofFn a ++ List.ofFn b
  let caller := input.length + k + 8
  let base := caller + input.length
  let scanned := scanWords input
  let initial := caller :: ((packInputs a b).live.map (caller + ·) ++
    scanned.live.map (base + ·))
  have hn : input.length = 2 * n + 1 := by
    simp only [input, List.length_append, List.length_ofFn]
    omega
  have hcaller : caller = 2 * n + 1 + k + 8 := by simp [caller, hn]
  have hbase : base = 4 * n + k + 10 := by simp [base, hcaller, hn]; omega
  have hkN : k ≤ (n + 1) * k := Nat.le_mul_of_pos_left _ (Nat.succ_pos _)
  have hinit : storage initial ≤ 24 * (n + 1 + (n + 1) * k) := by
    change max caller (storage ((packInputs a b).live.map (caller + ·) ++
      scanned.live.map (base + ·))) ≤ _
    rw [Nat.max_le]
    refine ⟨by omega, storage_append_le ?_ ?_⟩
    · exact (shifted_storage_le caller (packInputs_space a b)).trans (by omega)
    · exact (shifted_storage_le base (scanWords_space input)).trans (by omega)
  simp only [runExactBranch, packInputs_words]
  generalize H : dispatchExact a (scanWords (List.ofFn a ++ List.ofFn b)).largest = decoded
  cases decoded with
  | mk branch dispatch =>
    cases branch with
    | none => exact hinit
    | some label =>
      let out : ExactBranchOutput p hp n k :=
        ⟨fun _ => label, fun i j => coordinateWord p hp i (J j), 0⟩
      change storage (initial ++ (writeWords (labelCell out)).live.map (base + ·) ++
        (writeWords (coordinateCell out)).live.map (base + k + ·) ++
        [base + 4 *
          (joinWrites (writeWords (labelCell out)).words (writeWords (coordinateCell out)).words).1.length])
        ≤ _
      obtain ⟨hl, hc, hj⟩ := output_space_data out
      refine storage_append_le (storage_append_le (storage_append_le hinit ?_) ?_) ?_
      · exact (shifted_storage_le base hl).trans (by omega)
      · exact (shifted_storage_le (base + k) hc).trans (by rw [Nat.mul_comm k]; omega)
      · rw [storage_le_iff, hj, Nat.mul_comm k (n + 1)]
        simp only [List.mem_singleton, forall_eq]
        omega


private def chooseNormalization (word : Word p hp) : Option ℤ × List Step :=
  match word with
  | .zero => (none, [.comparison])
  | .normal _ m e _ =>
    if m = (format p hp).minNormalMantissa then
      (some (e - 1 + 2), [.comparison, .readExponent, .comparison, .index, .index])
    else (some (e + 2), [.comparison, .readExponent, .comparison, .index])

/-- The scale exponent and observations from scanning the stored tridiagonal
input and inspecting the selected word. -/
structure NormalizationScan where
  exponent : Option ℤ
  trace : List Step
  liveWords : List ℕ

/-- Select the normalization exponent with the same measured packed scan that
determines the exact-branch dispatch. The final branch tests the significand
against the format's smallest normalized significand and offsets the exponent. -/
def runNormalizationScan (a : Fin (n + 1) → Word p hp) (b : Fin n → Word p hp) :
    NormalizationScan :=
  let packed := packInputs a b
  let caller := packed.words.length + 8
  let base := caller + packed.words.length
  let scanned := scanWords packed.words
  let choice := chooseNormalization scanned.largest
  ⟨choice.1, packed.trace ++ scanned.trace ++ choice.2,
    caller :: (packed.live.map (caller + ·) ++ scanned.live.map (base + ·) ++ [base + 5])⟩

theorem runNormalizationScan_exponent
    (a : Fin (n + 1) → Word p hp) (b : Fin n → Word p hp) :
    (runNormalizationScan a b).exponent = normalizationExponent a b := by
  simp only [runNormalizationScan, packInputs_words, scanWords_largest, normalizationExponent]
  cases largestStoredEntry a b with
  | zero => rfl
  | normal negative m e hm =>
    by_cases h : m = (format p hp).minNormalMantissa <;>
      simp [chooseNormalization, coveringExponent, h]

theorem runNormalizationScan_resources
    (a : Fin (n + 1) → Word p hp) (b : Fin n → Word p hp) :
    let run := runNormalizationScan a b
    work run.trace ≤ 32 * (n + 1) ∧ TraceAllowed p run.trace ∧
      storage run.liveWords ≤ 24 * (n + 1) := by
  dsimp only
  let input := (packInputs a b).words
  let selected := (scanWords input).largest
  let caller := input.length + 8
  let base := caller + input.length
  have hlen : input.length = 2 * n + 1 := by
    simp only [input, packInputs_words, List.length_append, List.length_ofFn]
    omega
  have hchoose : work (chooseNormalization selected).2 ≤ 5 ∧
      TraceAllowed p (chooseNormalization selected).2 := by
    cases selected with
    | zero => simp [chooseNormalization, work, TraceAllowed, Step.Allowed]
    | normal negative m e hm =>
      by_cases h : m = (format p hp).minNormalMantissa <;>
        simp [chooseNormalization, h, work, TraceAllowed, Step.Allowed]
  refine ⟨?_, ?_, ?_⟩
  · have hpack := packInputs_work a b
    have hscan := scanWords_work input
    have hsel := hchoose.1
    change work ((packInputs a b).trace ++ (scanWords input).trace ++
      (chooseNormalization selected).2) ≤ _
    simp only [work, List.length_append] at *
    omega
  · exact append_allowed (append_allowed (packInputs_allowed a b) (scanWords_allowed input p))
      hchoose.2
  · change max caller (storage ((packInputs a b).live.map (caller + ·) ++
      (scanWords input).live.map (base + ·) ++ [base + 5])) ≤ _
    have hcaller : caller = 2 * n + 9 := by simp [caller, hlen]
    have hbase : base = 4 * n + 10 := by simp [base, hcaller, hlen]; omega
    rw [Nat.max_le]
    refine ⟨by omega, storage_append_le (storage_append_le ?_ ?_) ?_⟩
    · exact (shifted_storage_le caller (packInputs_space a b)).trans (by omega)
    · exact (shifted_storage_le base (scanWords_space input)).trans (by omega)
    · change max (base + 5) 0 ≤ _
      omega

end NumStability.CertifiedTridiagonalEigenpairs
