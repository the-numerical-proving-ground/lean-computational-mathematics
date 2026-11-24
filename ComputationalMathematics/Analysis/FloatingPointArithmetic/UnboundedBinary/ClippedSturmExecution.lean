import ComputationalMathematics.Analysis.FloatingPointArithmetic.UnboundedBinary.ClippedSturmSweep

/-!
# Trace-free execution of a clipped Sturm sweep

The loop state holds one pivot and one counter. A typed row program specifies
the rounded operations, clipping, and sign counting. Its ordinary interpreter
returns scalar values alone. A separate interpreter records the work charges
and the register occupancy of the same phases.
-/

namespace NumStability.FloatingPointFormat.UnboundedBinary

open ScalarWork

noncomputable section

variable {q : ℕ} {hq : 2 ≤ q}

/-- The state carried from one row to the next. The nonzero proof allows a
rounded division in the next row. -/
structure ClippedSturmState (q : ℕ) (hq : 2 ≤ q) where
  pivot : Word q hq
  pivot_ne_zero : pivot.value ≠ 0
  count : ℕ

private abbrev PositiveWord (q : ℕ) (hq : 2 ≤ q) :=
  {w : Word q hq // 0 < w.value}

private abbrev NonzeroWord (q : ℕ) (hq : 2 ≤ q) :=
  {w : Word q hq // w.value ≠ 0}

private def positiveClipWord (q : ℕ) (hq : 2 ≤ q) (r : ℕ) : PositiveWord q hq :=
  ⟨sturmClipWord q hq r, by rw [value_sturmClipWord]; exact sturmClipThreshold_pos r⟩

private def clipWord (s : PositiveWord q hq) (raw : Word q hq) : NonzeroWord q hq :=
  ⟨if s.val.value ≤ |raw.value| then raw else s.val, by
    split_ifs with h
    · intro hz
      rw [hz, abs_zero] at h
      exact s.property.not_ge h
    · exact s.property.ne'⟩

/-- The instructions used during initialization, a row, and the return.
A row shift charges the loop test, increment, and input reads in addition to
the rounded subtraction. -/
private inductive SturmInstruction (q : ℕ) (hq : 2 ≤ q) : Type → Type where
  | threshold (r : ℕ) : SturmInstruction q hq (PositiveWord q hq)
  | firstShift (a x : Word q hq) : SturmInstruction q hq (Word q hq)
  | rowShift (a x : Word q hq) : SturmInstruction q hq (Word q hq)
  | square (b : Word q hq) : SturmInstruction q hq (Word q hq)
  | quotient (z : Word q hq) (prev : NonzeroWord q hq) : SturmInstruction q hq (Word q hq)
  | difference (c v : Word q hq) : SturmInstruction q hq (Word q hq)
  | clip (s : PositiveWord q hq) (t : Word q hq) : SturmInstruction q hq (NonzeroWord q hq)
  | firstCount (d : NonzeroWord q hq) : SturmInstruction q hq ℕ
  | nextCount (count : ℕ) (d : NonzeroWord q hq) : SturmInstruction q hq ℕ
  | exit : SturmInstruction q hq Unit

@[inline] private def SturmInstruction.eval {α : Type} : SturmInstruction q hq α → α
  | .threshold r => positiveClipWord q hq r
  | .firstShift a x | .rowShift a x => (ScalarOperation.sub a x).eval
  | .square b => (ScalarOperation.mul b b).eval
  | .quotient z prev => (ScalarOperation.div z prev.val prev.property).eval
  | .difference c v => (ScalarOperation.sub c v).eval
  | .clip s t => clipWord s t
  | .firstCount d => if d.val.value < 0 then 1 else 0
  | .nextCount count d => count + (if d.val.value < 0 then 1 else 0)
  | .exit => ()

private abbrev Interpret (q : ℕ) (hq : 2 ≤ q) (m : Type → Type) :=
  {α : Type} → SturmInstruction q hq α → m α

@[inline] private def firstRow {m : Type → Type} [Monad m] (run : Interpret q hq m)
    (s : PositiveWord q hq) (a x : Word q hq) : m (ClippedSturmState q hq) := do
  let t ← run (.firstShift a x)
  let d ← run (.clip s t)
  let count ← run (.firstCount d)
  pure ⟨d.val, d.property, count⟩

@[inline] private def nextRow {m : Type → Type} [Monad m] (run : Interpret q hq m)
    (s : PositiveWord q hq) (a b x : Word q hq) (state : ClippedSturmState q hq) :
    m (ClippedSturmState q hq) := do
  let c ← run (.rowShift a x)
  let z ← run (.square b)
  let v ← run (.quotient z ⟨state.pivot, state.pivot_ne_zero⟩)
  let t ← run (.difference c v)
  let d ← run (.clip s t)
  let count ← run (.nextCount state.count d)
  pure ⟨d.val, d.property, count⟩

@[inline] private def pureInstruction : Interpret q hq Id := fun instruction => instruction.eval

/-- A trace-free loop. The threshold and shift are loop constants, and only
the current pivot and count survive from one row to the next. -/
def runClippedSturmSweep {n : ℕ} (q : ℕ) (hq : 2 ≤ q) (r : ℕ)
    (a : Fin (n + 1) → Word q hq) (b : Fin n → Word q hq) (x : Word q hq) :
    ClippedSturmState q hq :=
  let s := (pureInstruction (.threshold r)).run
  Fin.foldl n (fun state i => (nextRow pureInstruction s (a i.succ) (b i) x state).run)
    (firstRow pureInstruction s (a 0) x).run

private def eraseSweepResult (result : ClippedSturmSweepResult q hq) : ClippedSturmState q hq :=
  ⟨result.pivot, result.pivot_ne_zero, result.count⟩

private theorem foldl_intertwines {A B : Type*} {n : ℕ}
    (erase : A → B) (f : A → Fin n → A) (g : B → Fin n → B) (a : A)
    (h : ∀ s i, erase (f s i) = g (erase s) i) :
    erase (Fin.foldl n f a) = Fin.foldl n g (erase a) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Fin.foldl_succ_last, Fin.foldl_succ_last, h,
      ih (fun state i => f state i.castSucc) (fun state i => g state i.castSucc)
        (fun state i => h state i.castSucc)]

/-- Erasing the frozen sweep's instrumentation gives exactly the trace-free
pivot and count. The simulation uses the same input row at every transition. -/
theorem runClippedSturmSweep_eq {n : ℕ} (q : ℕ) (hq : 2 ≤ q) (r : ℕ)
    (a : Fin (n + 1) → Word q hq) (b : Fin n → Word q hq) (x : Word q hq) :
    let bare := runClippedSturmSweep q hq r a b x
    let frozen := clippedSturmSweep q hq r a b x
    bare.pivot = frozen.pivot ∧ bare.count = frozen.count := by
  have h : eraseSweepResult (clippedSturmSweep q hq r a b x) =
      runClippedSturmSweep q hq r a b x := by
    unfold clippedSturmSweep runClippedSturmSweep
    dsimp only
    change eraseSweepResult (Fin.foldl n _ _) = Fin.foldl n _ _
    apply foldl_intertwines
    intro state i
    rfl
  exact ⟨(congrArg ClippedSturmState.pivot h).symm, (congrArg ClippedSturmState.count h).symm⟩

/-- The trace-free sweep counts exactly the negative clipped pivots. -/
theorem runClippedSturmSweep_count {n : ℕ} (q : ℕ) (hq : 2 ≤ q) (r : ℕ)
    (a : Fin (n + 1) → Word q hq) (b : Fin n → Word q hq) (x : Word q hq) :
    let d := clippedSturmPivots q hq r (fun i => (a i).value) (fun i => (b i).value) x.value
    (runClippedSturmSweep q hq r a b x).count = (Finset.univ.filter (fun i => d i < 0)).card :=
  (runClippedSturmSweep_eq q hq r a b x).2.trans (clippedSturmSweep_count q hq r a b x)

/-- A resource account derived with the recording interpreter. These lists
are external evidence and are not part of the ordinary loop state. -/
structure ClippedSturmResources where
  trace : List ScalarWork.Step
  liveWords : List ℕ

private def SturmInstruction.charges {α : Type} : SturmInstruction q hq α → List ScalarWork.Step
  | .threshold _ => [.scaleByPowerOfTwo]
  | .firstShift _ _ => [.index, .arithmetic q]
  | .rowShift _ _ => [.comparison, .index, .index, .index, .arithmetic q]
  | .square _ | .quotient _ _ | .difference _ _ => [.arithmetic q]
  | .clip _ _ => [.comparison, .arithmetic q, .comparison]
  | .firstCount _ | .nextCount _ _ => [.comparison, .index]
  | .exit => [.comparison]

/-- Names of the scalar and index words in the arithmetic-model implementation.
The two input-array handles are included, and the resident entries are read
in place. A register that is uninitialized in an early phase may be reserved
in the accounting. -/
private inductive SturmRegister where
  | diagonalHandle | edgeHandle | dimension | precision | cursor | shift
  | threshold | pivot | count
  | accuracy | exponent | diagonal | edge | shifted | square | quotient | raw
  | magnitude | decision | newPivot | newCount

private def sweepRegisters : List SturmRegister :=
  [.diagonalHandle, .edgeHandle, .dimension, .precision, .cursor, .shift,
    .threshold, .pivot, .count]

private def SturmInstruction.temporaryRegisters {α : Type} :
    SturmInstruction q hq α → List SturmRegister
  | .threshold _ => [.accuracy, .exponent]
  | .firstShift _ _ => [.diagonal, .raw]
  | .rowShift _ _ => [.diagonal, .edge, .shifted]
  | .square _ => [.edge, .shifted, .square]
  | .quotient _ _ => [.shifted, .square, .quotient]
  | .difference _ _ => [.shifted, .quotient, .raw]
  | .clip _ _ => [.raw, .magnitude, .decision, .newPivot]
  | .firstCount _ | .nextCount _ _ => [.newPivot, .decision, .newCount]
  | .exit => []

/-- Instructions use the reserved sweep registers together with the local
operands, results and scratch registers named for that phase. -/
private def SturmInstruction.liveRegisterCount {α : Type} (step : SturmInstruction q hq α) : ℕ :=
  (sweepRegisters ++ step.temporaryRegisters).length

private def recordInstruction : Interpret q hq (StateM ClippedSturmResources) :=
  fun step prior => (step.eval,
    ⟨step.charges.reverse ++ prior.trace, step.liveRegisterCount :: prior.liveWords⟩)

private def recordedStart {n : ℕ} (q : ℕ) (hq : 2 ≤ q) (r : ℕ)
    (a : Fin (n + 1) → Word q hq) (x : Word q hq) :
    PositiveWord q hq × (ClippedSturmState q hq × ClippedSturmResources) :=
  let (s, prior) := (recordInstruction (.threshold r)).run ⟨[], []⟩
  (s, (firstRow recordInstruction s (a 0) x).run prior)

private def recordedNext (s : PositiveWord q hq) (a b x : Word q hq)
    (prior : ClippedSturmState q hq × ClippedSturmResources) :
    ClippedSturmState q hq × ClippedSturmResources :=
  (nextRow recordInstruction s a b x prior.1).run prior.2

private def recordedFold {n : ℕ} (q : ℕ) (hq : 2 ≤ q) (r : ℕ)
    (a : Fin (n + 1) → Word q hq) (b : Fin n → Word q hq) (x : Word q hq) :
    ClippedSturmState q hq × ClippedSturmResources :=
  let (s, init) := recordedStart q hq r a x
  Fin.foldl n (fun prior i => recordedNext s (a i.succ) (b i) x prior) init

private theorem recordedFold_eq_run {n : ℕ} (q : ℕ) (hq : 2 ≤ q) (r : ℕ)
    (a : Fin (n + 1) → Word q hq) (b : Fin n → Word q hq) (x : Word q hq) :
    (recordedFold q hq r a b x).1 = runClippedSturmSweep q hq r a b x := by
  unfold recordedFold runClippedSturmSweep
  dsimp only
  apply foldl_intertwines
  intro state i
  rfl

/-- The resource account accompanies the run of the same instructions.
The first projection is the trace-free result. The second is the separate
arithmetic-model account, with entries in execution order. -/
def recordedClippedSturmExecution {n : ℕ} (q : ℕ) (hq : 2 ≤ q) (r : ℕ)
    (a : Fin (n + 1) → Word q hq) (b : Fin n → Word q hq) (x : Word q hq) :
    ClippedSturmState q hq × ClippedSturmResources :=
  let (result, prior) := recordedFold q hq r a b x
  let (_, final) := (recordInstruction (.exit (q := q) (hq := hq))).run prior
  (result, ⟨final.trace.reverse, final.liveWords.reverse⟩)

theorem recordedClippedSturmExecution_eq_run {n : ℕ} (q : ℕ) (hq : 2 ≤ q) (r : ℕ)
    (a : Fin (n + 1) → Word q hq) (b : Fin n → Word q hq) (x : Word q hq) :
    (recordedClippedSturmExecution q hq r a b x).1 = runClippedSturmSweep q hq r a b x :=
  recordedFold_eq_run q hq r a b x

/-- Charges and simultaneous live-word upper bounds for the trace-free sweep. -/
def clippedSturmExecutionResources {n : ℕ} (q : ℕ) (hq : 2 ≤ q) (r : ℕ)
    (a : Fin (n + 1) → Word q hq) (b : Fin n → Word q hq) (x : Word q hq) :
    ClippedSturmResources :=
  (recordedClippedSturmExecution q hq r a b x).2

private def ResourceOK (q cost : ℕ) (resources : ClippedSturmResources) : Prop :=
  work resources.trace = cost ∧ TraceAllowed q resources.trace ∧ storage resources.liveWords ≤ 14

private theorem recordedStart_ok {n : ℕ} (q : ℕ) (hq : 2 ≤ q) (r : ℕ)
    (a : Fin (n + 1) → Word q hq) (x : Word q hq) :
    ResourceOK q 8 (recordedStart q hq r a x).2.2 := by
  change ResourceOK q 8
    ⟨[.index, .comparison, .comparison, .arithmetic q, .comparison, .arithmetic q, .index,
      .scaleByPowerOfTwo], [12, 13, 11, 11]⟩
  simp [ResourceOK, work, TraceAllowed, Step.Allowed, hq, storage]

private theorem recordedNext_ok (s : PositiveWord q hq) (a b x : Word q hq)
    (prior : ClippedSturmState q hq × ClippedSturmResources) (cost : ℕ)
    (h : ResourceOK q cost prior.2) :
    ResourceOK q (cost + 13) (recordedNext s a b x prior).2 := by
  rcases h with ⟨hwork, htrace, hlive⟩
  change ResourceOK q (cost + 13)
    ⟨[.index, .comparison, .comparison, .arithmetic q, .comparison, .arithmetic q, .arithmetic q,
      .arithmetic q, .arithmetic q, .index, .index, .index, .comparison] ++ prior.2.trace,
      [12, 13, 12, 12, 12, 12] ++ prior.2.liveWords⟩
  change prior.2.trace.length = cost at hwork
  refine ⟨by simp [work, hwork], ?_, ?_⟩
  · simp [TraceAllowed, Step.Allowed, hq] at htrace ⊢
    exact htrace
  · simp [storage_le_iff] at hlive ⊢
    exact hlive

private theorem recordedFold_ok {n : ℕ} (q : ℕ) (hq : 2 ≤ q) (r : ℕ)
    (a : Fin (n + 1) → Word q hq) (b : Fin n → Word q hq) (x : Word q hq) :
    ResourceOK q (8 + 13 * n) (recordedFold q hq r a b x).2 := by
  induction n with
  | zero =>
    unfold recordedFold
    dsimp only
    rw [Fin.foldl_zero]
    exact recordedStart_ok q hq r a x
  | succ n ih =>
    unfold recordedFold
    dsimp only
    rw [Fin.foldl_succ_last]
    have hprefix := ih (fun i => a i.castSucc) (fun i => b i.castSucc)
    change ResourceOK q (8 + 13 * (n + 1))
      (recordedNext (recordedStart q hq r a x).1 (a (Fin.last n).succ) (b (Fin.last n)) x
        (recordedFold q hq r (fun i => a i.castSucc) (fun i => b i.castSucc) x)).2
    rw [Nat.mul_succ, ← Nat.add_assoc]
    exact recordedNext_ok _ _ _ _ _ _ hprefix

/-- Linear work, precision compliance, and bounded additional storage for the
actual trace-free sweep. The resource interpreter accounts for all phases of
the same run without adding its lists to the ordinary interpreter. -/
theorem runClippedSturmSweep_resources {n : ℕ} (q : ℕ) (hq : 2 ≤ q) (r : ℕ)
    (a : Fin (n + 1) → Word q hq) (b : Fin n → Word q hq) (x : Word q hq) :
    let resources := clippedSturmExecutionResources q hq r a b x
    work resources.trace ≤ 13 * (n + 1) ∧ TraceAllowed q resources.trace ∧
      storage resources.liveWords ≤ 14 := by
  obtain ⟨hwork, htrace, hlive⟩ := recordedFold_ok q hq r a b x
  change work (List.reverse (.comparison :: (recordedFold q hq r a b x).2.trace)) ≤ 13 * (n + 1) ∧
    TraceAllowed q (List.reverse (.comparison :: (recordedFold q hq r a b x).2.trace)) ∧
    storage (List.reverse (9 :: (recordedFold q hq r a b x).2.liveWords)) ≤ 14
  refine ⟨?_, ?_, ?_⟩
  · rw [work, List.length_reverse, List.length_cons, ← work, hwork]
    omega
  · intro step hmem
    rcases List.mem_cons.mp (List.mem_reverse.mp hmem) with rfl | hmem
    · trivial
    · exact htrace step hmem
  · rw [storage_le_iff] at hlive ⊢
    intro words hmem
    rcases List.mem_cons.mp (List.mem_reverse.mp hmem) with rfl | hmem
    · norm_num
    · exact hlive words hmem

end
end NumStability.FloatingPointFormat.UnboundedBinary
