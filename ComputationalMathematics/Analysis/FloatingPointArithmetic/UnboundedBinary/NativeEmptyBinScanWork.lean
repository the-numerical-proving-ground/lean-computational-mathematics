import ComputationalMathematics.Analysis.FloatingPointArithmetic.UnboundedBinary.NativeEmptyBinScan

/-!
# Complete source-model work of the cached native empty-bin scan

The input is an already stored sorted stream and an already chosen native
binary scale. Each displayed primitive costs one source operation, including
stored-word reads/writes and ordinary cursor/index/control operations. Trace
construction and the old Work counters are proof instrumentation, not executed
numerical bookkeeping. No Boolean bit-complexity implementation is required.
-/

namespace NumStability.FloatingPointFormat.UnboundedBinary.EmptyBinScan.SourceWork

noncomputable section

open EmptyBinScan

variable {p : ℕ} {hp : 2 ≤ p}

/-- Constant-size stored locations of the scan and its return convention. -/
inductive Slot
  | scale | cursor | head | j | counter | lower | upper | scratch | result
  deriving DecidableEq, Repr

/-- Unit operations of the source arithmetic model. A scale is binary scaling,
not a general exponentiation. Cursor movement is ordinary index work. -/
inductive Primitive
  | read (slot : Slot)
  | write (slot : Slot)
  | compare | addOne | scale | increment | next | branch | call | ret
  deriving DecidableEq, Repr

open Primitive

/-- Acquire the fixed scale/cursor and initialize the four cached state fields. -/
def setupTrace : List Primitive :=
  [read .scale, write .scale, read .cursor, write .cursor,
   write .j, write .counter, read .scale, write .lower,
   read .counter, read .scale, scale, write .upper, call]

/-- A fixed-size state return: four field reads, four return-slot writes,
and return control. The same convention charges recursion unwinding. -/
def returnTrace : List Primitive :=
  [read .j, read .counter, read .lower, read .upper,
   write .result, write .result, write .result, write .result, ret]

def visitTrace : List Primitive := [read .cursor, branch]
def lowerTrace : List Primitive := [read .head, write .head, read .lower, compare, branch]
def upperTrace : List Primitive := [read .head, read .upper, compare, branch]
def continueTrace : List Primitive := [read .cursor, next, write .cursor, call]

/-- All cache/scratch accesses of the actual counter/endpoint advance, in
addition to its three arithmetic/index operations. The lower copy is its
read/write pair; it is not charged a second arithmetic operation. -/
def advanceTrace : List Primitive :=
  [read .counter, addOne, write .scratch,
   read .j, increment, write .j, read .upper, write .lower,
   read .scratch, write .counter, read .scratch, read .scale, scale, write .upper]

/-- Initialize from the supplied stored scale, avoiding exponent computation. -/
def initialStored (alpha : Word p hp) : State p hp where
  j := 1
  counter := ⟨2, native_two p hp⟩
  lower := alpha
  upper := ⟨roundToEven p hp (2 * alpha.val), roundToEven_native p hp _⟩

def advanceStored (alpha : Word p hp) (st : State p hp) : State p hp :=
  let w : Word p hp :=
    ⟨roundToEven p hp (st.counter.val + 1), roundToEven_native p hp _⟩
  {j := st.j + 1, counter := w, lower := st.upper,
   upper := ⟨roundToEven p hp (w.val * alpha.val), roundToEven_native p hp _⟩}

theorem initialStored_eq (alpha : Word p hp) (e : ℤ) (ha : alpha.val = (2 : ℝ) ^ e) :
    initialStored alpha = initial p hp e := by
  rcases alpha with ⟨a, h⟩
  dsimp only at ha
  subst a
  rfl

theorem advanceStored_eq (alpha : Word p hp) (e : ℤ) (ha : alpha.val = (2 : ℝ) ^ e)
    (st : State p hp) : advanceStored alpha st = advance e st := by
  simp [advanceStored, advance, ha]

structure Execution (p : ℕ) (hp : 2 ≤ p) where
  result : Result p hp
  trace : List Primitive

/-- Same comparisons, continuations and actual arithmetic as the frozen scan.
The single recursive result is shared; no prefix, suffix, or comparison is
recomputed by the cost monitor. -/
def execute (cmp : Comparison p hp) (alpha : Word p hp) :
    List (Word p hp) → State p hp → Execution p hp
  | [], st => ⟨⟨st, ⟨0, 0, 0, 1⟩⟩, visitTrace ++ returnTrace⟩
  | x :: xs, st =>
      if cmp.lt x st.lower then
        let r := execute cmp alpha xs st
        ⟨⟨r.result.state, r.result.work.tick 1 0⟩,
          visitTrace ++ lowerTrace ++ continueTrace ++ r.trace ++ returnTrace⟩
      else if cmp.lt x st.upper then
        let r := execute cmp alpha xs (advanceStored alpha st)
        ⟨⟨r.result.state, r.result.work.tick 2 1⟩,
          visitTrace ++ lowerTrace ++ upperTrace ++ advanceTrace ++ continueTrace ++
            r.trace ++ returnTrace⟩
      else ⟨⟨st, ⟨1, 2, 0, 1⟩⟩, visitTrace ++ lowerTrace ++ upperTrace ++ returnTrace⟩

/-- Exact preservation of both the numerical scan result and its old partial
instrumentation. The new trace is a cost refinement of that actual scan. -/
theorem execute_result_eq (cmp : Comparison p hp) (alpha : Word p hp) (e : ℤ)
    (ha : alpha.val = (2 : ℝ) ^ e) (xs : List (Word p hp)) (st : State p hp) :
    (execute cmp alpha xs st).result = scan cmp e xs st := by
  induction xs generalizing st with
  | nil => rfl
  | cons x xs ih =>
      simp only [execute, scan]
      split
      · simp only [ih]
      · split
        · rw [advanceStored_eq alpha e ha, ih]
        · rfl

/-- Complete loop trace, including all reads/writes/cursor/control/return
copies under the displayed fixed-size storage convention. -/
theorem execute_trace_length_le (cmp : Comparison p hp) (alpha : Word p hp)
    (xs : List (Word p hp)) (st : State p hp) :
    (execute cmp alpha xs st).trace.length ≤ 38 * xs.length + 11 := by
  induction xs generalizing st with
  | nil => simp [execute, visitTrace, returnTrace]
  | cons x xs ih =>
      simp only [execute]
      split
      · have h := ih st
        simp only [List.length_append]
        simp only [visitTrace, lowerTrace, continueTrace, returnTrace, List.length_cons,
          List.length_nil] at *
        omega
      · split
        · have h := ih (advanceStored alpha st)
          simp only [List.length_append]
          simp only [visitTrace, lowerTrace, upperTrace, advanceTrace, continueTrace,
            returnTrace, List.length_cons, List.length_nil] at *
          omega
        · simp [visitTrace, lowerTrace, upperTrace, returnTrace]
          omega

/-- Include setup and a final external output copy of all four state fields. -/
def runStored (cmp : Comparison p hp) (alpha : Word p hp) (xs : List (Word p hp)) :
    Execution p hp :=
  let r := execute cmp alpha xs (initialStored alpha)
  ⟨r.result, setupTrace ++ r.trace ++ returnTrace⟩

theorem runStored_result_eq (cmp : Comparison p hp) (alpha : Word p hp) (e : ℤ)
    (ha : alpha.val = (2 : ℝ) ^ e) (xs : List (Word p hp)) :
    (runStored cmp alpha xs).result = scan cmp e xs (initial p hp e) := by
  simp only [runStored, execute_result_eq cmp alpha e ha, initialStored_eq alpha e ha]

/-- Absolute source-model cost, including constant input/setup/output work. -/
theorem runStored_work_le (cmp : Comparison p hp) (alpha : Word p hp)
    (xs : List (Word p hp)) :
    (runStored cmp alpha xs).trace.length ≤ 38 * xs.length + 33 := by
  have h := execute_trace_length_le cmp alpha xs (initialStored alpha)
  simp only [runStored, List.length_append]
  simp only [setupTrace, returnTrace, List.length_cons, List.length_nil]
  omega

theorem runStored_work_linear (cmp : Comparison p hp) (alpha : Word p hp)
    (xs : List (Word p hp)) (hk : 1 ≤ xs.length) :
    (runStored cmp alpha xs).trace.length ≤ 71 * xs.length := by
  have h := runStored_work_le cmp alpha xs
  omega

/-- Full source-cost refinement retains the exact FIRST-empty answer. -/
theorem runStored_firstEmptyCutBin (cmp : Comparison p hp) (alpha : Word p hp) (e : ℤ)
    (ha : alpha.val = (2 : ℝ) ^ e) (xs : List (Word p hp))
    (hsize : xs.length + 2 < 2 ^ p) (hs : xs.Pairwise (fun a b => a.val ≤ b.val)) :
    (runStored cmp alpha xs).result.state.j =
      firstEmptyCutBin ((2 : ℝ) ^ e) (fun i => (xs.get i).val) (zpow_pos (by norm_num) e) := by
  rw [runStored_result_eq cmp alpha e ha]
  exact scan_from_initial_eq_firstEmptyCutBin cmp e xs hsize hs

end
end NumStability.FloatingPointFormat.UnboundedBinary.EmptyBinScan.SourceWork
