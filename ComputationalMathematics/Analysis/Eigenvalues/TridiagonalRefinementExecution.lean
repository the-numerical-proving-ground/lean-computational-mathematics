import ComputationalMathematics.Analysis.Eigenvalues.TridiagonalRefinement
import ComputationalMathematics.Analysis.FloatingPointArithmetic.UnboundedBinary.ClippedSturmExecution

/-!
# Constant-workspace indexed tridiagonal refinement

The arithmetic loop carries the two current endpoints. It calls the
constant-workspace Sturm sweep at each stored midpoint. The instrumented loop
provides a specification for its output and resource use.
-/

namespace NumStability.FloatingPointFormat.UnboundedBinary

open PaddedRefinement ScalarWork

noncomputable section

variable {n q : ℕ} {hq : 2 ≤ q}

private inductive RefineInstruction (n q : ℕ) (hq : 2 ≤ q) : Type → Type where
  | initialize (r : ℕ) : RefineInstruction n q hq (Word q hq × Endpoints q hq)
  | probe (interval : Endpoints q hq) : RefineInstruction n q hq (Word q hq)
  | count (r : ℕ) (a : Fin (n + 1) → Word q hq) (b : Fin n → Word q hq)
      (x : Word q hq) : RefineInstruction n q hq ℕ
  | retain (t : Word q hq) (j : Fin (n + 1)) (interval : Endpoints q hq) (x : Word q hq)
      (count : ℕ) : RefineInstruction n q hq (Endpoints q hq)
  | finish (interval : Endpoints q hq) : RefineInstruction n q hq (Word q hq)

@[inline] private def RefineInstruction.eval {α : Type} : RefineInstruction n q hq α → α
  | .initialize r => (padding q hq r, initial q hq)
  | .probe interval => midpoint interval
  | .count r a b x => (runClippedSturmSweep q hq r a b x).count
  | .retain t j interval x k => update t j interval x k
  | .finish interval => midpoint interval

private abbrev RefineInterpreter (n q : ℕ) (hq : 2 ≤ q) (m : Type → Type) :=
  {α : Type} → RefineInstruction n q hq α → m α

@[inline] private def refinePure : RefineInterpreter n q hq Id :=
  fun instruction => instruction.eval

@[inline] private def refineStep {m : Type → Type} [Monad m] (run : RefineInterpreter n q hq m)
    (r : ℕ) (j : Fin (n + 1)) (a : Fin (n + 1) → Word q hq) (b : Fin n → Word q hq)
    (t : Word q hq) (interval : Endpoints q hq) : m (Endpoints q hq) := do
  let x ← run (.probe interval)
  let count ← run (.count r a b x)
  run (.retain t j interval x count)

@[inline] private def refineExecutionStep (r : ℕ) (j : Fin (n + 1))
    (a : Fin (n + 1) → Word q hq) (b : Fin n → Word q hq) (t : Word q hq)
    (interval : Endpoints q hq) : Endpoints q hq :=
  (refineStep refinePure r j a b t interval).run

/-- The interval held after exactly `m` updates. The accumulator holds the
two current endpoints, and each sweep has finished before the next update. -/
def runTridiagonalRefinementInterval (r : ℕ) (j : Fin (n + 1))
    (a : Fin (n + 1) → Word q hq) (b : Fin n → Word q hq) (m : ℕ) :
    Endpoints q hq :=
  let (t, first) := RefineInstruction.eval (.initialize (n := n) (q := q) (hq := hq) r)
  Fin.foldl m (fun interval _ => refineExecutionStep r j a b t interval) first

/-- The stored label produced after exactly `r + 4` clipped-count updates. -/
def runTridiagonalRefinement (r : ℕ) (j : Fin (n + 1))
    (a : Fin (n + 1) → Word q hq) (b : Fin n → Word q hq) : Word q hq :=
  RefineInstruction.eval (.finish (n := n) (runTridiagonalRefinementInterval r j a b (r + 4)))

/-- Every prefix of the constant-workspace loop carries the endpoints of the
instrumented loop with the same input and the same number of updates. -/
theorem runTridiagonalRefinementInterval_eq (r : ℕ) (j : Fin (n + 1))
    (a : Fin (n + 1) → Word q hq) (b : Fin n → Word q hq) (m : ℕ) :
    runTridiagonalRefinementInterval r j a b m = tridiagonalRefinement_intervalAt r j a b m := by
  induction m with
  | zero =>
    simp only [runTridiagonalRefinementInterval, Fin.foldl_zero]
    rfl
  | succ m ih =>
    change Fin.foldl (m + 1) (fun interval _ =>
      refineExecutionStep r j a b (padding q hq r) interval) (initial q hq) = _
    rw [Fin.foldl_succ_last]
    change refineExecutionStep r j a b (padding q hq r)
      (runTridiagonalRefinementInterval r j a b m) = _
    rw [ih]
    let interval := tridiagonalRefinement_intervalAt r j a b m
    change update (padding q hq r) j interval (midpoint interval)
      (runClippedSturmSweep q hq r a b (midpoint interval)).count =
      update (padding q hq r) j interval (midpoint interval)
        (clippedSturmSweep q hq r a b (midpoint interval)).count
    rw [(runClippedSturmSweep_eq q hq r a b (midpoint interval)).2]

/-- The final native word agrees with the instrumented computation. -/
theorem runTridiagonalRefinement_eq (r : ℕ) (j : Fin (n + 1))
    (a : Fin (n + 1) → Word q hq) (b : Fin n → Word q hq) :
    runTridiagonalRefinement r j a b = (tridiagonalRefinement r j a b).label := by
  rw [runTridiagonalRefinement, runTridiagonalRefinementInterval_eq]
  rfl

/-- Work and peak live words of the run under the scalar arithmetic model. -/
structure TridiagonalRefinementUsage where
  work : ℕ
  peakWords : ℕ

/-- Resident input arrays plus slots for the tolerance exponent, rank, loop
bound and cursor, padding, two endpoints, midpoint, count, and candidate.
An active Sturm call uses additional space. -/
private def outerWords (n : ℕ) : ℕ := (n + 1) + n + 10

private def charge (n operations scratch : ℕ) (prior : TridiagonalRefinementUsage) :
    TridiagonalRefinementUsage :=
  ⟨prior.work + operations, max prior.peakWords (outerWords n + scratch)⟩

/-- The second interpreter charges the operations of each instruction. Its
counters and the nested Sturm observations are part of the mathematical
accounting. The numerical interpreter uses the same phase program. -/
private def refineMeasure : RefineInterpreter n q hq (StateM TridiagonalRefinementUsage) :=
  fun instruction prior =>
    match instruction with
    | .initialize r =>
      -- Initialize the loop and endpoints, form the exponent, and scale three.
      ((RefineInstruction.initialize (n := n) (q := q) (hq := hq) r).eval, charge n 7 0 prior)
    | .probe interval =>
      -- Test the loop bound, add the endpoints, and halve the rounded sum.
      (midpoint interval, charge n 3 0 prior)
    | .count r a b x =>
      let sweep := recordedClippedSturmExecution q hq r a b x
      (sweep.1.count, charge n (work sweep.2.trace) (storage sweep.2.liveWords) prior)
    | .retain t j interval x k =>
      -- Compare the count to the rank, form and compare the candidate,
      -- store the selected endpoint, then advance the cursor.
      (update t j interval x k, charge n 5 0 prior)
    | .finish interval =>
      -- Test the loop bound and assemble the final rounded midpoint.
      (midpoint interval, charge n 3 0 prior)

private def measuredStart (n q : ℕ) (hq : 2 ≤ q) (r : ℕ) :
    (Word q hq × Endpoints q hq) × TridiagonalRefinementUsage :=
  (refineMeasure (.initialize (n := n) (q := q) (hq := hq) r)).run ⟨0, 0⟩

private def measuredStep (r : ℕ) (j : Fin (n + 1))
    (a : Fin (n + 1) → Word q hq) (b : Fin n → Word q hq) (t : Word q hq)
    (prior : Endpoints q hq × TridiagonalRefinementUsage) :
    Endpoints q hq × TridiagonalRefinementUsage :=
  (refineStep refineMeasure r j a b t prior.1).run prior.2

private def measuredPrefix (r : ℕ) (j : Fin (n + 1))
    (a : Fin (n + 1) → Word q hq) (b : Fin n → Word q hq) (m : ℕ) :
    Endpoints q hq × TridiagonalRefinementUsage :=
  let setup := measuredStart n q hq r
  Fin.foldl m (fun prior _ => measuredStep r j a b setup.1.1 prior) (setup.1.2, setup.2)

/-- The observed word and resource use, obtained by interpreting the same
instruction phases with charged work and peak slot occupancy. The observation
is separate from the numerical loop's accumulator and return value. -/
def measuredTridiagonalRefinement (r : ℕ) (j : Fin (n + 1))
    (a : Fin (n + 1) → Word q hq) (b : Fin n → Word q hq) :
    Word q hq × TridiagonalRefinementUsage :=
  let prior := measuredPrefix r j a b (r + 4)
  (refineMeasure (.finish (n := n) prior.1)).run prior.2

private theorem measuredStep_interval (r : ℕ) (j : Fin (n + 1))
    (a : Fin (n + 1) → Word q hq) (b : Fin n → Word q hq) (t : Word q hq)
    (prior : Endpoints q hq × TridiagonalRefinementUsage) :
    (measuredStep r j a b t prior).1 = refineExecutionStep r j a b t prior.1 := by
  let x := midpoint prior.1
  change update t j prior.1 x (recordedClippedSturmExecution q hq r a b x).1.count =
    update t j prior.1 x (runClippedSturmSweep q hq r a b x).count
  rw [recordedClippedSturmExecution_eq_run]

private theorem measuredPrefix_interval (r : ℕ) (j : Fin (n + 1))
    (a : Fin (n + 1) → Word q hq) (b : Fin n → Word q hq) (m : ℕ) :
    (measuredPrefix r j a b m).1 = runTridiagonalRefinementInterval r j a b m := by
  induction m with
  | zero => simp only [measuredPrefix, runTridiagonalRefinementInterval, Fin.foldl_zero]; rfl
  | succ m ih =>
    unfold measuredPrefix runTridiagonalRefinementInterval
    dsimp only
    rw [Fin.foldl_succ_last, Fin.foldl_succ_last]
    change (measuredStep r j a b (padding q hq r) (measuredPrefix r j a b m)).1 =
      refineExecutionStep r j a b (padding q hq r) (runTridiagonalRefinementInterval r j a b m)
    rw [measuredStep_interval, ih]

/-- Running the meter gives exactly the numerical interpreter's returned word. -/
theorem measuredTridiagonalRefinement_eq_run (r : ℕ) (j : Fin (n + 1))
    (a : Fin (n + 1) → Word q hq) (b : Fin n → Word q hq) :
    (measuredTridiagonalRefinement r j a b).1 = runTridiagonalRefinement r j a b := by
  change midpoint (measuredPrefix r j a b (r + 4)).1 = _
  rw [measuredPrefix_interval]
  rfl

private theorem measuredPrefix_bound (r : ℕ) (j : Fin (n + 1))
    (a : Fin (n + 1) → Word q hq) (b : Fin n → Word q hq) (m : ℕ) :
    let usage := (measuredPrefix r j a b m).2
    usage.work ≤ 7 + (13 * (n + 1) + 8) * m ∧ usage.peakWords ≤ outerWords n + 14 := by
  induction m with
  | zero =>
    simp only [measuredPrefix, Fin.foldl_zero]
    change 7 ≤ 7 + (13 * (n + 1) + 8) * 0 ∧ max 0 (outerWords n + 0) ≤ outerWords n + 14
    simp
  | succ m ih =>
    let prefixState := measuredPrefix r j a b m
    let x := midpoint prefixState.1
    let sweep := clippedSturmExecutionResources q hq r a b x
    obtain ⟨hwork, _, hspace⟩ := runClippedSturmSweep_resources q hq r a b x
    change work sweep.trace ≤ 13 * (n + 1) at hwork
    change storage sweep.liveWords ≤ 14 at hspace
    change prefixState.2.work ≤ _ ∧ prefixState.2.peakWords ≤ _ at ih
    unfold measuredPrefix
    dsimp only
    rw [Fin.foldl_succ_last]
    change prefixState.2.work + 3 + work sweep.trace + 5 ≤ _ ∧
      max (max (max prefixState.2.peakWords (outerWords n + 0))
        (outerWords n + storage sweep.liveWords)) (outerWords n + 0) ≤ _
    refine ⟨?_, ?_⟩
    · rw [Nat.mul_succ]
      have := ih.1
      omega
    · rcases ih with ⟨_, hp⟩
      simp only [Nat.max_le, Nat.add_zero]
      exact ⟨⟨⟨hp, by omega⟩, by omega⟩, by omega⟩

/-- Work and peak resident words of the numerical loop, via its measured
interpreter. No step retains a previous count or stores a transcript. -/
theorem runTridiagonalRefinement_resources (r : ℕ) (j : Fin (n + 1))
    (a : Fin (n + 1) → Word q hq) (b : Fin n → Word q hq) :
    let result := measuredTridiagonalRefinement r j a b
    result.1 = (tridiagonalRefinement r j a b).label ∧
      result.2.work ≤ (13 * (n + 1) + 8) * (r + 4) + 10 ∧
      result.2.peakWords ≤ 26 * (n + 1) := by
  have hlabel := (measuredTridiagonalRefinement_eq_run r j a b).trans
    (runTridiagonalRefinement_eq r j a b)
  obtain ⟨hwork, hpeak⟩ := measuredPrefix_bound r j a b (r + 4)
  let prior := measuredPrefix r j a b (r + 4)
  change prior.2.work ≤ _ at hwork
  change prior.2.peakWords ≤ _ at hpeak
  refine ⟨hlabel, ?_, ?_⟩
  · change prior.2.work + 3 ≤ _
    omega
  · change max prior.2.peakWords (outerWords n + 0) ≤ _
    rw [Nat.max_le]
    unfold outerWords at hpeak ⊢
    exact ⟨by omega, by omega⟩

end

end NumStability.FloatingPointFormat.UnboundedBinary
