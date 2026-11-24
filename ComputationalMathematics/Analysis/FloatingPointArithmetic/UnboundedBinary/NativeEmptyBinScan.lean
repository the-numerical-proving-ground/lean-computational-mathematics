import ComputationalMathematics.Analysis.FloatingPointArithmetic.UnboundedBinary.NativeEmptyBinCut
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Pairwise

/-!
# Cached first-empty-bin scan on native words

The loop consumes a sorted stream once, caching the integer counter and both
endpoints. Its only comparison primitive takes native words and must agree
with their real denotations. The instrumented cost counts source-word
operations, not a RAM representation, allocation, or extraction of real words.
`firstEmptyCutBin` occurs only in correctness statements and proofs.
-/

namespace NumStability.FloatingPointFormat.UnboundedBinary.EmptyBinScan

noncomputable section

abbrev Word (p : ℕ) (hp : 2 ≤ p) := {x : ℝ // Native p hp x}

/-- An explicit native-word comparison primitive, with its semantic contract. -/
structure Comparison (p : ℕ) (hp : 2 ≤ p) where
  lt : Word p hp → Word p hp → Bool
  correct : ∀ a b, lt a b = true ↔ a.val < b.val

/-- `counter` stores j+1. j itself is a control index, not a numerical word. -/
structure State (p : ℕ) (hp : 2 ≤ p) where
  j : ℕ
  counter : Word p hp
  lower : Word p hp
  upper : Word p hp

variable {p : ℕ} {hp : 2 ≤ p}

/-- Exact meaning of the cached state, including positivity of the bin index. -/
def State.Valid (e : ℤ) (st : State p hp) : Prop :=
  1 ≤ st.j ∧ st.counter.val = ((st.j + 1 : ℕ) : ℝ) ∧
    st.lower.val = (st.j : ℝ) * (2 : ℝ) ^ e ∧
    st.upper.val = ((st.j + 1 : ℕ) : ℝ) * (2 : ℝ) ^ e

/-- Initialization uses the literal native 2 and one rounded binary scale. -/
def initial (p : ℕ) (hp : 2 ≤ p) (e : ℤ) : State p hp where
  j := 1
  counter := ⟨2, native_two p hp⟩
  lower := ⟨(2 : ℝ) ^ e, native_zpow p hp e⟩
  upper := ⟨roundToEven p hp (2 * (2 : ℝ) ^ e), roundToEven_native p hp _⟩

/-- One actual same-p +1, a cached-endpoint copy, and one rounded binary scale.
There is no numerical conversion of the updated control index. -/
def advance (e : ℤ) (st : State p hp) : State p hp :=
  let w : Word p hp :=
    ⟨roundToEven p hp (st.counter.val + 1), roundToEven_native p hp _⟩
  { j := st.j + 1, counter := w, lower := st.upper,
    upper := ⟨roundToEven p hp (w.val * (2 : ℝ) ^ e), roundToEven_native p hp _⟩ }

theorem initial_valid (p : ℕ) (hp : 2 ≤ p) (e : ℤ) : (initial p hp e).Valid e := by
  simp [State.Valid, initial, roundToEven_eq_self_of_native
    (native_mul_zpow (native_two p hp) e)]

theorem advance_valid (e : ℤ) (st : State p hp) (hv : st.Valid e)
    (hbound : st.j + 2 < 2 ^ p) : (advance e st).Valid e := by
  have hw : roundToEven p hp (st.counter.val + 1) = ((st.j + 2 : ℕ) : ℝ) := by
    rw [hv.2.1]
    have heq : ((st.j + 1 : ℕ) : ℝ) + 1 = ((st.j + 2 : ℕ) : ℝ) := by
      push_cast
      ring
    rw [heq]
    exact roundToEven_natCast_of_lt_two_pow p hp hbound
  have hs := roundToEven_eq_self_of_native
    (native_mul_zpow (native_natCast_of_lt_two_pow p hp hbound) e)
  simp only [State.Valid, advance]
  rw [hw, hs]
  exact ⟨by omega, by push_cast; ring, hv.2.2.2, by push_cast; ring⟩

/-- Primitive trace costs. Each update charges one rounded counter addition,
one rounded binary endpoint scale, one index increment, and one lower-endpoint
copy. Initialization has one extra scale and bounded literal/copy work. -/
structure Work where
  reads : ℕ
  comparisons : ℕ
  updates : ℕ
  controls : ℕ
  deriving Repr

def Work.tick (w : Work) (comparisons updates : ℕ) : Work :=
  ⟨w.reads + 1, w.comparisons + comparisons, w.updates + updates, w.controls + 1⟩

def Work.counterAdds (w : Work) : ℕ := w.updates
def Work.endpointScales (w : Work) : ℕ := w.updates
def Work.indexIncrements (w : Work) : ℕ := w.updates
def Work.lowerCopies (w : Work) : ℕ := w.updates

structure Result (p : ℕ) (hp : 2 ≤ p) where
  state : State p hp
  work : Work

/-- Single-suffix recursive scan. Each continuation consumes exactly the head;
endpoints are shared, and no prefix or bin search is recomputed. -/
def scan (cmp : Comparison p hp) (e : ℤ) : List (Word p hp) → State p hp → Result p hp
  | [], st => ⟨st, ⟨0, 0, 0, 1⟩⟩
  | x :: xs, st =>
      if cmp.lt x st.lower then
        let r := scan cmp e xs st
        ⟨r.state, r.work.tick 1 0⟩
      else if cmp.lt x st.upper then
        let r := scan cmp e xs (advance e st)
        ⟨r.state, r.work.tick 2 1⟩
      else ⟨st, ⟨1, 2, 0, 1⟩⟩

theorem scan_work_bounds (cmp : Comparison p hp) (e : ℤ) (xs : List (Word p hp))
    (st : State p hp) :
    (scan cmp e xs st).work.reads ≤ xs.length ∧
    (scan cmp e xs st).work.comparisons ≤ 2 * xs.length ∧
    (scan cmp e xs st).work.updates ≤ xs.length ∧
    (scan cmp e xs st).work.controls ≤ xs.length + 1 := by
  induction xs generalizing st with
  | nil => simp [scan]
  | cons x xs ih =>
      simp only [scan, List.length_cons]
      split
      · have h := ih st
        dsimp [Work.tick]
        omega
      · split
        · have h := ih (advance e st)
          dsimp [Work.tick]
          omega
        · dsimp
          omega

/-- Reachable state meanings and endpoint budget; all stored quantities are
native by type. The endpoint bound includes the final upper counter. -/
theorem scan_valid_bounds (cmp : Comparison p hp) (e : ℤ) (xs : List (Word p hp))
    (st : State p hp) (hv : st.Valid e) (hb : st.j + xs.length + 1 < 2 ^ p) :
    (scan cmp e xs st).state.Valid e ∧ st.j ≤ (scan cmp e xs st).state.j ∧
      (scan cmp e xs st).state.j ≤ st.j + xs.length := by
  induction xs generalizing st with
  | nil => simpa [scan] using hv
  | cons x xs ih =>
      simp only [scan]
      split
      · have h := ih st hv (by simp only [List.length_cons] at hb; omega)
        exact ⟨h.1, h.2.1, by dsimp only; simp only [List.length_cons]; omega⟩
      · split
        · have ha := advance_valid e st hv (by simp only [List.length_cons] at hb; omega)
          have h := ih (advance e st) ha (by
            change st.j + 1 + xs.length + 1 < 2 ^ p
            simp only [List.length_cons] at hb; omega)
          have hlo : st.j + 1 ≤ (scan cmp e xs (advance e st)).state.j := h.2.1
          have hhi : (scan cmp e xs (advance e st)).state.j ≤ st.j + 1 + xs.length := h.2.2
          exact ⟨h.1, by dsimp only; omega, by dsimp only; simp only [List.length_cons]; omega⟩
        · exact ⟨hv, le_refl _, by simp⟩

/-- Sortedness supplies the early-stop argument. Every earlier bin has an
actual input witness, and the returned bin contains no input word. -/
theorem scan_semantics (cmp : Comparison p hp) (e : ℤ) (xs : List (Word p hp))
    (st : State p hp) (hv : st.Valid e) (hb : st.j + xs.length + 1 < 2 ^ p)
    (hs : xs.Pairwise (fun a b => a.val ≤ b.val)) :
    (∀ x ∈ xs, ¬ InCutBin ((2 : ℝ) ^ e) (scan cmp e xs st).state.j x.val) ∧
    (∀ h, st.j ≤ h → h < (scan cmp e xs st).state.j →
      ∃ x ∈ xs, InCutBin ((2 : ℝ) ^ e) h x.val) := by
  have halpha : 0 < (2 : ℝ) ^ e := zpow_pos (by norm_num) _
  induction xs generalizing st with
  | nil => simp [scan]
  | cons x xs ih =>
      obtain ⟨hshead, hstail⟩ := List.pairwise_cons.mp hs
      simp only [scan]
      split
      · rename_i hlow
        have hx := (cmp.correct x st.lower).1 hlow
        have hb' : st.j + xs.length + 1 < 2 ^ p := by
          simp only [List.length_cons] at hb; omega
        obtain ⟨he, ho⟩ := ih st hv hb' hstail
        have hm : (st.j : ℝ) * (2 : ℝ) ^ e ≤
            ((scan cmp e xs st).state.j : ℝ) * (2 : ℝ) ^ e :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast
            (scan_valid_bounds cmp e xs st hv hb').2.1) halpha.le
        have hxout : x.val < ((scan cmp e xs st).state.j : ℝ) * (2 : ℝ) ^ e := by
          rw [hv.2.2.1] at hx
          exact hx.trans_le hm
        constructor
        · intro y hy
          rcases List.mem_cons.mp hy with rfl | hy
          · exact fun hbin => not_le_of_gt hxout hbin.1
          · exact he y hy
        · intro h hge hlt
          obtain ⟨y, hy, hbin⟩ := ho h hge hlt
          exact ⟨y, List.mem_cons_of_mem _ hy, hbin⟩
      · rename_i hnotlow
        split
        · rename_i hupper
          have hxupper := (cmp.correct x st.upper).1 hupper
          have hxlower : st.lower.val ≤ x.val := le_of_not_gt (by
            intro h; exact hnotlow ((cmp.correct x st.lower).2 h))
          have ha := advance_valid e st hv (by simp only [List.length_cons] at hb; omega)
          have hb' : (advance e st).j + xs.length + 1 < 2 ^ p := by
            change st.j + 1 + xs.length + 1 < 2 ^ p
            simp only [List.length_cons] at hb; omega
          obtain ⟨he, ho⟩ := ih (advance e st) ha hb' hstail
          have hm : ((st.j + 1 : ℕ) : ℝ) * (2 : ℝ) ^ e ≤
              ((scan cmp e xs (advance e st)).state.j : ℝ) * (2 : ℝ) ^ e :=
            mul_le_mul_of_nonneg_right (by exact_mod_cast
              (scan_valid_bounds cmp e xs (advance e st) ha hb').2.1) halpha.le
          have hxout : x.val < ((scan cmp e xs (advance e st)).state.j : ℝ) * (2 : ℝ) ^ e := by
            rw [hv.2.2.2] at hxupper
            exact hxupper.trans_le hm
          constructor
          · intro y hy
            rcases List.mem_cons.mp hy with rfl | hy
            · exact fun hbin => not_le_of_gt hxout hbin.1
            · exact he y hy
          · intro h hge hlt
            by_cases hsame : h = st.j
            · refine ⟨x, List.mem_cons_self, ?_⟩
              rw [hsame]
              exact ⟨by rwa [← hv.2.2.1], by rwa [← hv.2.2.2]⟩
            · obtain ⟨y, hy, hbin⟩ := ho h (by change st.j + 1 ≤ h; omega) hlt
              exact ⟨y, List.mem_cons_of_mem _ hy, hbin⟩
        · rename_i hnotupper
          have hxupper : st.upper.val ≤ x.val := le_of_not_gt (by
            intro h; exact hnotupper ((cmp.correct x st.upper).2 h))
          constructor
          · intro y hy hbin
            have hxy : x.val ≤ y.val := by
              rcases List.mem_cons.mp hy with rfl | hy
              · exact le_refl _
              · exact hshead y hy
            have hyupper := hxupper.trans hxy
            rw [hv.2.2.2] at hyupper
            exact not_lt_of_ge hyupper hbin.2
          · intro h hge hlt
            dsimp only at hlt
            omega

/-- Declarative indexed view of the supplied stream. To execute the logical
scanner on an existing list, call `scan` directly; this wrapper does not claim
that constructing `List.ofFn` or evaluating the indexed function is free. -/
def run (cmp : Comparison p hp) (e : ℤ) {k : ℕ} (s : Fin k → Word p hp) : Result p hp :=
  scan cmp e (List.ofFn s) (initial p hp e)

/-- Exact first-empty semantics, with no distinctness or nonzero assumptions.
`Nat.find` appears solely in the proof-only comparison selector. -/
theorem run_eq_firstEmptyCutBin (cmp : Comparison p hp) (e : ℤ) {k : ℕ}
    (s : Fin k → Word p hp) (hsize : k + 2 < 2 ^ p)
    (hsorted : Monotone (fun i => (s i).val)) :
    (run cmp e s).state.j = firstEmptyCutBin ((2 : ℝ) ^ e)
      (fun i => (s i).val) (zpow_pos (by norm_num) e) := by
  have hv := initial_valid p hp e
  have hb : (initial p hp e).j + (List.ofFn s).length + 1 < 2 ^ p := by
    simpa [initial, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hsize
  have hs : (List.ofFn s).Pairwise (fun a b => a.val ≤ b.val) := by
    apply List.pairwise_ofFn.mpr
    intro i j hij
    exact hsorted hij.le
  obtain ⟨he, ho⟩ := scan_semantics cmp e (List.ofFn s) (initial p hp e) hv hb hs
  have hbds := scan_valid_bounds cmp e (List.ofFn s) (initial p hp e) hv hb
  let alpha : ℝ := (2 : ℝ) ^ e
  have halpha : 0 < alpha := zpow_pos (by norm_num) _
  let j := (run cmp e s).state.j
  let first := firstEmptyCutBin alpha (fun i => (s i).val) halpha
  have hj : 1 ≤ j := hbds.1.1
  have hje : EmptyCutBin alpha (fun i => (s i).val) j := by
    intro i
    exact he (s i) (List.mem_ofFn.mpr ⟨i, rfl⟩)
  have hjocc : ∀ h, 1 ≤ h → h < j → ∃ i, InCutBin alpha h (s i).val := by
    intro h hge hlt
    obtain ⟨x, hx, hbin⟩ := ho h hge hlt
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
    exact ⟨i, hbin⟩
  have hf := firstEmptyCutBin_spec alpha (fun i => (s i).val) halpha
  change j = first
  apply le_antisymm
  · by_contra h
    obtain ⟨i, hi⟩ := hjocc first hf.1 (by omega)
    exact hf.2.2 i hi
  · by_contra h
    obtain ⟨i, hi⟩ := firstEmptyCutBin_min alpha (fun i => (s i).val) halpha hj (by omega)
    exact hje i hi

/-- Each occupied bin contributes exactly one cached state advance. -/
theorem scan_index_eq_updates (cmp : Comparison p hp) (e : ℤ) (xs : List (Word p hp))
    (st : State p hp) :
    (scan cmp e xs st).state.j = st.j + (scan cmp e xs st).work.updates := by
  induction xs generalizing st with
  | nil => simp [scan]
  | cons x xs ih =>
      simp only [scan]
      split
      · simpa [Work.tick] using ih st
      · split
        · have h := ih (advance e st)
          change (scan cmp e xs (advance e st)).state.j =
            st.j + ((scan cmp e xs (advance e st)).work.updates + 1)
          calc
            _ = (st.j + 1) + (scan cmp e xs (advance e st)).work.updates := h
            _ = _ := by omega
        · simp

/-- All cached numerical words retain their exact meanings through the scan,
and the final upper endpoint is at most (k+2)*alpha. -/
theorem run_valid_bounds (cmp : Comparison p hp) (e : ℤ) {k : ℕ}
    (s : Fin k → Word p hp) (hsize : k + 2 < 2 ^ p) :
    (run cmp e s).state.Valid e ∧
      1 ≤ (run cmp e s).state.j ∧ (run cmp e s).state.j ≤ k + 1 := by
  have h := scan_valid_bounds cmp e (List.ofFn s) (initial p hp e)
    (initial_valid p hp e) (by
      simpa [initial, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hsize)
  simpa [run, initial, Nat.add_comm] using h

/-- Loop costs, excluding bounded setup and input-stream representation.
Scale, index, and copy counts are exactly the counter-add count by the branch
cost model. No estimate is read or compared after the early-stop branch. -/
theorem run_work_bounds (cmp : Comparison p hp) (e : ℤ) {k : ℕ}
    (s : Fin k → Word p hp) :
    (run cmp e s).work.reads ≤ k ∧
    (run cmp e s).work.comparisons ≤ 2 * k ∧
    (run cmp e s).work.counterAdds ≤ k ∧
    (run cmp e s).work.endpointScales ≤ k ∧
    (run cmp e s).work.indexIncrements ≤ k ∧
    (run cmp e s).work.lowerCopies ≤ k ∧
    (run cmp e s).work.controls ≤ k + 1 := by
  have h := scan_work_bounds cmp e (List.ofFn s) (initial p hp e)
  simp only [List.length_ofFn] at h
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.1, h.2.2.1, h.2.2.1, h.2.2.2⟩

/-- Explicit logical loop work: reads, native comparisons, rounded +1, rounded
binary scales, index increments, lower-endpoint copies, and branch/termination
controls. Bounded setup and stream representation are separate. These natural
number formulas instrument the trace, not the numerical execution. -/
def Work.totalLoop (w : Work) : ℕ :=
  w.reads + w.comparisons + w.counterAdds + w.endpointScales +
    w.indexIncrements + w.lowerCopies + w.controls

theorem run_total_work_le (cmp : Comparison p hp) (e : ℤ) {k : ℕ}
    (s : Fin k → Word p hp) : (run cmp e s).work.totalLoop ≤ 8 * k + 1 := by
  have h := run_work_bounds cmp e s
  unfold Work.totalLoop
  omega

/-- Source surface: nonnegative sorted native estimates, including repeats,
zero estimates, and endpoint ties. The two sides need not be nonempty. -/
theorem run_source_cut (cmp : Comparison p hp) (e : ℤ) {k : ℕ} (hk : 1 ≤ k)
    (s : Fin k → Word p hp) (hsize : k + 2 < 2 ^ p)
    (hnonneg : ∀ i, 0 ≤ (s i).val) (hsorted : Monotone (fun i => (s i).val)) :
    let j := (run cmp e s).state.j
    let alpha := (2 : ℝ) ^ e
    1 ≤ j ∧ j ≤ k + 1 ∧
    (∀ i, (s i).val < (j : ℝ) * alpha ∨ ((j + 1 : ℕ) : ℝ) * alpha ≤ (s i).val) ∧
    (∀ i, (s i).val < (j : ℝ) * alpha → 0 ≤ (s i).val ∧ (s i).val < (2 * k : ℝ) * alpha) ∧
    (∀ i, ((j + 1 : ℕ) : ℝ) * alpha ≤ (s i).val → alpha ≤ (s i).val) := by
  dsimp only
  have hj := run_eq_firstEmptyCutBin cmp e s hsize hsorted
  rw [hj]
  have hf := firstEmptyCutBin_spec ((2 : ℝ) ^ e) (fun i => (s i).val)
    (zpow_pos (by norm_num) e)
  refine ⟨hf.1, hf.2.1, ?_, ?_, ?_⟩
  · exact firstEmptyCutBin_dichotomy _ _ _
  · intro i hlow
    exact ⟨hnonneg i, low_estimate_bound hk ((2 : ℝ) ^ e) (fun i => (s i).val)
      (zpow_pos (by norm_num) e) (i := i) hlow⟩
  · intro i hhigh
    exact high_estimate_ge_alpha _ _ _ hhigh

/-- Correctness directly for the supplied input list: `xs.get` is used only
in the mathematical selector, never to execute the scan or fetch prefixes. -/
theorem scan_from_initial_eq_firstEmptyCutBin (cmp : Comparison p hp) (e : ℤ)
    (xs : List (Word p hp)) (hsize : xs.length + 2 < 2 ^ p)
    (hsorted : xs.Pairwise (fun a b => a.val ≤ b.val)) :
    (scan cmp e xs (initial p hp e)).state.j =
      firstEmptyCutBin ((2 : ℝ) ^ e) (fun i => (xs.get i).val)
        (zpow_pos (by norm_num) e) := by
  have hs : Monotone (fun i => (xs.get i).val) := by
    intro i j hij
    obtain rfl | hlt := Fin.eq_or_lt_of_le hij
    · exact le_refl _
    · exact hsorted.rel_get_of_lt hlt
  have h := run_eq_firstEmptyCutBin cmp e xs.get hsize hs
  simpa only [run, List.ofFn_get] using h

/-- Direct-list exact cached-state meanings and final index bound. -/
theorem scan_from_initial_valid_bounds (cmp : Comparison p hp) (e : ℤ)
    (xs : List (Word p hp)) (hsize : xs.length + 2 < 2 ^ p) :
    (scan cmp e xs (initial p hp e)).state.Valid e ∧
    1 ≤ (scan cmp e xs (initial p hp e)).state.j ∧
    (scan cmp e xs (initial p hp e)).state.j ≤ xs.length + 1 := by
  have h := run_valid_bounds cmp e xs.get hsize
  simpa only [run, List.ofFn_get] using h

/-- For the source nonempty input, the explicitly enumerated loop primitives
have a linear bound. Setup, input storage, and bit-level arithmetic remain
separate from this logical trace theorem. -/
theorem scan_from_initial_linear_work (cmp : Comparison p hp) (e : ℤ)
    (xs : List (Word p hp)) (hk : 1 ≤ xs.length) :
    (scan cmp e xs (initial p hp e)).work.totalLoop ≤ 9 * xs.length := by
  have h := run_total_work_le cmp e xs.get
  simp only [run, List.ofFn_get] at h
  omega

end
end NumStability.FloatingPointFormat.UnboundedBinary.EmptyBinScan
