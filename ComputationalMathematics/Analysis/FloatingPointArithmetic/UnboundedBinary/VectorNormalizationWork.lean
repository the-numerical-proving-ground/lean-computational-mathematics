import ComputationalMathematics.Algorithms.Arithmetic.ScalarWork
import ComputationalMathematics.Analysis.FloatingPointArithmetic.UnboundedBinary.VectorNormalization

/-!
# Arithmetic-model work of binary vector normalization

The first pass computes the squares and accumulates their sum. The second
pass divides by the single computed norm and stores each converted component.
-/

namespace NumStability.FloatingPointFormat.UnboundedBinary.Word

open ScalarWork

private def squareFirstTrace (q : ℕ) : List Step :=
  [.index, .arithmetic q]

private def squareAccumulateTrace (q : ℕ) : List Step :=
  [.comparison, .index, .index, .arithmetic q, .arithmetic q]

private def normalizeComponentTrace (q p : ℕ) : List Step :=
  [.comparison, .index, .index, .arithmetic q, .conversion q p, .index]

/-- Charged operations for a nonempty normalization: the first square and
each ensuing square and addition, then one square root and one division
and conversion per component. Include loop tests and array accesses. -/
def normalizeToTrace (n q p : ℕ) : List Step :=
  squareFirstTrace q ++
    (List.range (n - 1)).flatMap (fun _ => squareAccumulateTrace q) ++
    [.comparison, .arithmetic q] ++
    (List.range n).flatMap (fun _ => normalizeComponentTrace q p) ++
    [.comparison]

/-- Live scalar-word counts for an out-of-place normalization. During the
first pass keep the input, cursor, accumulator and current term. During the
second keep the input, output, cursor, common denominator, loaded component
and the temporary quotient and conversion result. -/
def normalizeToLiveWords (n : ℕ) : List ℕ :=
  [n, n + 5, n + 2, 2 * n + 5, n]

private theorem length_flatMap_const {α β : Type*} (xs : List α) (ys : List β) :
    (xs.flatMap (fun _ => ys)).length = xs.length * ys.length := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [ih, Nat.add_mul, Nat.add_comm]

private theorem traceAllowed_flatMap_const {cap : ℕ} {α : Type*}
    (xs : List α) (ys : List Step) (h : TraceAllowed cap ys) :
    TraceAllowed cap (xs.flatMap (fun _ => ys)) := by
  intro step hstep
  obtain ⟨_, _, hi⟩ := List.mem_flatMap.mp hstep
  exact h step hi

theorem normalizeToTrace_work (n q p : ℕ) (hn : 1 ≤ n) :
    work (normalizeToTrace n q p) = 11 * n := by
  simp only [normalizeToTrace, work, List.length_append, length_flatMap_const,
    List.length_range, squareFirstTrace, squareAccumulateTrace, normalizeComponentTrace,
    List.length_cons, List.length_nil]
  omega

private def isArithmetic : Step → Bool
  | .arithmetic _ => true
  | _ => false

private def isConversion : Step → Bool
  | .conversion _ _ => true
  | _ => false

theorem normalizeToTrace_roundings (n q p : ℕ) (hn : 1 ≤ n) :
    ((normalizeToTrace n q p).filter isArithmetic).length = 3 * n ∧
      ((normalizeToTrace n q p).filter isConversion).length = n := by
  simp only [normalizeToTrace, List.filter_append, List.length_append, List.filter_flatMap,
    length_flatMap_const, List.length_range, squareFirstTrace, squareAccumulateTrace,
    normalizeComponentTrace, List.filter_cons, List.filter_nil, isArithmetic, isConversion,
    Bool.false_eq_true, ↓reduceIte, List.length_cons, List.length_nil]
  omega

theorem normalizeToTrace_allowed (n q p cap : ℕ) (hq : 2 ≤ q) (hp : 2 ≤ p)
    (hqc : q ≤ cap) (hpc : p ≤ cap) :
    TraceAllowed cap (normalizeToTrace n q p) := by
  have hs : TraceAllowed cap (squareAccumulateTrace q) := by
    simp [TraceAllowed, squareAccumulateTrace, Step.Allowed, hq, hqc]
  have ho : TraceAllowed cap (normalizeComponentTrace q p) := by
    simp [TraceAllowed, normalizeComponentTrace, Step.Allowed, hq, hqc, hp, hpc]
  have ha := traceAllowed_flatMap_const (List.range (n - 1)) _ hs
  have hb := traceAllowed_flatMap_const (List.range n) _ ho
  intro step hstep
  simp only [normalizeToTrace, List.mem_append] at hstep
  rcases hstep with (((hfirst | hsquares) | hsqrt) | hout) | hlast
  · exact (by
      simp [TraceAllowed, squareFirstTrace, Step.Allowed, hq, hqc] :
      TraceAllowed cap (squareFirstTrace q)) _ hfirst
  · exact ha _ hsquares
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hsqrt
    rcases hsqrt with rfl | rfl <;> simp [Step.Allowed, hq, hqc]
  · exact hb _ hout
  · simp only [List.mem_singleton] at hlast
    subst step
    trivial

theorem normalizeToLiveWords_storage (n : ℕ) :
    storage (normalizeToLiveWords n) ≤ 2 * n + 5 := by
  rw [storage_le_iff]
  simp [normalizeToLiveWords]
  omega

/-- Attach the two-pass execution schedule to the normalized output. -/
noncomputable def normalizeToExecution {n q : ℕ} {hq : 2 ≤ q}
    (p : ℕ) (hp : 2 ≤ p) (x : Fin n → Word q hq) (hx : euclidean x ≠ 0) :
    (Fin n → Word p hp) × List Step × List ℕ :=
  (normalizeTo p hp x hx, normalizeToTrace n q p, normalizeToLiveWords n)

/-- Normalizing and storing a nonzero vector costs at most eleven charged
operations per component and uses at most two vectors plus five scalar
words. All arithmetic and conversions respect the larger precision. -/
theorem normalizeToExecution_resources {n q : ℕ} {hq : 2 ≤ q}
    (p : ℕ) (hp : 2 ≤ p) (x : Fin n → Word q hq) (hx : euclidean x ≠ 0) :
    let execution := normalizeToExecution p hp x hx
    work execution.2.1 = 11 * n ∧
      TraceAllowed (max q p) execution.2.1 ∧
      storage execution.2.2 ≤ 2 * n + 5 := by
  have hn : 1 ≤ n := by
    by_contra! h
    have hz : n = 0 := by omega
    subst n
    apply hx
    ext i
    exact Fin.elim0 i
  exact ⟨normalizeToTrace_work n q p hn,
    normalizeToTrace_allowed n q p (max q p) hq hp (le_max_left ..) (le_max_right ..),
    normalizeToLiveWords_storage n⟩

end NumStability.FloatingPointFormat.UnboundedBinary.Word
