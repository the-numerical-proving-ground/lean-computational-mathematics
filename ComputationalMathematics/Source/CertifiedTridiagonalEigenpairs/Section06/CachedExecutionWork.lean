import ComputationalMathematics.Algorithms.Arithmetic.ScalarWork
import ComputationalMathematics.Source.CertifiedTridiagonalEigenpairs.Section06.CachedExecution

/-! # Scalar work and storage of the cached inverse-column stages -/

namespace NumStability.CertifiedTridiagonalEigenpairs

open ScalarWork

private def cachedCharges (q indices tests arithmetic : ℕ) : List Step :=
  List.replicate indices .index ++ List.replicate tests .comparison ++
    List.replicate arithmetic (.arithmetic q)

private def cachedPass (visits : ℕ) (body : List Step) : List Step :=
  (List.range visits).flatMap (fun _ => body)

private theorem cachedPass_length (visits : ℕ) (body : List Step) :
    (cachedPass visits body).length = visits * body.length := by
  have aux (is : List ℕ) : (is.flatMap (fun _ => body)).length = is.length * body.length := by
    induction is with
    | nil => simp
    | cons i is ih => simp [ih, Nat.add_mul, Nat.add_comm]
  unfold cachedPass
  rw [aux, List.length_range]

private theorem cachedPass_allowed {cap : ℕ} (visits : ℕ) {body : List Step}
    (h : TraceAllowed cap body) : TraceAllowed cap (cachedPass visits body) := by
  intro step hs
  obtain ⟨_, _, hj⟩ := List.mem_flatMap.mp hs
  exact h _ hj

private theorem cachedCharges_allowed {q cap : ℕ} (hq : 2 ≤ q) (hcap : q ≤ cap)
    (indices tests arithmetic : ℕ) :
    TraceAllowed cap (cachedCharges q indices tests arithmetic) := by
  intro step hs
  rcases List.mem_append.mp hs with hs | ha
  · rcases List.mem_append.mp hs with hi | ht
    · have he := (List.mem_replicate.mp hi).2
      subst step
      trivial
    · have he := (List.mem_replicate.mp ht).2
      subst step
      trivial
  · have he := (List.mem_replicate.mp ha).2
    subst step
    exact ⟨hq, hcap⟩

private def cachedDiagonalTrace (n q : ℕ) : List Step :=
  cachedCharges q 1 1 0 ++ cachedPass n (cachedCharges q 5 1 1)

private def cachedPivotTrace (n q : ℕ) : List Step :=
  -- The seed reads the rounded diagonal. Each later visit reads its
  -- predecessor, diagonal and original edge, and appends one pivot pair.
  cachedCharges q 6 3 0 ++ cachedPass (n - 1) (cachedCharges q 12 4 9)

private def cachedScoreTrace (n q : ℕ) : List Step :=
  -- Two seven-operation corrections, four component updates, and the
  -- four-operation score. The charge covers both endpoint tests.
  cachedCharges q 1 1 0 ++ cachedPass n (cachedCharges q 14 7 22)

private def cachedSelectionTrace (n q : ℕ) : List Step :=
  -- The initial incumbent is row zero. Each later row requires two score
  -- reads, two cursor updates, a loop test and one strict comparison.
  cachedCharges q 1 1 0 ++ cachedPass (n - 1) (cachedCharges q 4 2 0)

private def cachedOutwardTrace (left right q : ℕ) : List Step :=
  -- Seed each array with the already computed reciprocal. The quotient
  -- takes seven arithmetic operations and the product takes six. Charge
  -- two extra operations for the two exact sign changes.
  cachedCharges q 8 4 0 ++
    cachedPass left (cachedCharges q 13 6 15) ++
    cachedPass right (cachedCharges q 13 6 15)

private def cachedReorderTrace (n q : ℕ) : List Step :=
  -- Assemble the two arrays in row order, reading one component per row.
  cachedCharges q 1 1 0 ++ cachedPass n (cachedCharges q 6 2 0)

/-- A worst-case scalar charge schedule for the actual cached passes.
Zero-edge branches use fewer arithmetic operations than the charged
nonzero branch. -/
def vectorCachedExecutionTrace (q : ℕ) {n : ℕ} (r : Fin n) : List Step :=
  cachedDiagonalTrace n q ++ cachedPivotTrace n q ++ cachedPivotTrace n q ++
    cachedScoreTrace n q ++ cachedSelectionTrace n q ++
    cachedCharges q 1 0 1 ++ cachedOutwardTrace r.val (n - r.val - 1) q ++
    cachedReorderTrace n q

/-- Work by pass, including the exact lengths of the two outward scans. -/
theorem vectorCachedExecutionTrace_stageWork (q : ℕ) {n : ℕ} (r : Fin n) :
    work (cachedDiagonalTrace n q) = 7 * n + 2 ∧
      work (cachedPivotTrace n q) = 25 * (n - 1) + 9 ∧
      work (cachedScoreTrace n q) = 43 * n + 2 ∧
      work (cachedSelectionTrace n q) = 6 * (n - 1) + 2 ∧
      r.val + (n - r.val - 1) = n - 1 ∧
      work (cachedOutwardTrace r.val (n - r.val - 1) q) = 34 * (n - 1) + 12 ∧
      work (cachedReorderTrace n q) = 8 * n + 2 := by
  simp [work, cachedDiagonalTrace, cachedPivotTrace, cachedScoreTrace, cachedSelectionTrace,
    cachedOutwardTrace, cachedReorderTrace, cachedCharges, cachedPass_length]
  have := r.isLt
  omega

theorem vectorCachedExecutionTrace_work (q : ℕ) {n : ℕ} (r : Fin n) :
    work (vectorCachedExecutionTrace q r) = 148 * n - 50 := by
  simp [vectorCachedExecutionTrace, work, cachedDiagonalTrace, cachedPivotTrace,
    cachedScoreTrace, cachedSelectionTrace, cachedOutwardTrace, cachedReorderTrace,
    cachedCharges, cachedPass_length]
  have := r.isLt
  omega

theorem vectorCachedExecutionTrace_allowed (q cap : ℕ) {n : ℕ} (r : Fin n)
    (hq : 2 ≤ q) (hcap : q ≤ cap) : TraceAllowed cap (vectorCachedExecutionTrace q r) := by
  have append {xs ys : List Step} (hx : TraceAllowed cap xs) (hy : TraceAllowed cap ys) :
      TraceAllowed cap (xs ++ ys) := by
    intro step hs
    exact (List.mem_append.mp hs).elim (hx step) (hy step)
  have group := cachedCharges_allowed hq hcap
  have pass (visits indices tests arithmetic : ℕ) :
      TraceAllowed cap (cachedPass visits (cachedCharges q indices tests arithmetic)) :=
    cachedPass_allowed visits (group indices tests arithmetic)
  unfold vectorCachedExecutionTrace cachedDiagonalTrace cachedPivotTrace cachedScoreTrace
    cachedSelectionTrace cachedOutwardTrace cachedReorderTrace
  repeat' first | apply group | apply pass | apply append

/-- Scalar words reserved for the read-only tridiagonal input, rounded
diagonal, directional pivot pairs, cached score triples, two outward arrays,
the final column, and a constant workspace. Count full array capacities
even when a fill is still in progress or an earlier array can be released. -/
def vectorCachedExecutionLiveWords {n : ℕ} (r : Fin n) : List ℕ :=
  [2 * n + 32, 3 * n + 32, 7 * n + 32, 10 * n + 32,
    10 * n + 2 * (r.val + 1) + 2 * (n - r.val) + 32,
    12 * n + 2 * (r.val + 1) + 2 * (n - r.val) + 32]

theorem vectorCachedExecutionLiveWords_storage {n : ℕ} (r : Fin n) :
    storage (vectorCachedExecutionLiveWords r) ≤ 14 * n + 34 := by
  rw [storage_le_iff]
  simp [vectorCachedExecutionLiveWords]
  have := r.isLt
  omega

/-- The cache retains linear storage and uses at most 148 charged operations
per row before normalization. All charged floating-point operations use the
working precision. -/
theorem vectorCachedExecution_resources (q cap : ℕ) (hq : 2 ≤ q) (hcap : q ≤ cap)
    (n : ℕ) (hn : 0 < n) (a b : ℕ → ℝ) (η : ℝ) :
    let result := vectorCachedExecution q hq n hn a b η
    let trace := vectorCachedExecutionTrace q result.root
    let live := vectorCachedExecutionLiveWords result.root
    work trace ≤ 148 * n ∧ TraceAllowed cap trace ∧ storage live ≤ 14 * n + 34 := by
  intro result trace live
  exact ⟨(vectorCachedExecutionTrace_work q result.root).trans_le (Nat.sub_le ..),
    vectorCachedExecutionTrace_allowed q cap result.root hq hcap,
    vectorCachedExecutionLiveWords_storage result.root⟩

end NumStability.CertifiedTridiagonalEigenpairs
