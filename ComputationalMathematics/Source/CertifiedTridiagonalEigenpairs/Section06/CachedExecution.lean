import ComputationalMathematics.Source.CertifiedTridiagonalEigenpairs.Section06.ScoreSelection
import ComputationalMathematics.Source.CertifiedTridiagonalEigenpairs.Section06.InverseRecurrence

/-! # Cached rounded tridiagonal inverse-column execution -/

namespace NumStability.CertifiedTridiagonalEigenpairs

open FloatingPointFormat.UnboundedBinary

/-- Append the next value from the most recently stored value, using each update once. -/
private def cacheScanLoop {α : Type*} (next : ℕ → α → α) :
    (remaining index : ℕ) → Vector α (index + 1) → Vector α (index + 1 + remaining)
  | 0, _, values => values
  | remaining + 1, index, values =>
    let updated := values.push (next index values[index])
    (cacheScanLoop next remaining (index + 1) updated).cast (by omega)

private theorem cacheScanLoop_get {α : Type*} (next : ℕ → α → α)
    (f : ℕ → α) (hf : ∀ i, i < bound → f (i + 1) = next i (f i))
    (remaining index : ℕ) (values : Vector α (index + 1))
    (hbound : index + remaining ≤ bound)
    (hvalues : ∀ j (hj : j < index + 1), values[j] = f j)
    (j : ℕ) (hj : j < index + 1 + remaining) :
    (cacheScanLoop next remaining index values)[j] = f j := by
  induction remaining generalizing index with
  | zero => exact hvalues j hj
  | succ remaining ih =>
    rw [cacheScanLoop, Vector.getElem_cast]
    apply ih (index + 1) _ (by omega)
    intro k hk
    by_cases h : k < index + 1
    · rw [Vector.getElem_push_lt h, hvalues]
    · obtain rfl : k = index + 1 := by omega
      rw [Vector.getElem_push_eq, hvalues, hf index (by omega)]

private def cacheScan {α : Type*} (seed : α) (next : ℕ → α → α) : (n : ℕ) → Vector α n
  | 0 => #v[]
  | n + 1 =>
    let initial : Vector α 1 := ⟨(Array.emptyWithCapacity (n + 1)).push seed, by simp⟩
    (cacheScanLoop next n 0 initial).cast (by omega)

private theorem cacheScan_get {α : Type*} (seed : α) (next : ℕ → α → α)
    (f : ℕ → α) (hseed : seed = f 0)
    (hnext : ∀ j, j + 1 < n → f (j + 1) = next j (f j))
    (j : ℕ) (hj : j < n) : (cacheScan seed next n)[j] = f j := by
  obtain _ | n := n
  · omega
  rw [cacheScan, Vector.getElem_cast]
  apply cacheScanLoop_get next f (bound := n) _ n 0 _ (by omega) _ j
  · intro i hi
    exact hnext i (by omega)
  · intro i hi
    obtain rfl : i = 0 := by omega
    simpa using hseed

/-- One rounded diagonal and two directional pivot arrays. The right array
is stored in sweep order, from the last row toward the first. -/
structure VectorCachedSweeps (n : ℕ) where
  diagonal : Vector ℝ n
  left : Vector (ℝ × ℝ) n
  rightReversed : Vector (ℝ × ℝ) n

/-- Read the right pivot in original row order. -/
def VectorCachedSweeps.right {n : ℕ} (s : VectorCachedSweeps n) (i : Fin n) : ℝ × ℝ :=
  s.rightReversed[n - 1 - i.val]'(by omega)

private noncomputable def readDiagonal {n : ℕ} (h : Vector ℝ n) (i : ℕ) : ℝ :=
  if hi : i < n then h[i] else 0

private noncomputable def pivotScan (q : ℕ) (hq : 2 ≤ q) (n : ℕ)
    (h b : ℕ → ℝ) (η : ℝ) : Vector (ℝ × ℝ) n :=
  cacheScan (h 0, η)
    (fun i d => vectorPivotStep q hq (h (i + 1)) η (b i) d.1 d.2) n

private theorem pivotScan_get (q : ℕ) (hq : 2 ≤ q) (n : ℕ)
    (h a b : ℕ → ℝ) (η : ℝ) (hh : ∀ i < n, h i = roundToEven q hq (a i))
    (i : Fin n) : (pivotScan q hq n h b η).get i = vectorLeftSweep q hq a b η i.val := by
  unfold pivotScan Vector.get
  apply cacheScan_get _ _ (vectorLeftSweep q hq a b η)
  · rw [vectorLeftSweep, hh 0 (by have := i.isLt; omega)]
  · intro j hj
    rw [vectorLeftSweep, hh (j + 1) hj]

/-- Round the diagonal once, then fill each directional array with one
recurrence step per edge. -/
noncomputable def vectorCachedSweeps (q : ℕ) (hq : 2 ≤ q) (n : ℕ)
    (a b : ℕ → ℝ) (η : ℝ) : VectorCachedSweeps n :=
  let h := Vector.ofFn (fun i : Fin n => roundToEven q hq (a i.val))
  ⟨h, pivotScan q hq n (readDiagonal h) b η,
    pivotScan q hq n (fun j => readDiagonal h (n - 1 - j)) (fun j => b (n - 2 - j)) η⟩

@[simp] theorem vectorCachedSweeps_diagonal (q : ℕ) (hq : 2 ≤ q) (n : ℕ)
    (a b : ℕ → ℝ) (η : ℝ) (i : Fin n) :
    (vectorCachedSweeps q hq n a b η).diagonal.get i = roundToEven q hq (a i.val) := by
  simp [vectorCachedSweeps, Vector.get]

@[simp] theorem vectorCachedSweeps_left (q : ℕ) (hq : 2 ≤ q) (n : ℕ)
    (a b : ℕ → ℝ) (η : ℝ) (i : Fin n) :
    (vectorCachedSweeps q hq n a b η).left.get i = vectorLeftSweep q hq a b η i.val := by
  unfold vectorCachedSweeps
  apply pivotScan_get
  intro j hj
  simp [readDiagonal, hj]

@[simp] theorem vectorCachedSweeps_right (q : ℕ) (hq : 2 ≤ q) (n : ℕ)
    (a b : ℕ → ℝ) (η : ℝ) (i : Fin n) :
    (vectorCachedSweeps q hq n a b η).right i = vectorRightSweep q hq n a b η i.val := by
  unfold VectorCachedSweeps.right vectorCachedSweeps vectorRightSweep
  change (pivotScan q hq n _ _ η).get ⟨n - 1 - i.val, by have := i.isLt; omega⟩ = _
  apply pivotScan_get
  intro j hj
  have hj' : n - 1 - j < n := by omega
  simp [readDiagonal, hj']

/-- Compute a twist with the already stored left and right pivots. -/
noncomputable def VectorCachedSweeps.twist {n : ℕ} (s : VectorCachedSweeps n)
    (q : ℕ) (hq : 2 ≤ q) (b : ℕ → ℝ) (η : ℝ) (r : Fin n) : ℝ × ℝ :=
  let left := if hl : 0 < r.val then s.left.get ⟨r.val - 1, by omega⟩ else (0, η)
  let right := if hr : r.val + 1 < n then s.right ⟨r.val + 1, hr⟩ else (0, η)
  let bL := if 0 < r.val then b (r.val - 1) else 0
  let bR := if r.val + 1 < n then b r.val else 0
  vectorTwist q hq (s.diagonal.get r) η bL left.1 left.2 bR right.1 right.2

@[simp] theorem vectorCachedSweeps_twist (q : ℕ) (hq : 2 ≤ q) (n : ℕ)
    (a b : ℕ → ℝ) (η : ℝ) (r : Fin n) :
    (vectorCachedSweeps q hq n a b η).twist q hq b η r = vectorSweepTwist q hq n a b η r := by
  by_cases hl : 0 < r.val <;> by_cases hr : r.val + 1 < n <;>
    simp [VectorCachedSweeps.twist, vectorSweepTwist, hl, hr]

/-- Store the twist's real component, squared modulus and imaginary
reciprocal. Only the selected twist will need a real reciprocal. -/
structure VectorCachedScore where
  twistRe : ℝ
  modulus : ℝ
  score : ℝ

/-- Compute every twist and score once from the directional arrays. -/
noncomputable def VectorCachedSweeps.scores {n : ℕ} (s : VectorCachedSweeps n)
    (q : ℕ) (hq : 2 ≤ q) (b : ℕ → ℝ) (η : ℝ) : Vector VectorCachedScore n :=
  Vector.ofFn fun i =>
    let γ := s.twist q hq b η i
    let modulus := vectorSquaredModulus q hq γ.1 γ.2
    ⟨γ.1, modulus, roundToEven q hq (γ.2 / modulus)⟩

@[simp] theorem vectorCachedSweeps_score (q : ℕ) (hq : 2 ≤ q) (n : ℕ)
    (a b : ℕ → ℝ) (η : ℝ) (i : Fin n) :
    ((vectorCachedSweeps q hq n a b η).scores q hq b η |>.get i).score =
      vectorScore q hq (vectorSweepTwist q hq n a b η i) := by
  simp [VectorCachedSweeps.scores, Vector.get, vectorScore]

/-- Read the selected score and finish its reciprocal with one rounded division. -/
noncomputable def VectorCachedScore.reciprocal (q : ℕ) (hq : 2 ≤ q)
    (data : VectorCachedScore) : ℂ :=
  ⟨roundToEven q hq (data.twistRe / data.modulus), data.score⟩

@[simp] theorem vectorCachedSweeps_reciprocal (q : ℕ) (hq : 2 ≤ q) (n : ℕ)
    (a b : ℕ → ℝ) (η : ℝ) (i : Fin n) :
    ((vectorCachedSweeps q hq n a b η).scores q hq b η |>.get i).reciprocal q hq =
      let γ := vectorSweepTwist q hq n a b η i
      roundedTwistReciprocal q hq γ.1 γ.2 := by
  simp [VectorCachedSweeps.scores, VectorCachedScore.reciprocal, Vector.get,
    roundedTwistReciprocal]

private noncomputable def cachedOutwardEdge {n : ℕ} (s : VectorCachedSweeps n)
    (b : ℕ → ℝ) (r i : Fin n) : InversePathEdge :=
  let left := i.val < r.val
  let d := if left then s.left.get i else s.right i
  ⟨if left then b i.val else b (i.val - 1), 0, d.1, d.2⟩

private theorem cachedOutwardEdge_eq (q : ℕ) (hq : 2 ≤ q) (n : ℕ)
    (a b : ℕ → ℝ) (η : ℝ) (r i : Fin n) :
    cachedOutwardEdge (vectorCachedSweeps q hq n a b η) b r i =
      vectorOutwardEdge q hq n a b η r i 0 := by
  simp [cachedOutwardEdge, vectorOutwardEdge]

private noncomputable def cachedLeftColumn {n : ℕ} (s : VectorCachedSweeps n)
    (q : ℕ) (hq : 2 ≤ q) (b : ℕ → ℝ) (r : Fin n) (root : ℂ) : Vector ℂ (r.val + 1) :=
  cacheScan root (fun j prev =>
    let i : Fin n := ⟨r.val - (j + 1), by have := r.isLt; omega⟩
    roundedInverseStep q hq (cachedOutwardEdge s b r i) prev) (r.val + 1)

private noncomputable def cachedRightColumn {n : ℕ} (s : VectorCachedSweeps n)
    (q : ℕ) (hq : 2 ≤ q) (b : ℕ → ℝ) (r : Fin n) (root : ℂ) : Vector ℂ (n - r.val) :=
  cacheScan root (fun j prev =>
    if hi : r.val + (j + 1) < n then
      roundedInverseStep q hq (cachedOutwardEdge s b r ⟨r.val + (j + 1), hi⟩) prev
    else 0) (n - r.val)

/-- Propagate the rounded root outward, retaining each parent once. The
two scans run in increasing distance from the root on their own sides. -/
noncomputable def VectorCachedSweeps.column {n : ℕ} (s : VectorCachedSweeps n)
    (q : ℕ) (hq : 2 ≤ q) (b : ℕ → ℝ) (r : Fin n) (root : ℂ) : Vector ℂ n :=
  let left := cachedLeftColumn s q hq b r root
  let right := cachedRightColumn s q hq b r root
  Vector.ofFn fun i =>
    if i.val ≤ r.val then left[r.val - i.val]'(by omega)
    else right[i.val - r.val]'(by have := i.isLt; omega)

private theorem cachedLeftColumn_get (q : ℕ) (hq : 2 ≤ q) (n : ℕ)
    (a b : ℕ → ℝ) (η : ℝ) (r : Fin n) (root : ℂ)
    (hroot : root = vectorRoundedInverseColumn q hq n a b η r r)
    (j : ℕ) (hj : j < r.val + 1) :
    (cachedLeftColumn (vectorCachedSweeps q hq n a b η) q hq b r root)[j] =
      vectorRoundedInverseColumn q hq n a b η r ⟨r.val - j, by have := r.isLt; omega⟩ := by
  let w := vectorRoundedInverseColumn q hq n a b η r
  let row (k : ℕ) : Fin n := ⟨r.val - k, by have := r.isLt; omega⟩
  unfold cachedLeftColumn
  apply cacheScan_get _ _ (fun k => w (row k))
  · simpa [row, w, Fin.eta] using hroot
  · intro k hk
    change w (row (k + 1)) = roundedInverseStep q hq
      (cachedOutwardEdge (vectorCachedSweeps q hq n a b η) b r (row (k + 1))) (w (row k))
    rw [cachedOutwardEdge_eq]
    have hrow : (row (k + 1)).val < r.val := by dsimp [row]; omega
    have hpar : vectorParent r (row (k + 1)) = row k := by
      apply Fin.ext
      rw [vectorParent, dif_pos hrow]
      dsimp [row]
      omega
    have hne : row (k + 1) ≠ r := fun he => (Nat.ne_of_lt hrow) (congrArg Fin.val he)
    have hstep : w (row (k + 1)) = roundedInverseStep q hq
        (vectorOutwardEdge q hq n a b η r (row (k + 1)) 0)
        (w (vectorParent r (row (k + 1)))) :=
      (vectorRoundedInverseColumn_recurrence q hq n a b η r).2.2 _ hne
    rw [hstep, hpar]

private theorem cachedRightColumn_get (q : ℕ) (hq : 2 ≤ q) (n : ℕ)
    (a b : ℕ → ℝ) (η : ℝ) (r : Fin n) (root : ℂ)
    (hroot : root = vectorRoundedInverseColumn q hq n a b η r r)
    (j : ℕ) (hj : j < n - r.val) :
    (cachedRightColumn (vectorCachedSweeps q hq n a b η) q hq b r root)[j] =
      vectorRoundedInverseColumn q hq n a b η r ⟨r.val + j, by omega⟩ := by
  let w := vectorRoundedInverseColumn q hq n a b η r
  let row (k : ℕ) : Fin n := if h : r.val + k < n then ⟨r.val + k, h⟩ else r
  have hrow (k : ℕ) (hk : r.val + k < n) : row k = ⟨r.val + k, hk⟩ := dif_pos hk
  unfold cachedRightColumn
  change _ = w ⟨r.val + j, by omega⟩
  rw [← hrow j (by omega)]
  apply cacheScan_get _ _ (fun k => w (row k))
  · simpa [row, w, r.isLt, Fin.eta] using hroot
  · intro k hk
    have hi : r.val + (k + 1) < n := by omega
    rw [dif_pos hi, cachedOutwardEdge_eq]
    change w (row (k + 1)) = roundedInverseStep q hq
      (vectorOutwardEdge q hq n a b η r ⟨r.val + (k + 1), hi⟩ 0) (w (row k))
    have hrowlt : r.val < (row (k + 1)).val := by rw [hrow (k + 1) hi]; simp
    have hpar : vectorParent r (row (k + 1)) = row k := by
      apply Fin.ext
      rw [vectorParent, dif_neg (not_lt_of_ge hrowlt.le), dif_pos hrowlt]
      change (row (k + 1)).val - 1 = (row k).val
      rw [hrow (k + 1) hi, hrow k (by omega)]
      simp
    have hne : row (k + 1) ≠ r := fun he => (Nat.ne_of_gt hrowlt) (congrArg Fin.val he)
    have hstep : w (row (k + 1)) = roundedInverseStep q hq
        (vectorOutwardEdge q hq n a b η r (row (k + 1)) 0)
        (w (vectorParent r (row (k + 1)))) :=
      (vectorRoundedInverseColumn_recurrence q hq n a b η r).2.2 _ hne
    rw [hstep, hpar]
    congr 2
    exact hrow (k + 1) hi

/-- Pointwise agreement of the once-per-edge computation with the inverse
path denotation. -/
theorem vectorCachedSweeps_column_get (q : ℕ) (hq : 2 ≤ q) (n : ℕ)
    (a b : ℕ → ℝ) (η : ℝ) (r : Fin n) (root : ℂ)
    (hroot : root = vectorRoundedInverseColumn q hq n a b η r r) (i : Fin n) :
    ((vectorCachedSweeps q hq n a b η).column q hq b r root).get i =
      vectorRoundedInverseColumn q hq n a b η r i := by
  change ((vectorCachedSweeps q hq n a b η).column q hq b r root)[i.val] = _
  simp only [VectorCachedSweeps.column, Vector.getElem_ofFn]
  by_cases h : i.val ≤ r.val
  · rw [if_pos h, cachedLeftColumn_get q hq n a b η r root hroot]
    congr 1
    exact Fin.ext (by change r.val - (r.val - i.val) = i.val; omega)
  · rw [if_neg h, cachedRightColumn_get q hq n a b η r root hroot]
    congr 1
    exact Fin.ext (by change r.val + (i.val - r.val) = i.val; omega)

/-- Cached column at a prescribed root, including the diagonal and sweeps. -/
noncomputable def vectorCachedColumn (q : ℕ) (hq : 2 ≤ q) (n : ℕ)
    (a b : ℕ → ℝ) (η : ℝ) (r : Fin n) : Vector ℂ n :=
  let s := vectorCachedSweeps q hq n a b η
  let γ := s.twist q hq b η r
  s.column q hq b r (roundedTwistReciprocal q hq γ.1 γ.2)

@[simp] theorem vectorCachedColumn_get (q : ℕ) (hq : 2 ≤ q) (n : ℕ)
    (a b : ℕ → ℝ) (η : ℝ) (r i : Fin n) :
    (vectorCachedColumn q hq n a b η r).get i = vectorRoundedInverseColumn q hq n a b η r i := by
  unfold vectorCachedColumn
  apply vectorCachedSweeps_column_get
  rw [vectorCachedSweeps_twist, (vectorRoundedInverseColumn_recurrence q hq n a b η r).1]

private noncomputable def cacheSelectLoop {n : ℕ} (scores : Vector VectorCachedScore n) :
    (remaining index : ℕ) → index + remaining ≤ n → Fin n → Fin n
  | 0, _, _, best => best
  | remaining + 1, index, h, best =>
    let current : Fin n := ⟨index, by omega⟩
    let best' := if (scores.get best).score < (scores.get current).score then current else best
    cacheSelectLoop scores remaining (index + 1) (by omega) best'

private def CacheScoreBest {n : ℕ} (scores : Vector VectorCachedScore n)
    (limit : ℕ) (best : Fin n) : Prop :=
  best.val < limit ∧
    ∀ i : Fin n, i.val < limit → (scores.get i).score ≤ (scores.get best).score ∧
      ((scores.get i).score = (scores.get best).score → best ≤ i)

private theorem cacheSelectLoop_best {n : ℕ} (scores : Vector VectorCachedScore n)
    (remaining index : ℕ) (h : index + remaining ≤ n) (best : Fin n)
    (hbest : CacheScoreBest scores index best) :
    CacheScoreBest scores (index + remaining) (cacheSelectLoop scores remaining index h best) := by
  induction remaining generalizing index best with
  | zero => exact hbest
  | succ remaining ih =>
    rw [cacheSelectLoop, show index + (remaining + 1) = index + 1 + remaining by omega]
    apply ih
    let current : Fin n := ⟨index, by omega⟩
    change CacheScoreBest scores (index + 1)
      (if (scores.get best).score < (scores.get current).score then current else best)
    split_ifs with himprove
    · refine ⟨by change index < index + 1; omega, fun i hi => ?_⟩
      by_cases he : i = current
      · subst i
        simp
      · have hlt : i.val < index := by
          by_contra! hn
          exact he (Fin.ext (by dsimp [current]; omega))
        have hstrict := lt_of_le_of_lt (hbest.2 i hlt).1 himprove
        exact ⟨hstrict.le, fun heq => (hstrict.ne heq).elim⟩
    · refine ⟨by have := hbest.1; omega, fun i hi => ?_⟩
      by_cases hlt : i.val < index
      · exact hbest.2 i hlt
      · have he : i = current := Fin.ext (by dsimp [current]; omega)
        subst i
        exact ⟨le_of_not_gt himprove, fun _ => by
          change best.val ≤ index
          exact hbest.1.le⟩

/-- Scan the cached scores in row order, replacing the incumbent only after
a strict improvement. This reads one new score per comparison. -/
noncomputable def vectorCachedScoreIndex {n : ℕ} (hn : 0 < n)
    (scores : Vector VectorCachedScore n) : Fin n :=
  cacheSelectLoop scores (n - 1) 1 (by omega) ⟨0, hn⟩

theorem vectorCachedScoreIndex_spec {n : ℕ} (hn : 0 < n)
    (scores : Vector VectorCachedScore n) :
    let r := vectorCachedScoreIndex hn scores
    (∀ i, (scores.get i).score ≤ (scores.get r).score) ∧
      (∀ i, (scores.get i).score = (scores.get r).score → r ≤ i) := by
  have hs : CacheScoreBest scores 1 ⟨0, hn⟩ := by
    refine ⟨by change 0 < 1; decide, fun i hi => ?_⟩
    obtain rfl : i = ⟨0, hn⟩ := Fin.ext (by change i.val = 0; omega)
    simp
  have hbest : CacheScoreBest scores (1 + (n - 1)) (vectorCachedScoreIndex hn scores) :=
    cacheSelectLoop_best scores (n - 1) 1 (by omega) ⟨0, hn⟩ hs
  rw [show 1 + (n - 1) = n by omega] at hbest
  exact ⟨fun i => (hbest.2 i i.isLt).1, fun i => (hbest.2 i i.isLt).2⟩

/-- Selected row and its rounded inverse column in original row order. -/
structure VectorCachedExecution (n : ℕ) where
  root : Fin n
  column : Vector ℂ n

/-- Fill both sweeps, compute and scan the stored scores, then propagate one
column. The scores and selected reciprocal share the stored squared modulus. -/
noncomputable def vectorCachedExecution (q : ℕ) (hq : 2 ≤ q) (n : ℕ) (hn : 0 < n)
    (a b : ℕ → ℝ) (η : ℝ) : VectorCachedExecution n :=
  let sweeps := vectorCachedSweeps q hq n a b η
  let scores := sweeps.scores q hq b η
  let r := vectorCachedScoreIndex hn scores
  let root := (scores.get r).reciprocal q hq
  ⟨r, sweeps.column q hq b r root⟩

theorem vectorCachedExecution_root (q : ℕ) (hq : 2 ≤ q) (n : ℕ) (hn : 0 < n)
    (a b : ℕ → ℝ) (η : ℝ) :
    (vectorCachedExecution q hq n hn a b η).root = vectorSelectedIndex q hq n hn a b η := by
  let scores := (vectorCachedSweeps q hq n a b η).scores q hq b η
  let r := vectorCachedScoreIndex hn scores
  let r' := vectorSelectedIndex q hq n hn a b η
  change r = r'
  obtain ⟨hmax, hleast⟩ := vectorCachedScoreIndex_spec hn scores
  obtain ⟨hmax', hleast'⟩ := vectorSelectedIndex_spec q hq n hn a b η
  have heq : (scores.get r').score = (scores.get r).score := by
    apply le_antisymm (hmax r')
    simpa only [scores, vectorCachedSweeps_score] using hmax' r
  exact le_antisymm (hleast r' heq) (hleast' r (by
    simpa only [scores, vectorCachedSweeps_score] using heq.symm))

theorem vectorCachedExecution_column_get (q : ℕ) (hq : 2 ≤ q) (n : ℕ) (hn : 0 < n)
    (a b : ℕ → ℝ) (η : ℝ) (i : Fin n) :
    (vectorCachedExecution q hq n hn a b η).column.get i =
      vectorRoundedInverseColumn q hq n a b η (vectorCachedExecution q hq n hn a b η).root i := by
  unfold vectorCachedExecution
  apply vectorCachedSweeps_column_get
  rw [vectorCachedSweeps_reciprocal, (vectorRoundedInverseColumn_recurrence q hq n a b η _).1]

end NumStability.CertifiedTridiagonalEigenpairs
