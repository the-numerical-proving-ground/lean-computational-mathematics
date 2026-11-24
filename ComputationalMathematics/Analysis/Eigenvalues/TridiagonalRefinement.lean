import ComputationalMathematics.Analysis.Eigenvalues.PaddedRefinement
import ComputationalMathematics.Analysis.Eigenvalues.TridiagonalSturmCount
import ComputationalMathematics.Analysis.FloatingPointArithmetic.UnboundedBinary.ClippedSturmSweep

/-!
# Indexed tridiagonal refinement by the clipped Sturm sweep

The counted execution uses one call to the native clipped sweep per update.
Instrumentation records arithmetic and live words at the corresponding stages.
-/

namespace NumStability.FloatingPointFormat.UnboundedBinary

open ScalarWork PaddedRefinement NoisyRankCertificate

noncomputable section
open Classical

variable {n q : ℕ} {hq : 2 ≤ q}

private structure RefinementState (q : ℕ) (hq : 2 ≤ q) where
  interval : Endpoints q hq
  trace : List Step
  liveWords : List ℕ

/-- The returned label and the work and live-word observations of the run. -/
structure TridiagonalRefinementResult (q : ℕ) (hq : 2 ≤ q) where
  label : Word q hq
  trace : List Step
  liveWords : List ℕ

/-- Set up the loop bound and cursor, both endpoints, and the exponent and
exact scaling of the padding. -/
private def refineInitTrace : List Step :=
  [.index, .index, .index, .index, .index, .index, .scaleByPowerOfTwo]

/-- Test the loop bound, add the endpoints, and halve their rounded sum. -/
private def refineBeforeCount (q : ℕ) : List Step :=
  [.comparison, .arithmetic q, .scaleByPowerOfTwo]

/-- Test the rank, form and compare the padded candidate, store the chosen
endpoint, and advance the cursor. -/
private def refineAfterCount (q : ℕ) : List Step :=
  [.comparison, .arithmetic q, .comparison, .index, .index]

private def refineFinishTrace (q : ℕ) : List Step :=
  [.comparison, .arithmetic q, .scaleByPowerOfTwo]

/-- The diagonal and off-diagonal are resident through all calls. The outer
loop needs at most ten additional words for the tolerance exponent, rank,
loop bound and cursor, padding, endpoints, midpoint, count, and candidate. -/
private def residentWords (n : ℕ) : ℕ :=
  (n + 1) + n

private def refinementLoop (r : ℕ) (j : Fin (n + 1))
    (a : Fin (n + 1) → Word q hq) (b : Fin n → Word q hq) (t : Word q hq) :
    ℕ → RefinementState q hq
  | 0 => ⟨initial q hq, refineInitTrace, [residentWords n + 10]⟩
  | m + 1 =>
    let prev := refinementLoop r j a b t m
    let x := midpoint prev.interval
    let sweep := clippedSturmSweep q hq r a b x
    let interval := update t j prev.interval x sweep.count
    let trace := prev.trace ++ refineBeforeCount q ++ sweep.trace ++ refineAfterCount q
    let liveWords := prev.liveWords ++
      (sweep.liveWords.map fun words => residentWords n + 10 + words) ++ [residentWords n + 10]
    ⟨interval, trace, liveWords⟩

/-- The stored interval after the first `m` updates of the clipped-count loop. -/
def tridiagonalRefinement_intervalAt (r : ℕ) (j : Fin (n + 1))
    (a : Fin (n + 1) → Word q hq) (b : Fin n → Word q hq) (m : ℕ) :
    Endpoints q hq :=
  (refinementLoop r j a b (padding q hq r) m).interval

/-- Fixed-length refinement with the actual clipped sweep as its count.
The padding is formed once and the two stored endpoints are retained across
calls. Each count reuses the same scratch storage. -/
def tridiagonalRefinement (r : ℕ) (j : Fin (n + 1))
    (a : Fin (n + 1) → Word q hq) (b : Fin n → Word q hq) :
    TridiagonalRefinementResult q hq :=
  let t := padding q hq r
  let result := refinementLoop r j a b t (r + 4)
  ⟨midpoint result.interval, result.trace ++ refineFinishTrace q,
    result.liveWords ++ [residentWords n + 10]⟩

private theorem refinementLoop_interval (r : ℕ) (j : Fin (n + 1))
    (a : Fin (n + 1) → Word q hq) (b : Fin n → Word q hq) (m : ℕ) :
    (refinementLoop r j a b (padding q hq r) m).interval =
      iterate r j (fun x => (clippedSturmSweep q hq r a b x).count) m := by
  induction m with
  | zero => rfl
  | succ m ih => simp only [refinementLoop, iterate, step, ih]

/-- The counted execution returns the padded-refinement midpoint. -/
theorem tridiagonalRefinement_label (r : ℕ) (j : Fin (n + 1))
    (a : Fin (n + 1) → Word q hq) (b : Fin n → Word q hq) :
    (tridiagonalRefinement r j a b).label =
      refine r j (fun x => (clippedSturmSweep q hq r a b x).count) := by
  simp only [tridiagonalRefinement, refine, refinementLoop_interval]

private theorem traceAllowed_append {cap : ℕ} {xs ys : List Step}
    (hx : TraceAllowed cap xs) (hy : TraceAllowed cap ys) :
    TraceAllowed cap (xs ++ ys) := by
  intro s hs
  rcases List.mem_append.mp hs with h | h
  · exact hx s h
  · exact hy s h

private theorem refinementLoop_resources (r : ℕ) (j : Fin (n + 1))
    (a : Fin (n + 1) → Word q hq) (b : Fin n → Word q hq) (m : ℕ) :
    let result := refinementLoop r j a b (padding q hq r) m
    work result.trace ≤ (13 * (n + 1) + 8) * m + 7 ∧
      TraceAllowed q result.trace ∧ storage result.liveWords ≤ residentWords n + 24 := by
  induction m with
  | zero =>
    simp [refinementLoop, refineInitTrace, work, TraceAllowed, Step.Allowed, storage]
  | succ m ih =>
    obtain ⟨hwork, hallowed, hspace⟩ := ih
    let prev := refinementLoop r j a b (padding q hq r) m
    let x := midpoint prev.interval
    let sweep := clippedSturmSweep q hq r a b x
    obtain ⟨hsweep, hcap⟩ := clippedSturmSweep_work q hq r a b x
    have hsweepSpace := clippedSturmSweep_storage q hq r a b x
    change work (prev.trace ++ refineBeforeCount q ++ sweep.trace ++ refineAfterCount q) ≤ _ ∧
      TraceAllowed q (prev.trace ++ refineBeforeCount q ++ sweep.trace ++ refineAfterCount q) ∧
      storage (prev.liveWords ++
        sweep.liveWords.map (fun words => residentWords n + 10 + words) ++
        [residentWords n + 10]) ≤ _
    refine ⟨?_, ?_, ?_⟩
    · change work prev.trace ≤ _ at hwork
      change work sweep.trace ≤ _ at hsweep
      simp only [work, List.length_append, refineBeforeCount, refineAfterCount,
        List.length_cons, List.length_nil] at *
      rw [Nat.mul_succ]
      omega
    · have hbefore : TraceAllowed q (refineBeforeCount q) := by
        simp [TraceAllowed, refineBeforeCount, Step.Allowed, hq]
      have hafter : TraceAllowed q (refineAfterCount q) := by
        simp [TraceAllowed, refineAfterCount, Step.Allowed, hq]
      exact traceAllowed_append (traceAllowed_append (traceAllowed_append hallowed hbefore) hcap)
        hafter
    · rw [storage_le_iff] at hspace hsweepSpace ⊢
      intro words hwords
      rcases List.mem_append.mp hwords with hmid | hlast
      · rcases List.mem_append.mp hmid with hprev | hcount
        · exact hspace words hprev
        · obtain ⟨scratch, hscratch, rfl⟩ := List.mem_map.mp hcount
          have := hsweepSpace scratch hscratch
          omega
      · have := List.mem_singleton.mp hlast
        omega

/-- One count per iteration, constant charged overhead per iteration, and
linear peak storage even when the resident matrix words are included. -/
theorem tridiagonalRefinement_resources (r : ℕ) (j : Fin (n + 1))
    (a : Fin (n + 1) → Word q hq) (b : Fin n → Word q hq) :
    let result := tridiagonalRefinement r j a b
    work result.trace ≤ (13 * (n + 1) + 8) * (r + 4) + 10 ∧
      TraceAllowed q result.trace ∧ storage result.liveWords ≤ 26 * (n + 1) := by
  obtain ⟨hwork, hallowed, hspace⟩ := refinementLoop_resources r j a b (r + 4)
  let state := refinementLoop r j a b (padding q hq r) (r + 4)
  change work (state.trace ++ refineFinishTrace q) ≤ _ ∧
    TraceAllowed q (state.trace ++ refineFinishTrace q) ∧
    storage (state.liveWords ++ [residentWords n + 10]) ≤ _
  refine ⟨?_, ?_, ?_⟩
  · change work state.trace ≤ _ at hwork
    simp only [work, List.length_append, refineFinishTrace, List.length_cons,
      List.length_nil] at *
    omega
  · have hfinish : TraceAllowed q (refineFinishTrace q) := by
      simp [TraceAllowed, refineFinishTrace, Step.Allowed, hq]
    exact traceAllowed_append hallowed hfinish
  · rw [storage_le_iff] at hspace ⊢
    intro words hwords
    rcases List.mem_append.mp hwords with hprev | hlast
    · have := hspace words hprev
      unfold residentWords at this
      omega
    · have := List.mem_singleton.mp hlast
      unfold residentWords at this
      omega

private theorem abs_ascendingEigenvalue_le_operatorNorm {m : ℕ}
    {A : Matrix (Fin m) (Fin m) ℝ} (hA : A.IsHermitian) (i : Fin m) :
    |ascendingEigenvalue hA i| ≤ realMatrixOperatorNorm A := by
  let v := hermitianOrderedEigenbasis hA i.rev
  have hv : ‖v‖ = 1 := (hermitianOrderedEigenbasis hA).orthonormal.norm_eq_one i.rev
  have heig : realMatrixContinuousLinearMap A v = ascendingEigenvalue hA i • v :=
    hermitianOrderedEigenbasis_apply hA i.rev
  have h := (realMatrixContinuousLinearMap A).le_opNorm v
  rw [heig, norm_smul, hv, mul_one, mul_one, Real.norm_eq_abs] at h
  exact h

/-- The actual clipped-sweep refinement preserves the enclosure and achieves
the stated final accuracy from its strict-count certificate. The spectral norm
bound places the requested eigenvalue in the initial interval. -/
theorem tridiagonalRefinement_enclosures_and_accuracy_of_count_bracket (r : ℕ) (j : Fin (n + 1))
    (a : Fin (n + 1) → Word q hq) (b : Fin n → Word q hq)
    (hr : 2 ≤ r) (hq' : r + 8 ≤ q)
    (hH : realMatrixOperatorNorm (sturmTridiagonal (fun i => (a i).value)
      (fun i => (b i).value)) ≤ 3 / 2)
    (hcount : ∀ x : Word q hq, -2 ≤ x.value → x.value ≤ 2 →
      let eigenvalues := ascendingEigenvalue (sturmTridiagonal_isHermitian
        (fun i => (a i).value) (fun i => (b i).value))
      let count := (clippedSturmSweep q hq r a b x).count
      strictBelowCount eigenvalues (x.value - unitRoundoff r) ≤ count ∧
        count ≤ strictBelowCount eigenvalues (x.value + unitRoundoff r)) :
    let eigenvalues := ascendingEigenvalue (sturmTridiagonal_isHermitian
      (fun i => (a i).value) (fun i => (b i).value))
    (∀ m,
      let interval := tridiagonalRefinement_intervalAt r j a b m
      let x := midpoint interval
      interval.Contains (eigenvalues j) ∧
        interval.lower.value ≤ x.value ∧ x.value ≤ interval.upper.value) ∧
    |(tridiagonalRefinement r j a b).label.value - eigenvalues j| ≤ (423 / 256) * unitRoundoff r ∧
      (423 / 256) * unitRoundoff r < 2 * unitRoundoff r := by
  let hHerm := sturmTridiagonal_isHermitian (fun i => (a i).value) (fun i => (b i).value)
  have hbound := abs_le.mp ((abs_ascendingEigenvalue_le_operatorNorm hHerm j).trans hH)
  simp only [tridiagonalRefinement_label, tridiagonalRefinement_intervalAt, refinementLoop_interval]
  exact refine_enclosures_and_accuracy j (ascendingEigenvalue_monotone hHerm) (by linarith [hbound.1])
    (by linarith [hbound.2]) _ hcount hr hq'

end

end NumStability.FloatingPointFormat.UnboundedBinary
