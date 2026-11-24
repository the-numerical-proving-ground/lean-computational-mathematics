import ComputationalMathematics.Analysis.Eigenvalues.TridiagonalRefinement

/-! Determinism of the traces used by the finite trial. -/

namespace NumStability.CertifiedTridiagonalEigenpairs

open FloatingPointFormat.UnboundedBinary ScalarWork

private theorem foldl_preserves {α : Type*} {n : ℕ} (P : α → Prop)
    (f : α → Fin n → α) (init : α) (hinit : P init)
    (hstep : ∀ i s, P s → P (f s i)) : P (Fin.foldl n f init) := by
  induction n with
  | zero => simpa only [Fin.foldl_zero] using hinit
  | succ n ih =>
    rw [Fin.foldl_succ_last]
    exact hstep (Fin.last n) _ (ih _ (fun i s h => hstep i.castSucc s h))

private theorem sweepNoFairBit_aux {n q : ℕ} {hq : 2 ≤ q}
    (f : ClippedSturmSweepResult q hq → Fin n → ClippedSturmSweepResult q hq)
    (init : ClippedSturmSweepResult q hq)
    (hinit : Step.fairBit ∉ init.trace)
    (hstep : ∀ i s, Step.fairBit ∉ s.trace → Step.fairBit ∉ (f s i).trace) :
    Step.fairBit ∉ (Step.comparison :: (Fin.foldl n f init).trace).reverse := by
  simpa using
    foldl_preserves (fun state => Step.fairBit ∉ state.trace) f init hinit hstep

private theorem sweepNoFairBit {n q : ℕ} {hq : 2 ≤ q} (r : ℕ)
    (a : Fin (n + 1) → Word q hq) (b : Fin n → Word q hq) (x : Word q hq) :
    Step.fairBit ∉ (clippedSturmSweep q hq r a b x).trace := by
  unfold clippedSturmSweep
  apply sweepNoFairBit_aux
  · change Step.fairBit ∉
      ([.scaleByPowerOfTwo, .index, .arithmetic q, .comparison, .arithmetic q,
        .comparison, .comparison, .index] : List Step).reverse
    simp
  · intro i state h
    change Step.fairBit ∉
      ([.comparison, .index, .index, .index, .arithmetic q, .arithmetic q,
        .arithmetic q, .arithmetic q, .comparison, .arithmetic q, .comparison,
        .comparison, .index] : List Step).reverse ++ state.trace
    simp [h]

/-- The rounded indexed refinement introduces no fresh random bits. -/
theorem refinementTrace_noFairBit {n q : ℕ} {hq : 2 ≤ q} (r : ℕ) (j : Fin (n + 1))
    (a : Fin (n + 1) → Word q hq) (b : Fin n → Word q hq) :
    Step.fairBit ∉ (tridiagonalRefinement r j a b).trace := by
  unfold tridiagonalRefinement
  change Step.fairBit ∉ _ ++ [.comparison, .arithmetic q, .scaleByPowerOfTwo]
  simp only [List.mem_append, not_or]
  constructor
  · generalize r + 4 = m
    induction m with
    | zero =>
      change Step.fairBit ∉ [.index, .index, .index, .index, .index, .index, .scaleByPowerOfTwo]
      simp
    | succ m ih =>
      change Step.fairBit ∉ _ ++ [.comparison, .arithmetic q, .scaleByPowerOfTwo] ++
        (clippedSturmSweep q hq r a b _).trace ++
          [.comparison, .arithmetic q, .comparison, .index, .index]
      simp [ih, sweepNoFairBit]
  · simp

end NumStability.CertifiedTridiagonalEigenpairs
