import ComputationalMathematics.Analysis.Eigenvalues.TridiagonalRefinementExecution
import ComputationalMathematics.Source.CertifiedTridiagonalEigenpairs.BidiagonalSVDLabelRefinement
import ComputationalMathematics.Source.CertifiedTridiagonalEigenpairs.BidiagonalSVDEmptyBin
import Mathlib.Data.List.Forall2

/-!
# Cached nonnegative singular labels before the first empty bin

The scan consumes the requested indices in ascending order. Each index has one
native scalar refinement, one comparison against zero, and one comparison
against the preceding maximum. Both maxima select an existing stored word.
-/

open Matrix

namespace NumStability.CertifiedTridiagonalEigenpairs

open FloatingPointFormat.UnboundedBinary ScalarWork

private noncomputable def largerWord {q : ℕ} {hq : 2 ≤ q} (a b : Word q hq) : Word q hq :=
  if a.value ≤ b.value then b else a

@[simp] private theorem largerWord_value {q : ℕ} {hq : 2 ≤ q} (a b : Word q hq) :
    (largerWord a b).value = max a.value b.value := by
  unfold largerWord
  split
  · rename_i h
    exact (max_eq_right h).symm
  · rename_i h
    exact (max_eq_left (le_of_not_ge h)).symm

/-- The numeric cache holds only the stored label stream. -/
structure BidiagonalLabelCache (q : ℕ) (hq : 2 ≤ q) where
  labels : List (EmptyBinScan.Word q hq)

private noncomputable def cacheScan {q : ℕ} {hq : 2 ≤ q} {ι : Type*}
    (refine : ι → Word q hq) : Word q hq → List ι → List (EmptyBinScan.Word q hq)
  | _, [] => []
  | prev, i :: is =>
      let best := largerWord prev (largerWord .zero (refine i))
      ⟨best.value, best.native_value⟩ :: cacheScan refine best is

private theorem cacheScan_spec {q : ℕ} {hq : 2 ≤ q} {ι : Type*}
    (refine : ι → Word q hq) (truth : ι → ℝ) (ε : ℝ)
    (hε : 0 ≤ ε) (rs : List ι)
    (hmono : rs.Pairwise (fun i j => truth i ≤ truth j))
    (hnonneg : ∀ i ∈ rs, 0 ≤ truth i)
    (happrox : ∀ i ∈ rs, |(refine i).value - truth i| ≤ ε)
    (prev : Word q hq) (hprev : ∀ i ∈ rs, prev.value ≤ truth i + ε) :
    let labels := cacheScan refine prev rs
    (∀ w ∈ labels, prev.value ≤ w.val) ∧
    labels.Pairwise (fun a b => a.val ≤ b.val) ∧
    List.Forall₂ (fun w i => |w.val - truth i| ≤ ε) labels rs := by
  induction rs generalizing prev with
  | nil => simp [cacheScan]
  | cons i is ih =>
    let best := largerWord prev (largerWord .zero (refine i))
    have hbest : best.value = max prev.value (max 0 (refine i).value) := by
      simp only [best, largerWord_value]
      rfl
    have hmem : i ∈ i :: is := List.mem_cons_self
    have hstored : |best.value - truth i| ≤ ε := by
      have hraw := abs_le.mp (happrox i hmem)
      rw [hbest, abs_le]
      constructor
      · have hle : (refine i).value ≤ max prev.value (max 0 (refine i).value) :=
          (le_max_right _ _).trans (le_max_right _ _)
        linarith
      · have hup : max prev.value (max 0 (refine i).value) ≤ truth i + ε :=
          max_le (hprev i hmem) (max_le (add_nonneg (hnonneg i hmem) hε)
            (by linarith only [hraw.2]))
        linarith only [hup]
    have hmono' := List.pairwise_cons.mp hmono
    have htail (j : ι) (hj : j ∈ is) : j ∈ i :: is := List.mem_cons_of_mem i hj
    have hnext (j : ι) (hj : j ∈ is) : best.value ≤ truth j + ε := by
      have hi := (abs_le.mp hstored).2
      linarith [hmono'.1 j hj]
    obtain ⟨hlo, hs, ha⟩ := ih hmono'.2 (fun j hj => hnonneg j (htail j hj))
      (fun j hj => happrox j (htail j hj)) best hnext
    have hpb : prev.value ≤ best.value := by rw [hbest]; exact le_max_left _ _
    change (∀ w ∈ (⟨best.value, best.native_value⟩ :: cacheScan refine best is),
        prev.value ≤ w.val) ∧
      (⟨best.value, best.native_value⟩ :: cacheScan refine best is).Pairwise _ ∧
      List.Forall₂ _ (⟨best.value, best.native_value⟩ :: cacheScan refine best is) (i :: is)
    refine ⟨?_, List.pairwise_cons.mpr ⟨hlo, hs⟩, List.Forall₂.cons hstored ha⟩
    intro w hw
    rcases List.mem_cons.mp hw with rfl | hw
    · exact hpb
    · exact hpb.trans (hlo w hw)

/-- Instrumentation for the same rank loop. Its transcript is used only for
proofs of operation counts and precision, outside the numeric cache. -/
private def cacheScanTrace {ι : Type*} (refineTrace : ι → List Step) : List ι → List Step
  | [] => []
  | i :: is =>
      [.index] ++ refineTrace i ++ [.comparison, .comparison, .index, .index] ++
        cacheScanTrace refineTrace is

private theorem cacheScan_trace {q : ℕ} {ι : Type*} (refineTrace : ι → List Step) (rs : List ι)
    (W : ℕ) (hwork : ∀ i ∈ rs, work (refineTrace i) ≤ W)
    (hbits : ∀ i ∈ rs, TraceAllowed q (refineTrace i)) :
    work (cacheScanTrace refineTrace rs) ≤ rs.length * (W + 5) ∧
      TraceAllowed q (cacheScanTrace refineTrace rs) := by
  induction rs with
  | nil => simp [cacheScanTrace, work, TraceAllowed]
  | cons i is ih =>
    have hmem : i ∈ i :: is := List.mem_cons_self
    have htail (j : ι) (hj : j ∈ is) : j ∈ i :: is := List.mem_cons_of_mem i hj
    obtain ⟨hw, hb⟩ := ih (fun j hj => hwork j (htail j hj)) (fun j hj => hbits j (htail j hj))
    have hi := hwork i hmem
    refine ⟨?_, ?_⟩
    · simp only [cacheScanTrace, work, List.length_append, List.length_cons, List.length_nil,
        Nat.succ_mul] at hw hi ⊢
      omega
    · intro op hop
      simp only [cacheScanTrace, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hop
      rcases hop with (((rfl | hs) | (rfl | rfl | rfl | rfl)) | ht)
      all_goals first | trivial | exact hbits i hmem op hs | exact hb op ht

/-- The native refinement reuses the widened edge table for the entire rank list.
The prefix cache stores precisely the words subsequently read by the bin scan. -/
noncomputable def bidiagonalCachedRefinement {p n k : ℕ} {hp : 2 ≤ p} (hn : 0 < n)
    (upper : Bool) (C : Matrix (Fin n) (Fin n) (Word p hp)) (I : Fin k → Fin n) :
    BidiagonalLabelCache (svdLabelPrecision k p) (svdLabelPrecision_ge_two k p) :=
  let e := bidiagonalRefinementEdges hn k upper C
  let refine := fun i => runTridiagonalRefinement (svdAuxiliaryPrecision k p + 7)
    ((bidiagonalRefinementCoord hn).symm (Fin.natAdd n i)) (fun _ => .zero) e
  ⟨cacheScan refine .zero (List.ofFn I)⟩

private theorem bidiagonalCachedRefinement_labels_eq_recorded {p n k : ℕ} {hp : 2 ≤ p}
    (hn : 0 < n) (upper : Bool) (C : Matrix (Fin n) (Fin n) (Word p hp)) (I : Fin k → Fin n) :
    (bidiagonalCachedRefinement hn upper C I).labels =
      cacheScan (fun i => (bidiagonalRefineLabel hn k upper C i).label) .zero (List.ofFn I) := by
  simp only [bidiagonalCachedRefinement, runTridiagonalRefinement_eq, bidiagonalRefineLabel]

/-- The resource transcript for the exact rank schedule in the numeric cache.
The label computation does not materialize this transcript. -/
noncomputable def bidiagonalCachedRefinementTrace {p n k : ℕ} {hp : 2 ≤ p} (hn : 0 < n)
    (upper : Bool) (C : Matrix (Fin n) (Fin n) (Word p hp)) (I : Fin k → Fin n) : List Step :=
  cacheScanTrace (fun i => (bidiagonalRefineLabel hn k upper C i).trace) (List.ofFn I)

/-- The cached stream, in the exact word type expected by the first-empty-bin scan. -/
noncomputable def bidiagonalCachedLabels {p n k : ℕ} {hp : 2 ≤ p} (hn : 0 < n)
    (upper : Bool) (C : Matrix (Fin n) (Fin n) (Word p hp)) (I : Fin k → Fin n) :
    List (EmptyBinScan.Word (svdAuxiliaryPrecision k p + 15) (svdBinLabelPrecision_ge_two k p)) :=
  (bidiagonalCachedRefinement hn upper C I).labels

/-- The sorted, nonnegative cache meets the paper's absolute error at each original
requested rank. Its trace includes the actual refinements and running comparisons. -/
theorem bidiagonalCachedLabels_spec {p n k : ℕ} {hp : 2 ≤ p} (hn : 0 < n)
    (upper : Bool) (C : Matrix (Fin n) (Fin n) (Word p hp)) (I : Fin k → Fin n)
    (hI : StrictMono I) (hs : bidiagonalSupport upper (fun i j => (C i j).value))
    (hC : ∀ i j, |(C i j).value| ≤ 1 / 4) :
    let labels := bidiagonalCachedLabels hn upper C I
    ∃ hlength : labels.length = k,
    (∀ a ∈ labels, 0 ≤ a.val) ∧
    labels.Pairwise (fun a b => a.val ≤ b.val) ∧
    (∀ i : Fin labels.length, |(labels.get i).val - ascendingRealSpectrum
      (fun j l => (C j l).value) (I (Fin.cast hlength i))| ≤
        unitRoundoff (svdAuxiliaryPrecision k p) / 64) ∧
    work (bidiagonalCachedRefinementTrace hn upper C I) ≤
      k * (68 * (n + n) * (svdAuxiliaryPrecision k p + 7) + 5) ∧
    TraceAllowed (svdLabelPrecision k p) (bidiagonalCachedRefinementTrace hn upper C I) := by
  dsimp only
  let ε := unitRoundoff (svdAuxiliaryPrecision k p) / 64
  let truth := ascendingRealSpectrum (fun i j => (C i j).value)
  let refine := fun i => (bidiagonalRefineLabel hn k upper C i).label
  let rs := List.ofFn I
  obtain ⟨_, _, hmono, hnonneg, _⟩ := exists_orthonormalBases_ascendingRealSpectrum
    (fun i j => (C i j).value)
  have hsorted : rs.Pairwise (fun i j => truth i ≤ truth j) := by
    rw [List.pairwise_ofFn]
    intro i j hij
    exact hmono (hI hij).le
  have hε : 0 ≤ ε := (div_pos (unitRoundoff_pos _) (by norm_num)).le
  have happrox (i : Fin n) := (bidiagonalRefineLabel_spec hn k upper C hs hC i).1
  obtain ⟨hlo, hsrt, ha⟩ := cacheScan_spec refine truth ε hε rs hsorted (fun i _ => hnonneg i)
    (fun i _ => happrox i) .zero (fun i _ => add_nonneg (hnonneg i) hε)
  have heq : bidiagonalCachedLabels hn upper C I = cacheScan refine .zero rs :=
    bidiagonalCachedRefinement_labels_eq_recorded hn upper C I
  have hlen : (bidiagonalCachedLabels hn upper C I).length = k :=
    (congrArg List.length heq).trans (ha.length_eq.trans List.length_ofFn)
  have htrace := cacheScan_trace (fun i => (bidiagonalRefineLabel hn k upper C i).trace) rs _
    (fun i _ => (bidiagonalRefineLabel_spec hn k upper C hs hC i).2.1)
    (fun i _ => (bidiagonalRefineLabel_spec hn k upper C hs hC i).2.2.1)
  refine ⟨hlen, heq ▸ hlo, heq ▸ hsrt, ?_, ?_, htrace.2⟩
  · intro i
    have hik : i.val < k := (Fin.cast hlen i).isLt
    have hli : i.val < (cacheScan refine .zero rs).length := by simpa only [← heq] using i.isLt
    have hi := ha.get hli (by simpa only [rs, List.length_ofFn] using hik)
    simpa [← heq, rs, truth] using hi
  · simpa only [rs, List.length_ofFn] using htrace.1

/-- Running the existing endpoint scan on the actual computed labels yields the first
empty bin. The scan and the later singular-label consumers share exactly this stream. -/
theorem bidiagonalCachedCut_spec {p n k : ℕ} {hp : 2 ≤ p} (hn : 2 ≤ n) (hk : 1 ≤ k)
    (hkn : k ≤ n) (hguard : precisionGuard n p)
    (upper : Bool) (C : Matrix (Fin n) (Fin n) (Word p hp)) (I : Fin k → Fin n)
    (hI : StrictMono I) (hs : bidiagonalSupport upper (fun i j => (C i j).value))
    (hC : ∀ i j, |(C i j).value| ≤ 1 / 4)
    (cmp : EmptyBinScan.Comparison (svdAuxiliaryPrecision k p + 15)
      (svdBinLabelPrecision_ge_two k p)) :
    let labels := bidiagonalCachedLabels (by omega : 0 < n) upper C I
    let execution := EmptyBinScan.SourceWork.runStored cmp (svdBinWidthWord k p) labels
    let cut := execution.result.state
    let s := fun i : Fin labels.length => (labels.get i).val
    let α := svdAlpha k p
    ∃ hlength : labels.length = k,
    (∀ i : Fin labels.length, |s i - ascendingRealSpectrum
      (fun j l => (C j l).value) (I (Fin.cast hlength i))| ≤
        unitRoundoff (svdAuxiliaryPrecision k p) / 64) ∧
    1 ≤ cut.j ∧ cut.j ≤ k + 1 ∧ EmptyCutBin α s cut.j ∧
    (∀ m : ℕ, 1 ≤ m → m < cut.j → ∃ i, InCutBin α m (s i)) ∧
    cut.lower.val = (cut.j : ℝ) * α ∧ cut.upper.val = ((cut.j + 1 : ℕ) : ℝ) * α ∧
    (∀ i : Fin labels.length,
      (s i < cut.lower.val ∧ s i ≤ 2 * unitRoundoff p) ∨
      (cut.upper.val ≤ s i ∧ 2 * α ≤ s i)) ∧
    execution.trace.length ≤ 71 * k := by
  dsimp only
  let labels := bidiagonalCachedLabels (by omega : 0 < n) upper C I
  obtain ⟨hlen, hnonneg, hsorted, herr, _, _⟩ :=
    bidiagonalCachedLabels_spec (by omega : 0 < n) upper C I hI hs hC
  obtain ⟨hα, _, _, _, _, hjlo, hjhi, he, hprior, hlo, hhi, hu, hside, hwork⟩ :=
    svd_empty_bin_cut n k p hp cmp labels hn hk hkn hlen hguard hnonneg hsorted
  rw [hα] at he hprior hlo hhi hu hside
  refine ⟨hlen, herr, hjlo, hjhi, he, hprior, hlo, hhi, ?_, hwork⟩
  intro i
  rcases hside i with hlow | hhigh
  · exact Or.inl ⟨hlow.1, hlow.2.trans hu⟩
  · exact Or.inr hhigh

end NumStability.CertifiedTridiagonalEigenpairs
