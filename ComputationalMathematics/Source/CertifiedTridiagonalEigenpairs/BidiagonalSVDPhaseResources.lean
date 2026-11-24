import ComputationalMathematics.Analysis.FloatingPointArithmetic.UnboundedBinary.VectorNormalizationWork
import ComputationalMathematics.Source.CertifiedTridiagonalEigenpairs.BidiagonalSVDOracleOutput
import ComputationalMathematics.Source.CertifiedTridiagonalEigenpairs.BidiagonalSVDResources

/-! Work and live scalar words of the deterministic bidiagonal phases. -/

namespace NumStability.CertifiedTridiagonalEigenpairs.BidiagonalSVDRequest

open FloatingPointFormat.UnboundedBinary ScalarWork

noncomputable section

variable {n k p : ℕ} {hp : 2 ≤ p}

/-- Scan the stored coefficients and charge the exact shifts and widening
of the unshifted and shifted packed bands. -/
private def preparationSetupTrace (d k p : ℕ) : List Step :=
  (List.replicate (2 * d - 1)
    [.index, .comparison, .comparison, .readExponent, .readExponent, .comparison,
      .comparison, .comparison, .index]).flatten ++
  [.readExponent, .comparison, .index, .index, .index, .index, .index, .index] ++
  (List.replicate (2 * d - 1)
    [.index, .index, .comparison, .index, .scaleByPowerOfTwo,
      .conversion p (svdLabelPrecision k p), .index,
      .index, .index, .comparison, .index, .scaleByPowerOfTwo,
      .conversion p (svdAuxiliaryPrecision k p), .index]).flatten ++
  (List.replicate (2 * d) [.index, .comparison, .index, .index]).flatten

private theorem mem_flatten_replicate {α : Type*} {a : α} {xs : List α} {m : ℕ}
    (h : a ∈ (List.replicate m xs).flatten) : a ∈ xs := by
  obtain ⟨_, hl, ha⟩ := List.mem_flatten.mp h
  obtain ⟨_, rfl⟩ := List.mem_replicate.mp hl
  exact ha

private theorem length_flatten_replicate {α : Type*} (xs : List α) (m : ℕ) :
    (List.replicate m xs).flatten.length = m * xs.length := by
  induction m with
  | zero => simp
  | succ m ih => simp [List.replicate_succ, ih, Nat.succ_mul, Nat.add_comm]

private theorem preparationSetupWork_le (d k p : ℕ) (hd : 1 ≤ d) :
    work (preparationSetupTrace d k p) ≤ 60 * d := by
  simp [preparationSetupTrace, work]
  omega

private def cutStep (q : ℕ) : EmptyBinScan.SourceWork.Primitive → Step
  | .compare => .comparison
  | .addOne | .scale => .arithmetic q
  | _ => .index

/-- Work of the band scan and assembly, refinements at the requested ranks and
running clipping/maxima, and the actual cached cut. Rank assembly is measured
separately. -/
def TridiagonalCall.preparationTrace (call : TridiagonalCall n k p) (upper : Bool)
    (a : Fin (n + 1) → Word p hp) (b : Fin n → Word p hp) (I : Fin k → Fin (n + 1)) :
    List Step :=
  let e := call.preprocessing.scaleExponent
  let C := storedBidiagonalWord upper (fun i => (a i).scale (-e)) (fun i => (b i).scale (-e))
  preparationSetupTrace (n + 1) k p ++ bidiagonalCachedRefinementTrace (by omega) upper C I ++
    call.preprocessing.cutExecution.trace.map (cutStep (svdLabelPrecision k p))

/-- Keep the input bands, widened refinement arrays, shifted bands, cached
labels, request indices and cut state. The sweep workspace is reused for each
rank. The stored empty-bin record is also charged. -/
def TridiagonalCall.preparationLiveWords (call : TridiagonalCall n k p) (upper : Bool)
    (a : Fin (n + 1) → Word p hp) (b : Fin n → Word p hp) (I : Fin k → Fin (n + 1)) :
    List ℕ :=
  let e := call.preprocessing.scaleExponent
  let C := storedBidiagonalWord upper (fun i => (a i).scale (-e)) (fun i => (b i).scale (-e))
  let resident := 8 * (n + 1) + 3 * k + 32 + call.preprocessing.cutExecution.trace.length
  resident :: (List.ofFn I).flatMap (fun i =>
    (bidiagonalRefineLabel (by omega) k upper C i).liveWords.map (resident + ·))

/-- The prepared call's charge uses the exact bands, rank list and output
of the executed cut. -/
theorem TridiagonalCall.preparation_resources (call : TridiagonalCall n k p) (upper : Bool)
    (a : Fin (n + 1) → Word p hp) (b : Fin n → Word p hp) (I : Fin k → Fin (n + 1))
    (cmp : EmptyBinScan.Comparison (svdLabelPrecision k p) (svdLabelPrecision_ge_two k p))
    (hn : 2 ≤ n + 1) (hk : 1 ≤ k) (hguard : precisionGuard (n + 1) p)
    (hI : StrictMono I)
    (hprep : prepareTridiagonalCall upper a b I cmp hn hk hguard hI = some call) :
    work (call.preparationTrace upper a b I) ≤ 1024 * ((n + 1) * k * p) ∧
      storage (call.preparationLiveWords upper a b I) ≤ 160 * ((n + 1) + (n + 1) * k) ∧
      TraceAllowed (svdWorkingPrecision (n + 1) k p) (call.preparationTrace upper a b I) := by
  have hkn : k ≤ n + 1 := by simpa using Fintype.card_le_of_injective I hI.injective
  simp only [prepareTridiagonalCall] at hprep
  obtain ⟨pre, hlen, hpre, rfl⟩ := Option.pmap_eq_some_iff.mp hprep
  have he' : ∃ e, normalizationExponent a b = some e := by
    cases hs : normalizationExponent a b with
    | none => simp [preprocessBidiagonal, hs] at hpre
    | some e => exact ⟨e, rfl⟩
  obtain ⟨e, he⟩ := he'
  obtain ⟨observed, hobserved, hexp, hspec⟩ :=
    preprocessBidiagonal_spec upper a b I cmp hn hk hkn hguard hI he
  have hsame : observed = pre := Option.some.inj (hobserved.symm.trans hpre)
  subst observed
  obtain ⟨_, _, _, _, _, _, _, _, _, hcut⟩ := hspec
  let C := storedBidiagonalWord upper (fun i => (a i).scale (-e)) (fun i => (b i).scale (-e))
  have hsupport : bidiagonalSupport upper (fun i j => (C i j).value) :=
    scaledBidiagonal_support upper a b e
  have hentry : ∀ i j, |(C i j).value| ≤ 1 / 4 :=
    (scaledBidiagonal_bounds upper a b he).1
  obtain ⟨_, _, _, _, href, hrefPrecision⟩ :=
    bidiagonalCachedLabels_spec (by omega : 0 < n + 1) upper C I hI hsupport hentry
  have htol := (svd_deterministic_work_factors_le (by omega : 0 < k) hkn hguard).1
  have htol' : k * (68 * ((n + 1) + (n + 1)) *
      (svdAuxiliaryPrecision k p + 7) + 5) =
      136 * ((n + 1) * k * (svdAuxiliaryPrecision k p + 7)) + 5 * k := by ring
  have hsetup := preparationSetupWork_le (n + 1) k p (by omega)
  have hnk : n + 1 ≤ (n + 1) * k := by
    simpa using Nat.mul_le_mul_left (n + 1) hk
  have hk' : k ≤ (n + 1) * k := by
    simpa using Nat.mul_le_mul_right k (Nat.le_add_left 1 n)
  have hkp : (n + 1) * k ≤ (n + 1) * k * p := by
    simpa using Nat.mul_le_mul_left ((n + 1) * k) (show 1 ≤ p by omega)
  have hcap := svd_stage_precisions_le (n + 1) k p
  have hlabelCap : svdLabelPrecision k p ≤ svdWorkingPrecision (n + 1) k p := hcap.1
  have haux := auxiliaryPrecision_ge_two k p
  have hlabel := svdLabelPrecision_ge_two k p
  simp only [TridiagonalCall.preparationTrace, TridiagonalCall.preparationLiveWords,
    assembleTridiagonalCall, hexp]
  change work (preparationSetupTrace (n + 1) k p ++
    bidiagonalCachedRefinementTrace (by omega) upper C I ++ _) ≤ _ ∧ _ ∧ _
  refine ⟨?_, ?_, ?_⟩
  · rw [htol'] at href
    simp only [work, List.length_append, List.length_map] at hsetup href ⊢
    omega
  · rw [storage_le_iff]
    intro words hwords
    simp only [List.mem_cons, List.mem_flatMap, List.mem_map] at hwords
    rcases hwords with rfl | ⟨i, _, live, hlive, rfl⟩
    · omega
    · have hbound := (bidiagonalRefineLabel_spec
        (by omega : 0 < n + 1) k upper C hsupport hentry i).2.2.2
      have hliveBound := (storage_le_iff.mp hbound) live hlive
      omega
  · intro step hstep
    simp only [List.mem_append, List.mem_map] at hstep
    rcases hstep with (hsetupStep | hrefStep) | ⟨op, _, rfl⟩
    · simp only [preparationSetupTrace, List.mem_append] at hsetupStep
      rcases hsetupStep with ((hscan | hscale) | hbands) | hdiag
      · have hs := mem_flatten_replicate hscan
        cases step <;> simp [Step.Allowed] at hs ⊢
      · simp at hscale
        rcases hscale with rfl | rfl | rfl
        all_goals trivial
      · have hs := mem_flatten_replicate hbands
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
        rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        all_goals first | trivial | exact ⟨hp, hcap.2.2, hlabel, hlabelCap⟩ |
          exact ⟨hp, hcap.2.2, haux, hcap.2.1⟩
      · have hs := mem_flatten_replicate hdiag
        cases step <;> simp [Step.Allowed] at hs ⊢
    · have h := hrefPrecision step hrefStep
      cases step <;> simp only [Step.Allowed] at h ⊢
      all_goals first | trivial | omega
    · cases op <;> simp [cutStep, Step.Allowed, hlabel, hlabelCap]

/-- Materialize one parity column using the prepared slot and row indices. -/
private def copyParityTrace (d : ℕ) : List Step :=
  [.index, .index] ++ (List.replicate d [.index, .index, .index]).flatten

/-- Traverse the stored list to the selected offset, then output its rounded
and rescaled label. -/
private def emitLabelTrace (p : ℕ) (j : Fin k) : List Step :=
  List.replicate (2 * j.val) .index ++
    [.index, .arithmetic p, .scaleByPowerOfTwo, .index]

/-- Parity extraction, both families of normalized vectors, and final labels. -/
def finishTrace (d k p : ℕ) : List Step :=
  (List.replicate (2 * k) (copyParityTrace d)).flatten ++
  (List.replicate (2 * k) (Word.normalizeToTrace d (svdAuxiliaryPrecision k p) p)).flatten ++
  (List.finRange k).flatMap (emitLabelTrace p)

/-- Both raw and both final arrays, with scratch reused across columns. -/
def finishLiveWords (d k : ℕ) : List ℕ :=
  let resident := 4 * (d * k) + k
  (resident + 2) :: (Word.normalizeToLiveWords d).map (resident + ·)

theorem finish_resources (d k p : ℕ) (hd : 1 ≤ d) (hk : 1 ≤ k) (hkd : k ≤ d)
    (hp : 2 ≤ p) :
    work (finishTrace d k p) ≤ 40 * (d * k) ∧
      storage (finishLiveWords d k) ≤ 14 * (d + d * k) ∧
      TraceAllowed (svdWorkingPrecision d k p) (finishTrace d k p) := by
  have hcap := svd_stage_precisions_le d k p
  have hkd' : k ≤ d * k := by simpa using Nat.mul_le_mul_right k hd
  have hnorm := Word.normalizeToTrace_work d (svdAuxiliaryPrecision k p) p hd
  have hcopy : work (copyParityTrace d) = 3 * d + 2 := by simp [copyParityTrace, work]; omega
  have hlabels : work ((List.finRange k).flatMap (emitLabelTrace p)) ≤ k * (2 * d + 4) := by
    have bound (xs : List (Fin k)) :
        work (xs.flatMap (emitLabelTrace p)) ≤ xs.length * (2 * d + 4) := by
      induction xs with
      | nil => simp [work]
      | cons i xs ih =>
        have hi := i.isLt
        simp only [List.flatMap_cons, work, List.length_append, List.length_cons,
          Nat.succ_mul, emitLabelTrace, List.length_replicate, List.length_nil] at ih ⊢
        omega
    simpa using bound (List.finRange k)
  refine ⟨?_, ?_, ?_⟩
  · simp only [finishTrace, work, List.length_append, length_flatten_replicate] at ⊢
    simp only [work] at hcopy hnorm hlabels
    rw [hcopy, hnorm]
    calc
      _ ≤ 2 * k * (3 * d + 2) + 2 * k * (11 * d) + k * (2 * d + 4) := by omega
      _ ≤ _ := by nlinarith
  · rw [storage_le_iff]
    intro words hw
    simp only [finishLiveWords, List.mem_cons, List.mem_map] at hw
    rcases hw with rfl | ⟨live, hlive, rfl⟩
    · omega
    · have h := storage_le_iff.mp (Word.normalizeToLiveWords_storage d) live hlive
      omega
  · intro step hs
    simp only [finishTrace, List.mem_append, List.mem_flatMap] at hs
    rcases hs with ((hcopyStep | hnormStep) | ⟨j, _, hs⟩)
    · have hs := mem_flatten_replicate hcopyStep
      simp only [copyParityTrace, List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
        or_self] at hs
      rcases hs with rfl | hs
      · trivial
      · have hs' := mem_flatten_replicate hs
        simp only [List.mem_cons, List.not_mem_nil, or_false, or_self] at hs'
        cases hs'
        trivial
    · exact Word.normalizeToTrace_allowed d (svdAuxiliaryPrecision k p) p _
        (auxiliaryPrecision_ge_two k p) hp hcap.2.1 hcap.2.2 step
        (mem_flatten_replicate hnormStep)
    · simp only [emitLabelTrace, List.mem_append, List.mem_replicate, List.mem_cons,
        List.mem_nil_iff, or_false] at hs
      rcases hs with ⟨_, rfl⟩ | rfl | rfl | rfl | rfl
      all_goals simp [Step.Allowed, hp, hcap.2.2]

end

end NumStability.CertifiedTridiagonalEigenpairs.BidiagonalSVDRequest
