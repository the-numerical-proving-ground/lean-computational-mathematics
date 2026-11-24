import ComputationalMathematics.Source.CertifiedTridiagonalEigenpairs.FiniteTrial.Target
import ComputationalMathematics.Source.CertifiedTridiagonalEigenpairs.FiniteTrial.RefinementTrace
import ComputationalMathematics.Source.CertifiedTridiagonalEigenpairs.IndexedRefinement.Proof
import ComputationalMathematics.Source.CertifiedTridiagonalEigenpairs.RequestedAdjacentGaps.Proof

/-! Bounds for the precise rounded test on one sampled tridiagonal matrix. -/

namespace NumStability.CertifiedTridiagonalEigenpairs

open FloatingPointFormat.UnboundedBinary NoisyRankCertificate ScalarWork
noncomputable section

variable {n p : ℕ} {J : Finset ℕ}
  (a : Fin (n + 1) → TrialWord n J p) (b : Fin n → TrialWord n J p)
  (words : Fin (n + 1) → FairBitWord (rngBits (n + 1) J.card))

set_option quotPrecheck false

local notation "q₀" => workingPrecision (n + 1) J.card p
local notation "g₀" => gapScale (n + 1) J.card p
local notation "α" => gapLabelError (n + 1) J.card p
local notation "ωq" => workingRoundoff (n + 1) J.card p
local notation "A₀" => (fun i => (a i).value)
local notation "B₀" => (fun i => (b i).value)
local notation "D" => (fun i => (trialDiagonal a words i).value)
local notation "λM" => ascendingEigenvalue (sturmTridiagonal_isHermitian D B₀)

theorem trialThreshold_value :
    (trialThreshold n J p).value = 3 * gapScale (n + 1) J.card p / 4 := by
  rw [trialThreshold, Word.value_scale, Word.value_round]
  let m := p + 3 * Nat.clog 2 (n + 1) + Nat.clog 2 J.card + 18
  have h3 : Native q₀ (workingPrecision_ge_two (n + 1) J.card p) (3 : ℝ) := by
    exact_mod_cast native_natCast_of_lt_two_pow q₀ (workingPrecision_ge_two (n + 1) J.card p)
      (m := 3) (show 3 < 2 ^ q₀ from
        calc
          3 < 2 ^ 2 := by decide
          _ ≤ 2 ^ q₀ := Nat.pow_le_pow_right (by decide) (workingPrecision_ge_two (n + 1) J.card p))
  have hs : 3 * gapScale (n + 1) J.card p / 4 = 3 * (2 : ℝ) ^ (-(m : ℤ) - 2) := by
    rw [gapScale_eq_roundoff, zpow_sub₀ (by norm_num : (2 : ℝ) ≠ 0)]
    change 3 * (2 : ℝ) ^ (-(m : ℤ)) / 4 =
      3 * ((2 : ℝ) ^ (-(m : ℤ)) / (2 : ℝ) ^ (2 : ℤ))
    norm_num
    ring
  rw [roundToEven_eq_self_of_native h3, hs]
  exact mul_comm _ _

/-- The matrix certified by the gate reads the exact diagonal returned by the run. -/
theorem trialRun_matrix_eq :
    sturmTridiagonal (fun i => ((trialRun n p J a b words).diagonal[i.val]).value) B₀ =
      trialMatrix a b words := rfl

theorem trialMatrix_eq_sampledMatrix :
    trialMatrix a b words = sampledMatrix (n + 1) J.card p (sturmTridiagonal A₀ B₀) words := by
  ext i j
  by_cases h : i = j
  · subst j
    rw [trialMatrix, sturmTridiagonal_diagonal, trialDiagonal, trialDiagonalWords,
      Vector.getElem_ofFn, Word.value_round]
    simp [sampledMatrix, sturmTridiagonal_diagonal]
  · rw [sampledMatrix_offDiag _ _ _ _ _ h]
    simp [trialMatrix, sturmTridiagonal, h]

include b in
private theorem trialDiagonal_roundoff (hn : 2 ≤ n + 1) (guard : precisionGuard (n + 1) p)
    (ha : ∀ i, |(a i).value| ≤ 1 / 4) (i : Fin (n + 1)) :
    |D i - ((a i).value + cellCenter (perturbationScale p) (rngBits (n + 1) J.card)
      (trialDraws (n + 1) J.card words i))| ≤ 2 * ωq := by
  have heq := congrArg (fun (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) => M i i)
    (trialMatrix_eq_sampledMatrix a b words)
  change trialMatrix a b words i i = _ at heq
  rw [trialMatrix, sturmTridiagonal_diagonal] at heq
  dsimp only at heq ⊢
  rw [heq]
  simpa only [sturmTridiagonal_diagonal] using
    sampledMatrix_diag_roundoff hn guard (sturmTridiagonal A₀ B₀) words i
      (by simpa only [sturmTridiagonal_diagonal] using ha i)

private theorem tridiagonalNorm_sub_le {d d' : Fin (n + 1) → ℝ}
    {s : Fin n → ℝ} {C : ℝ} (hC : 0 ≤ C) (h : ∀ i, |d i - d' i| ≤ C) :
    realMatrixOperatorNorm (sturmTridiagonal d s - sturmTridiagonal d' s) ≤ C := by
  rw [← sturmTridiagonal_sub]
  simpa using sturmTridiagonal_operatorNorm_le (d - d') (s - s) hC (show 0 ≤ (0 : ℝ) by norm_num)
    h (by simp)

include b in
private theorem trialDiagonal_sub_le (hn : 2 ≤ n + 1) (guard : precisionGuard (n + 1) p)
    (ha : ∀ i, |(a i).value| ≤ 1 / 4) (i : Fin (n + 1)) :
    |D i - (a i).value| ≤ perturbationScale p + 2 * ωq := by
  let ν := cellCenter (perturbationScale p) (rngBits (n + 1) J.card)
    (trialDraws (n + 1) J.card words i)
  have hν := abs_cellCenter_lt (show 0 < perturbationScale p by
    rw [perturbationScale_eq_roundoff]; exact unitRoundoff_pos _) (trialDraws (n + 1) J.card words i)
  change |ν| < perturbationScale p at hν
  rw [show D i - (a i).value = (D i - ((a i).value + ν)) + ν by ring]
  exact (abs_add_le _ _).trans (by linarith [trialDiagonal_roundoff a b words hn guard ha i])

private theorem trialMatrix_norm_lt (hn : 2 ≤ n + 1) (guard : precisionGuard (n + 1) p)
    (ha : ∀ i, |(a i).value| ≤ 1 / 4) (hb : ∀ i, |(b i).value| ≤ 1 / 4) :
    realMatrixOperatorNorm (trialMatrix a b words) < 1 := by
  have hp := clog_add_le_of_precisionGuard (by omega : 0 < n + 1) guard
  have hu := unitRoundoff_le_quarter p (by omega)
  have hprec := (trialPrecisionBudget (k := J.card) hn guard).2.2.2.1
  have hd (i) : |D i| ≤ 1 / 4 + unitRoundoff p / 128 := by
    rw [show D i = (D i - (a i).value) + (a i).value by ring]
    exact (abs_add_le _ _).trans (by linarith [trialDiagonal_sub_le a b words hn guard ha i, ha i])
  unfold trialMatrix
  apply (sturmTridiagonal_operatorNorm_le _ _ (by linarith [unitRoundoff_pos p]) (by norm_num) hd hb).trans_lt
  linarith

private theorem trialRefinement_label_error (hn : 2 ≤ n + 1) (guard : precisionGuard (n + 1) p)
    (ha : ∀ i, |(a i).value| ≤ 1 / 4) (hb : ∀ i, |(b i).value| ≤ 1 / 4)
    (i : Fin (n + 1)) :
    |(trialRefinement a b words i).label.value - λM i| ≤ α := by
  have hr : 2 ≤ gapToleranceExponent (n + 1) J.card p := by
    unfold gapToleranceExponent
    omega
  have hnorm := trialMatrix_norm_lt a b words hn guard ha hb
  have ⟨_, hlabel, hstrict, _⟩ := indexedRefinement n _ q₀ _ i (trialDiagonal a words) b hr
    (trialPrecisionBudget (k := J.card) hn guard).2.2.2.2
    (hnorm.le.trans (by norm_num)) (fun j => (hb j).trans (by norm_num))
  rw [← gapTolerance_twice, gapTolerance_eq_roundoff]
  exact hlabel.trans hstrict.le

private theorem markTrialRank_read {N : ℕ} (flags : Vector Bool N) (r : ℕ) (i : Fin N) :
    (markTrialRank flags r)[i.val] = (decide (r = i.val + 1) || flags[i.val]) := by
  have hi := i.isLt
  by_cases h : 1 ≤ r ∧ r ≤ N
  · rw [markTrialRank, dif_pos h, Vector.getElem_set]
    have he : r - 1 = i.val ↔ r = i.val + 1 := by omega
    by_cases heq : r = i.val + 1
    · simp [heq]
    · simp [heq, mt he.mp heq]
  · have hne : r ≠ i.val + 1 := by omega
    simp [markTrialRank, h, hne]

private theorem fold_markTrialRank_read {N : ℕ} (ranks : List ℕ) (flags : Vector Bool N)
    (i : Fin N) :
    (ranks.foldl markTrialRank flags)[i.val] = true ↔ i.val + 1 ∈ ranks ∨ flags[i.val] = true := by
  induction ranks generalizing flags with
  | nil => simp
  | cons r rest ih =>
    simp only [List.foldl_cons, ih, markTrialRank_read, Bool.or_eq_true, decide_eq_true_eq,
      List.mem_cons]
    constructor
    · rintro (h | h | h)
      · exact Or.inl (Or.inr h)
      · exact Or.inl (Or.inl h.symm)
      · exact Or.inr h
    · rintro ((h | h) | h)
      · exact Or.inr (Or.inl h.symm)
      · exact Or.inl h
      · exact Or.inr (Or.inr h)

private theorem trialRequestedFlag_read {N : ℕ} (J : Finset ℕ) (i : Fin N) :
    (trialRequestedFlags N J)[i.val] = true ↔ i.val + 1 ∈ J := by
  simp [trialRequestedFlags, fold_markTrialRank_read]

private theorem trialNeighborFlag_read {N : ℕ} (J : Finset ℕ) (i : Fin N) :
    (trialNeighborFlags N J)[i.val] = true ↔ i.val + 1 ∈ requestedNeighborRanks N J := by
  have hi : i.val + 1 ∈ Finset.Icc 1 N := Finset.mem_Icc.mpr ⟨by omega, Nat.succ_le_of_lt i.isLt⟩
  simp only [trialNeighborFlags, fold_markTrialRank_read, Vector.getElem_replicate,
    Bool.false_eq_true, or_false, requestedNeighborRanks, Finset.mem_inter, hi, and_true,
    Finset.mem_union, Finset.mem_image, List.mem_flatMap, Finset.mem_toList, List.mem_cons,
    List.not_mem_nil, or_false]
  constructor
  · rintro ⟨j, hj, h | h | h⟩
    · exact Or.inl (Or.inl (h ▸ hj))
    · exact Or.inl (Or.inr ⟨j, hj, h.symm⟩)
    · exact Or.inr ⟨j, hj, h.symm⟩
  · rintro ((h | ⟨j, hj, h⟩) | ⟨j, hj, h⟩)
    · exact ⟨i.val + 1, h, Or.inl rfl⟩
    · exact ⟨j, hj, Or.inr (Or.inl h.symm)⟩
    · exact ⟨j, hj, Or.inr (Or.inr h.symm)⟩

theorem mem_trialRanks (i : Fin (n + 1)) : i ∈ trialRanks n J ↔
    i.val + 1 ∈ requestedNeighborRanks (n + 1) J := by
  simp [trialRanks, List.mem_finRange, trialNeighborFlag_read]

theorem mem_trialEdges (e : Fin n) : e ∈ trialEdges n J ↔
    e.val + 1 ∈ requestedAdjacentGapIndices (n + 1) J := by
  have he : e.val + 1 ∈ Finset.Icc 1 (n + 1 - 1) :=
    Finset.mem_Icc.mpr ⟨by omega, by have := e.isLt; omega⟩
  simp only [trialEdges, List.mem_filter, List.mem_finRange, true_and, Bool.or_eq_true,
    requestedAdjacentGapIndices, Finset.mem_filter, he]
  rw [trialRequestedFlag_read J e.castSucc, trialRequestedFlag_read J e.succ]
  rfl

private theorem neighborRank_mem {i j : ℕ} (hi : 1 ≤ i) (hi' : i ≤ n + 1)
    (hj : j ∈ J) (h : i = j ∨ i = j - 1 ∨ i = j + 1) :
    i ∈ requestedNeighborRanks (n + 1) J := by
  apply Finset.mem_inter.mpr ⟨?_, Finset.mem_Icc.mpr ⟨hi, hi'⟩⟩
  rcases h with rfl | rfl | rfl
  · exact Finset.mem_union_left _ (Finset.mem_union_left _ hj)
  · exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_image_of_mem _ hj))
  · exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ hj)

/-- Every tested difference reads two ranks in the refinement pass. -/
theorem trialEdges_endpoints_mem (e : Fin n) (he : e ∈ trialEdges n J) :
    e.castSucc ∈ trialRanks n J ∧ e.succ ∈ trialRanks n J := by
  have h := (mem_trialEdges e).mp he
  simp only [requestedAdjacentGapIndices, Finset.mem_filter] at h
  rw [mem_trialRanks, mem_trialRanks]
  simp only [Fin.val_castSucc, Fin.val_succ]
  have hh := e.isLt
  rcases h.2 with h | h
  · exact ⟨neighborRank_mem (by omega) (by omega) h (Or.inl rfl),
      neighborRank_mem (by omega) (by omega) h (Or.inr (Or.inr (by omega)))⟩
  · exact ⟨neighborRank_mem (by omega) (by omega) h (Or.inr (Or.inl (by omega))),
      neighborRank_mem (by omega) (by omega) h (Or.inl rfl)⟩

private theorem trialCachedLabels_read (i : Fin (n + 1)) (hi : i ∈ trialRanks n J) :
    (trialCachedLabels (trialDiagonalWords a words) b)[i.val] = (trialRefinement a b words i).label := by
  have hflag := (trialNeighborFlag_read J i).mpr ((mem_trialRanks i).mp hi)
  unfold trialCachedLabels
  rw [Vector.getElem_ofFn]
  change (if (trialNeighborFlags (n + 1) J)[i.val] then _ else _) = _
  rw [if_pos hflag]
  exact runTridiagonalRefinement_eq _ _ _ _

/-- The measured refinement of a visited rank returns the cache word and
bounds the space of that active call, including its matrix inputs. -/
theorem trialCachedLabels_rank_resources (i : Fin (n + 1)) (hi : i ∈ trialRanks n J) :
    let observed := measuredTridiagonalRefinement (gapToleranceExponent (n + 1) J.card p)
      i (trialDiagonal a words) b
    observed.1 = (trialCachedLabels (trialDiagonalWords a words) b)[i.val] ∧
      observed.2.peakWords ≤ 26 * (n + 1) := by
  have h := runTridiagonalRefinement_resources (gapToleranceExponent (n + 1) J.card p)
    i (trialDiagonal a words) b
  exact ⟨h.1.trans (trialCachedLabels_read a b words i hi).symm, h.2.2⟩

/-- Live-word bounds by phase of the cache pass. The fixed overhead covers
the original input diagonal retained for a future trial, the neighbor
flags, the label array and six control slots. Active refinement measurements
also include the sampled diagonal and original subdiagonal. -/
noncomputable def trialCacheLiveWords : List ℕ :=
  let resident := 3 * (n + 1) + 6
  resident :: (trialRanks n J).map fun i =>
    resident + (measuredTridiagonalRefinement (gapToleranceExponent (n + 1) J.card p)
      i (trialDiagonal a words) b).2.peakWords

/-- The cache pass completes each active refinement before the following
rank, so its working-space bound is linear in the dimension. -/
theorem trialCachedLabels_storage :
    storage (trialCacheLiveWords a b words) ≤ 35 * (n + 1) := by
  rw [storage_le_iff]
  intro slots hslots
  rcases List.mem_cons.mp hslots with h | h
  · rw [h]
    omega
  · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp h
    have hpeak := (trialCachedLabels_rank_resources a b words i hi).2
    omega

private theorem trialAccepts_iff :
    trialAccepts n p J a b words = true ↔
      ∀ e ∈ trialEdges n J, 3 * g₀ / 4 ≤ (trialDifference a b words e).value := by
  simp only [trialAccepts, trialRun, List.all_map, Function.comp_def, id_eq,
    List.all_eq_true, decide_eq_true_eq, trialThreshold_value]
  apply forall_congr'
  intro e
  apply imp_congr_right
  intro he
  have ⟨hle, hre⟩ := trialEdges_endpoints_mem e he
  rw [trialCachedLabels_read a b words e.succ hre, trialCachedLabels_read a b words e.castSucc hle]
  rfl

private theorem roundedGap_bounds (hn : 2 ≤ n + 1) (guard : precisionGuard (n + 1) p)
    (ha : ∀ i, |(a i).value| ≤ 1 / 4) (hb : ∀ i, |(b i).value| ≤ 1 / 4) (e : Fin n) :
    let d := (trialDifference a b words e).value
    let gap := λM e.succ - λM e.castSucc
    (3 * g₀ / 4 ≤ d → certifiedGap (n + 1) J.card p < gap) ∧
      (15 * g₀ / 16 < gap → 3 * g₀ / 4 < d) := by
  dsimp only
  let x := (trialRefinement a b words e.succ).label.value -
    (trialRefinement a b words e.castSucc).label.value
  let gap := λM e.succ - λM e.castSucc
  let d := (trialDifference a b words e).value
  change (3 * g₀ / 4 ≤ d → certifiedGap (n + 1) J.card p < gap) ∧
    (15 * g₀ / 16 < gap → 3 * g₀ / 4 < d)
  have hω := (trialPrecisionBudget (k := J.card) hn guard).2.1
  have hg : 0 < g₀ := by rw [gapScale_eq_roundoff]; exact unitRoundoff_pos _
  have h₀ := abs_le.mp (trialRefinement_label_error a b words hn guard ha hb e.castSucc)
  have h₁ := abs_le.mp (trialRefinement_label_error a b words hn guard ha hb e.succ)
  have hxlo : gap - g₀ / 32 ≤ x := by
    unfold gap x
    unfold gapLabelError at h₀ h₁
    linarith
  have hxhi : x ≤ gap + g₀ / 32 := by
    unfold gap x
    unfold gapLabelError at h₀ h₁
    linarith
  obtain ⟨ρ, hρ, hmul⟩ := roundToEven_signedRelErrorWitness q₀
    (workingPrecision_ge_two (n + 1) J.card p) x
  have hd : d = x * (1 + ρ) := by
    unfold d trialDifference ScalarOperation.eval
    rw [Word.value_round]
    exact hmul
  have hρlo : 127 / 128 ≤ 1 + ρ := by
    linarith [(abs_le.mp hρ).1, show unitRoundoff q₀ ≤ 1 / 128 from hω]
  have hρhi : 1 + ρ ≤ 129 / 128 := by
    linarith [(abs_le.mp hρ).2, show unitRoundoff q₀ ≤ 1 / 128 from hω]
  constructor
  · intro hpass
    have hpos : 0 < x := by
      by_contra! hnon
      have h := mul_nonpos_of_nonpos_of_nonneg hnon (by linarith : 0 ≤ 1 + ρ)
      linarith
    have hup : d ≤ x * (129 / 128) := by rw [hd]; exact mul_le_mul_of_nonneg_left hρhi hpos.le
    unfold certifiedGap
    linarith
  · intro hgood
    have hpos : 0 ≤ x := by linarith
    have hlo : x * (127 / 128) ≤ d := by rw [hd]; exact mul_le_mul_of_nonneg_left hρlo hpos
    linarith

private theorem acceptedGap (hn : 2 ≤ n + 1) (guard : precisionGuard (n + 1) p)
    (ha : ∀ i, |(a i).value| ≤ 1 / 4) (hb : ∀ i, |(b i).value| ≤ 1 / 4)
    (hpass : trialAccepts n p J a b words = true) (j : Fin (n + 1)) (hj : j.val + 1 ∈ J)
    (i : Fin (n + 1)) (hij : i ≠ j) :
    certifiedGap (n + 1) J.card p < |λM i - λM j| := by
  have hmono := ascendingEigenvalue_monotone (sturmTridiagonal_isHermitian D B₀)
  have hgap (e : Fin n) (he : e.val + 1 ∈ J ∨ e.val + 1 + 1 ∈ J) :
      certifiedGap (n + 1) J.card p < λM e.succ - λM e.castSucc := by
    apply (roundedGap_bounds a b words hn guard ha hb e).1
    apply (trialAccepts_iff a b words).mp hpass
    apply (mem_trialEdges e).mpr
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, by omega⟩, he⟩
  rcases lt_or_gt_of_ne hij with hlt | hlt
  · have hval : i.val < j.val := hlt
    let e : Fin n := ⟨j.val - 1, by omega⟩
    have hs : e.succ = j := Fin.ext (by simp [e]; omega)
    have hc : i ≤ e.castSucc := by change i.val ≤ j.val - 1; omega
    have he : e.val + 1 + 1 = j.val + 1 := by change j.val - 1 + 1 + 1 = _; omega
    have hl := hgap e (Or.inr (he ▸ hj))
    rw [hs] at hl
    rw [abs_of_nonpos (sub_nonpos.mpr (hmono hlt.le))]
    linarith [hmono hc]
  · have hval : j.val < i.val := hlt
    let e : Fin n := ⟨j.val, by omega⟩
    have hc : e.castSucc = j := Fin.ext rfl
    have hs : e.succ ≤ i := hval
    have hl := hgap e (Or.inl hj)
    rw [hc] at hl
    rw [abs_of_nonneg (sub_nonneg.mpr (hmono hlt.le))]
    linarith [hmono hs]

theorem finiteTrialCoupledAcceptance : SourceTargets.finiteTrialCoupledAcceptance := by
  intro n p J a b hn guard ha hb words V A spectrumAV g hcell hgood
  have ⟨hω, _, _, _, _⟩ := trialPrecisionBudget (k := J.card) hn guard
  have hdist : realMatrixOperatorNorm
      (trialMatrix a b words - sturmTridiagonal A (fun i => (b i).value)) ≤ g / 32 := by
    apply tridiagonalNorm_sub_le
    · change 0 ≤ gapScale (n + 1) J.card p / 32
      rw [gapScale_eq_roundoff]
      exact div_nonneg (unitRoundoff_pos _).le (by norm_num)
    · intro i
      let ν := cellCenter (perturbationScale p) (rngBits (n + 1) J.card)
        (trialDraws (n + 1) J.card words i)
      change |(trialDiagonal a words i).value - ((a i).value + V i)| ≤ g / 32
      rw [show (fun i => (trialDiagonal a words i).value) i - ((a i).value + V i) = ((trialDiagonal a words i).value - ((a i).value + ν)) + -(V i - ν) by ring]
      apply (abs_add_le _ _).trans
      rw [abs_neg]
      unfold gapLabelError at hω
      linarith [trialDiagonal_roundoff a b words hn guard ha i, hcell i]
  let hM := sturmTridiagonal_isHermitian (fun i => (trialDiagonal a words i).value)
    (fun i => (b i).value)
  let hA := sturmTridiagonal_isHermitian A (fun i => (b i).value)
  have hweyl (i : Fin (n + 1)) : |ascendingEigenvalue hM i - spectrumAV i| ≤ g / 32 :=
    (HDP.Matrix.abs_hermitianOrderedEigenvalue_sub_le_operatorNorm _ _ hM hA i.rev).trans hdist
  apply (trialAccepts_iff a b words).mpr
  intro e he
  apply ((roundedGap_bounds a b words hn guard ha hb e).2 ?_).le
  have h := hgood e ((mem_trialEdges e).mp he)
  linarith [(abs_le.mp (hweyl e.castSucc)).2, (abs_le.mp (hweyl e.succ)).1]

private theorem requestedNeighborRanks_card_le (N : ℕ) (J : Finset ℕ) :
    (requestedNeighborRanks N J).card ≤ 3 * J.card := by
  unfold requestedNeighborRanks
  have hsub := Finset.card_le_card (Finset.inter_subset_left
    (s₁ := J ∪ J.image (· - 1) ∪ J.image (· + 1)) (s₂ := Finset.Icc 1 N))
  have hu := Finset.card_union_le (J ∪ J.image (· - 1)) (J.image (· + 1))
  have hv := Finset.card_union_le J (J.image (· - 1))
  have hleft : (J.image (· - 1)).card ≤ J.card := Finset.card_image_le
  have hright : (J.image (· + 1)).card ≤ J.card := Finset.card_image_le
  omega

private theorem trialRanks_length (n : ℕ) (J : Finset ℕ) :
    (trialRanks n J).length ≤ 3 * J.card := by
  have hnodup : (trialRanks n J).Nodup := (List.nodup_finRange _).filter _
  rw [← List.toFinset_card_of_nodup hnodup]
  apply Nat.le_trans _ (requestedNeighborRanks_card_le (n + 1) J)
  apply Finset.card_le_card_of_injOn (fun i : Fin (n + 1) => i.val + 1)
  · intro i hi
    exact (mem_trialRanks i).mp (List.mem_toFinset.mp hi)
  · intro i _ j _ h
    change i.val + 1 = j.val + 1 at h
    exact Fin.ext (by omega)

private theorem trialEdges_length (n : ℕ) (J : Finset ℕ) :
    (trialEdges n J).length ≤ 2 * J.card := by
  have hnodup : (trialEdges n J).Nodup := (List.nodup_finRange _).filter _
  rw [← List.toFinset_card_of_nodup hnodup]
  apply Nat.le_trans _ (requestedAdjacentGapIndices_card_le (n + 1) J)
  apply Finset.card_le_card_of_injOn (fun i : Fin n => i.val + 1)
  · intro i hi
    exact (mem_trialEdges i).mp (List.mem_toFinset.mp hi)
  · intro i _ j _ h
    change i.val + 1 = j.val + 1 at h
    exact Fin.ext (by omega)

private theorem work_flatMap_le {β : Type*} {indices : List β} {pieces : β → List Step}
    {bound : ℕ} (h : ∀ i ∈ indices, work (pieces i) ≤ bound) :
    work (indices.flatMap pieces) ≤ indices.length * bound := by
  induction indices with
  | nil => simp [work]
  | cons i rest ih =>
    have head := h i (by simp)
    have tail := ih (by intro j hj; exact h j (by simp [hj]))
    simp only [List.flatMap_cons, List.length_cons, Nat.add_mul, Nat.one_mul]
    simp only [work, List.length_append] at *
    omega

private theorem noFairBits_count {trace : List Step} (h : Step.fairBit ∉ trace) :
    trace.countP isFairBit = 0 := by
  apply List.countP_eq_zero.mpr
  intro s hs
  cases s <;> simp [isFairBit] at *
  contradiction

private theorem trialTrace_fairBits :
    (trialTrace a b words).countP isFairBit = (n + 1) * rngBits (n + 1) J.card := by
  have hRef :
      ((trialRanks n J).flatMap (fun i => (trialRefinement a b words i).trace)).countP
        isFairBit = 0 := by
    apply noFairBits_count
    rintro h
    obtain ⟨i, _, hi⟩ := List.mem_flatMap.mp h
    exact refinementTrace_noFairBit _ _ _ _ hi
  have hEdge :
      ((trialEdges n J).flatMap (fun _ => [.index, .index, .arithmetic q₀, .comparison])).countP
        isFairBit = 0 := by
    apply noFairBits_count
    simp
  simp only [trialTrace, List.countP_append, List.countP_replicate, samplerTrace_randBits,
    hRef, hEdge, isFairBit, Bool.false_eq_true, ↓reduceIte, zero_add, add_zero]
  simp [isFairBit]

private theorem trialTrace_allowed :
    TraceAllowed q₀ (trialTrace a b words) := by
  intro step hs
  simp only [trialTrace, List.mem_append, List.mem_flatMap, List.mem_singleton] at hs
  rcases hs with ((((h | h) | h) | h) | h)
  · cases List.eq_of_mem_replicate h
    trivial
  · exact samplerTrace_allowed _ _ _ step h
  · obtain ⟨i, _, hi⟩ := h
    exact (tridiagonalRefinement_resources _ i (trialDiagonal a words) b).2.1 step hi
  · cases h
    trivial
  · obtain ⟨i, _, hi⟩ := h
    simp [List.mem_cons] at hi
    rcases hi with rfl | rfl | rfl <;> simp [Step.Allowed, workingPrecision_ge_two]

private theorem trialTrace_work (hn : 2 ≤ n + 1) (guard : precisionGuard (n + 1) p)
    (hJ : J.Nonempty) (hsubset : J ⊆ Finset.Icc 1 (n + 1)) :
    work (trialTrace a b words) ≤ 2000 * (n + 1) * J.card * (p + Nat.clog 2 (n + 1)) := by
  let N := n + 1
  let L := Nat.clog 2 N
  let k := J.card
  let r := gapToleranceExponent N k p
  let s := p + L
  have hk : 1 ≤ k := Finset.card_pos.mpr hJ
  have hkn : k ≤ N := by
    have h := Finset.card_le_card hsubset
    simpa using h
  have hlog := Nat.clog_mono_right 2 hkn
  have hp : L + 7 ≤ p := clog_add_le_of_precisionGuard (by omega : 0 < N) guard
  have hs : 1 ≤ s := by dsimp [s]; omega
  have hr : 2 ≤ r := by unfold r gapToleranceExponent; omega
  have hr' : r ≤ 5 * s := by unfold r gapToleranceExponent s L at *; omega
  have hsample' := rngBits_le hkn
  have hsample : 4 * rngBits N k + 7 ≤ 30 * s := by unfold s L; omega
  have href (i : Fin N) : work (trialRefinement a b words i).trace ≤ 68 * N * r := by
    have hi := (tridiagonalRefinement_resources r i (trialDiagonal a words) b).1
    have hmul := Nat.mul_le_mul (show 13 * N + 8 ≤ 21 * N by omega)
      (show r + 4 ≤ 3 * r by omega)
    have hNr : 2 ≤ N * r := by
      exact hr.trans (by simpa using Nat.mul_le_mul_right r (show 1 ≤ N by omega))
    have hcalc : (21 * N) * (3 * r) = 63 * (N * r) := by ring
    have hcalc' : 68 * N * r = 68 * (N * r) := by ring
    rw [hcalc] at hmul
    rw [hcalc']
    change work (trialRefinement a b words i).trace ≤ (13 * N + 8) * (r + 4) + 10 at hi
    exact hi.trans (by omega)
  have hR : work ((trialRanks n J).flatMap (fun i => (trialRefinement a b words i).trace)) ≤
      1020 * (N * k * s) := calc
    _ ≤ (trialRanks n J).length * (68 * N * r) := work_flatMap_le (by
      intro i _; exact href i)
    _ ≤ (3 * k) * (68 * N * (5 * s)) :=
      Nat.mul_le_mul (trialRanks_length n J) (Nat.mul_le_mul_left _ hr')
    _ = 1020 * (N * k * s) := by ring
  have hE : work ((trialEdges n J).flatMap (fun _ => [.index, .index, .arithmetic q₀, .comparison])) ≤
      8 * k := calc
    _ ≤ (trialEdges n J).length * 4 := work_flatMap_le (by intro _ _; rfl)
    _ ≤ (2 * k) * 4 := Nat.mul_le_mul_right _ (trialEdges_length n J)
    _ = 8 * k := by ring
  have hS : N * (4 * rngBits N k + 7) ≤ 30 * (N * k * s) := calc
    _ ≤ N * (30 * s) := Nat.mul_le_mul_left _ hsample
    _ ≤ (N * k) * (30 * s) := Nat.mul_le_mul_right _
      (by simpa using Nat.mul_le_mul_left N hk)
    _ = _ := by ring
  have hN : N ≤ N * k * s := by
    exact (by simpa using Nat.mul_le_mul_left N hk : N ≤ N * k).trans
      (by simpa using Nat.mul_le_mul_left (N * k) hs)
  have hscale : 1 ≤ N * k * s := by omega
  calc
    work (trialTrace a b words) =
        12 * (N + k) + N * (4 * rngBits N k + 7) +
        work ((trialRanks n J).flatMap (fun i => (trialRefinement a b words i).trace)) + 1 +
        work ((trialEdges n J).flatMap (fun _ => [.index, .index, .arithmetic q₀, .comparison])) := by
      simp only [trialTrace, work, List.length_append, List.length_replicate, List.length_cons,
        List.length_nil]
      rw [show (samplerTrace N k p).length = _ from samplerTrace_work N k p]
    _ ≤ 2000 * (N * k * s) := by omega
    _ = 2000 * (n + 1) * J.card * (p + Nat.clog 2 (n + 1)) := by unfold N k s L; ring

theorem finiteTrialCertificate : SourceTargets.finiteTrialCertificate := by
  intro n p J a b hn guard hJ hsubset ha hb words S M μ g trace
  have hbudget := (trialPrecisionBudget (k := J.card) hn guard).2.2.2.1
  have hpert : 0 ≤ perturbationScale p + 2 * workingRoundoff (n + 1) J.card p := by
    rw [perturbationScale_eq_roundoff, workingRoundoff]
    linarith [unitRoundoff_pos (p + 8), unitRoundoff_pos (workingPrecision (n + 1) J.card p)]
  refine ⟨trialThreshold_value, tridiagonalNorm_sub_le hpert ?_, hbudget,
    trialMatrix_norm_lt a b words hn guard ha hb, ?_,
    acceptedGap a b words hn guard ha hb, trialTrace_fairBits a b words,
    trialTrace_work a b words hn guard hJ hsubset, trialTrace_allowed a b words⟩
  · exact trialDiagonal_sub_le a b words hn guard ha
  · intro i j hij
    exact (congrArg (fun (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) => A i j)
      (trialMatrix_eq_sampledMatrix a b words)).trans (sampledMatrix_offDiag _ _ _ _ _ hij)

end
end NumStability.CertifiedTridiagonalEigenpairs
