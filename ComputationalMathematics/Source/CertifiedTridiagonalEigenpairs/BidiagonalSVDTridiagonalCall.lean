import ComputationalMathematics.Source.CertifiedTridiagonalEigenpairs.BidiagonalSVDPreprocessing
import ComputationalMathematics.Source.CertifiedTridiagonalEigenpairs.BidiagonalSVDRequestPlan

/-!
# Stored input to the single shifted tridiagonal call

The call uses the nonzero-branch scale and the existing empty-bin result. Its
two packed bands are stored directly at the auxiliary precision.
-/

open Matrix NumStability.Matrix.Bipartite

namespace NumStability.CertifiedTridiagonalEigenpairs.BidiagonalSVDRequest
open FloatingPointFormat.UnboundedBinary

abbrev edgeCount (n : ℕ) : ℕ := (n + 1) + (n + 1) - 1

theorem auxiliaryPrecision_ge_two (k p : ℕ) : 2 ≤ svdAuxiliaryPrecision k p := by
  unfold svdAuxiliaryPrecision
  omega

abbrev AuxWord (k p : ℕ) := Word (svdAuxiliaryPrecision k p) (auxiliaryPrecision_ge_two k p)

/-- The sign and exponent of the exact dyadic mass. -/
def massWord (k p : ℕ) (negative : Bool) : AuxWord k p :=
  .normal negative _ (1 - ((p + Nat.clog 2 k : ℕ) : ℤ))
    (format _ _).minNormalMantissa_normalized

theorem value_massWord (k p : ℕ) (negative : Bool) :
    (massWord k p negative).value = if negative then -svdAlpha k p else svdAlpha k p := by
  have hpow : 1 - ((p + Nat.clog 2 k : ℕ) : ℤ) = -((p + Nat.clog 2 k : ℕ) : ℤ) + 1 := by
    omega
  cases negative
  · simp only [massWord, Word.value, hpow, Bool.false_eq_true, if_false]
    rw [FloatingPointFormat.normalizedValue_false_minNormalMantissa_eq, svdAlpha_eq_unitRoundoff]
    simp [FloatingPointFormat.betaR, format, unitRoundoff]
  · simp only [massWord, Word.value, hpow, if_true]
    rw [FloatingPointFormat.normalizedValue_true_eq_neg_false,
      FloatingPointFormat.normalizedValue_false_minNormalMantissa_eq, svdAlpha_eq_unitRoundoff]
    simp [FloatingPointFormat.betaR, format, unitRoundoff]

private theorem get_ofFn {m : ℕ} {β : Type*} (f : Fin m → β) (i : Fin m) :
    (Vector.ofFn f).get i = f i := Vector.getElem_ofFn i.isLt

/-- Left positions carry the positive mass and right positions the negative mass. -/
def shiftedDiagonal (n k p : ℕ) (upper : Bool) :
    Vector (AuxWord k p) (edgeCount n + 1) :=
  let coord := bidiagonalRefinementCoord (n := n + 1) (by omega)
  Vector.ofFn fun i =>
    Sum.elim (fun _ => massWord k p false) (fun _ => massWord k p true)
      (bidiagonalParityCoord upper (n + 1) (coord i))

variable {n k p : ℕ} {hp : 2 ≤ p}

/-- The signed edges are the original diagonal and off-diagonal words in the order
`a₀,b₀,a₁,b₁,…,aₙ`, scaled by the existing exponent and widened exactly. -/
def shiftedEdges (k : ℕ) (a : Fin (n + 1) → Word p hp) (b : Fin n → Word p hp) (e : ℤ) :
    Vector (AuxWord k p) (edgeCount n) :=
  Vector.ofFn fun i =>
    let x := if h : i.val % 2 = 0 then a ⟨i.val / 2, by have hi := i.isLt; change i.val < (n + 1) + (n + 1) - 1 at hi; omega⟩
      else b ⟨i.val / 2, by have hi := i.isLt; change i.val < (n + 1) + (n + 1) - 1 at hi; omega⟩
    (x.scale (-e)).widen (auxiliaryPrecision_ge_two k p) (by unfold svdAuxiliaryPrecision; omega)

private theorem bidiagonal_shift_formula (upper : Bool)
    (C : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (α : ℝ) :
    bidiagonalMassShift upper C α =
      zeroDiagonalTridiagonal (upperGolubKahanOffdiag (if upper then C else Cᵀ)) +
      Matrix.diagonal (Sum.elim (fun _ => α) (fun _ => -α) ∘ bidiagonalParityCoord upper (n + 1)) := by
  cases upper <;> rfl

private theorem value_shiftedEdges (k : ℕ) (upper : Bool) (a : Fin (n + 1) → Word p hp)
    (b : Fin n → Word p hp) (e : ℤ) (i : Fin (edgeCount n)) :
    ((shiftedEdges k a b e).get i).value = upperGolubKahanOffdiag
      (if upper then scaledBidiagonal upper a b e else (scaledBidiagonal upper a b e)ᵀ)
      (bidiagonalRefinementCoord (by omega) i.castSucc) := by
  let c := bidiagonalRefinementCoord (n := n + 1) (by omega)
  let j := c i.castSucc
  have hj : j.val = i.val := rfl
  have hi := i.isLt
  change i.val < (n + 1) + (n + 1) - 1 at hi
  have hloc : ∀ h : i.val / 2 < n, (⟨i.val / 2, h⟩ : Fin n).castSucc = interleaveHalf j := by
    intro h
    exact Fin.ext (by simp only [Fin.val_castSucc, interleaveHalf, hj])
  have hsucc : ∀ h : i.val / 2 < n,
      (⟨i.val / 2, h⟩ : Fin n).succ =
        (⟨j.val / 2 + 1, by omega⟩ : Fin (n + 1)) := by
    intro h
    exact Fin.ext (by simp only [Fin.val_succ, hj])
  change _ = upperGolubKahanOffdiag
    (if upper then scaledBidiagonal upper a b e else (scaledBidiagonal upper a b e)ᵀ) j
  simp only [shiftedEdges, get_ofFn, Word.value_widen, upperGolubKahanOffdiag]
  by_cases h : i.val % 2 = 0
  · have h' : j.val % 2 = 0 := hj ▸ h
    rw [dif_pos h, if_pos h']
    have ht : (⟨i.val / 2, by omega⟩ : Fin (n + 1)) = interleaveHalf j :=
      Fin.ext rfl
    rw [ht]
    cases upper <;> simp [scaledBidiagonal, j, c]
  · have h' : j.val % 2 ≠ 0 := hj ▸ h
    have hh : j.val / 2 < n := by omega
    rw [dif_neg h, if_neg h', dif_pos (by omega : j.val / 2 + 1 < n + 1)]
    let t : Fin n := ⟨i.val / 2, by omega⟩
    rw [← hloc t.isLt, ← hsucc t.isLt]
    cases upper
    · simpa only [Bool.false_eq_true, if_false, transpose_apply, scaledBidiagonal] using
        (storedBidiagonal_lower (fun i => (a i).scale (-e)) (fun i => (b i).scale (-e)) t).symm
    · simpa only [ite_true, scaledBidiagonal] using
        (storedBidiagonal_upper (fun i => (a i).scale (-e)) (fun i => (b i).scale (-e)) t).symm

/-- The denotation of the packed call input is exactly the oriented mass-shifted
dilation, with the index cast required by the tridiagonal interface. -/
theorem shiftedBands_matrix (k : ℕ) (upper : Bool) (a : Fin (n + 1) → Word p hp)
    (b : Fin n → Word p hp) (e : ℤ) :
    let c := bidiagonalRefinementCoord (n := n + 1) (by omega)
    storedTridiagonal (p := svdAuxiliaryPrecision k p) (shiftedDiagonal n k p upper).get (shiftedEdges k a b e).get =
      (bidiagonalMassShift upper (scaledBidiagonal upper a b e) (svdAlpha k p)).submatrix c c := by
  dsimp only
  rw [bidiagonal_shift_formula]
  let c := bidiagonalRefinementCoord (n := n + 1) (by omega)
  let d := fun i => ((shiftedDiagonal n k p upper).get i).value
  let f := fun i => ((shiftedEdges k a b e).get i).value
  let C := scaledBidiagonal upper a b e
  let g := upperGolubKahanOffdiag (if upper then C else Cᵀ)
  let m := Sum.elim (fun _ => svdAlpha k p) (fun _ => -svdAlpha k p) ∘
    bidiagonalParityCoord upper (n + 1)
  have hd (i) : d i = m (c i) := by
    simp only [d, shiftedDiagonal, get_ofFn, m, Function.comp_apply]
    cases bidiagonalParityCoord upper (n + 1) (c i) <;> simp [value_massWord]
  have hf (i) : f i = g (c i.castSucc) := value_shiftedEdges k upper a b e i
  ext i j
  change sturmTridiagonal d f i j =
    zeroDiagonalTridiagonal g (c i) (c j) + Matrix.diagonal m (c i) (c j)
  by_cases hij : i = j
  · subst j
    rw [sturmTridiagonal_diagonal, zeroDiagonalTridiagonal_diag, Matrix.diagonal_apply_eq,
      zero_add, hd]
  · rw [Matrix.diagonal_apply_ne _ (fun h => hij (c.injective h)), add_zero]
    by_cases hu : i.val + 1 = j.val
    · let t : Fin (edgeCount n) := ⟨i.val, by have h := j.isLt; change j.val < edgeCount n + 1 at h; omega⟩
      have hi : t.castSucc = i := Fin.ext rfl
      have hj : t.succ = j := Fin.ext hu
      rw [← hi, ← hj, sturmTridiagonal_upper, hf]
      simp only [zeroDiagonalTridiagonal]
      rw [if_pos (show (c t.succ).val = (c t.castSucc).val + 1 from rfl)]
    · by_cases hl : j.val + 1 = i.val
      · let t : Fin (edgeCount n) := ⟨j.val, by have h := i.isLt; change i.val < edgeCount n + 1 at h; omega⟩
        have hi : t.succ = i := Fin.ext hl
        have hj : t.castSucc = j := Fin.ext rfl
        rw [← hi, ← hj, sturmTridiagonal_lower, hf]
        have hne : t.val ≠ t.val + 1 + 1 := by omega
        simp only [zeroDiagonalTridiagonal]
        rw [if_neg (show (c t.castSucc).val ≠ (c t.succ).val + 1 from hne),
          if_pos (show (c t.succ).val = (c t.castSucc).val + 1 from rfl)]
      · rw [sturmTridiagonal_support _ _ i j hij hu hl]
        simp only [zeroDiagonalTridiagonal]
        rw [if_neg (show (c j).val ≠ (c i).val + 1 from Ne.symm hu),
          if_neg (show (c i).val ≠ (c j).val + 1 from Ne.symm hl)]

/-- The input at the call boundary, retaining the exact scale, cache and cut used to
construct it. The request depends on the same cached labels as the eventual output. -/
structure TridiagonalCall (n k p : ℕ) where
  slots : Fin k ↪ Fin (n + 1)
  preprocessing : BidiagonalPreprocessing k p
  labelCount : preprocessing.cache.labels.length = k
  low : Fin k → Bool
  diagonal : Vector (AuxWord k p) (edgeCount n + 1)
  edges : Vector (AuxWord k p) (edgeCount n)

namespace TridiagonalCall

/-- The stored label used for a slot of the original bidiagonal request. -/
noncomputable def label (call : TridiagonalCall n k p) (j : Fin k) : ℝ :=
  (call.preprocessing.cache.labels.get (Fin.cast call.labelCount.symm j)).val

/-- Denotation at the tridiagonal routine's packed dimensions. -/
noncomputable def matrix (call : TridiagonalCall n k p) :
    Matrix (Fin (edgeCount n + 1)) (Fin (edgeCount n + 1)) ℝ :=
  storedTridiagonal (p := svdAuxiliaryPrecision k p) call.diagonal.get call.edges.get

theorem matrix_isHermitian (call : TridiagonalCall n k p) : call.matrix.IsHermitian :=
  sturmTridiagonal_isHermitian _ _

private def toOneBased (m : ℕ) : Fin m ↪ ℕ where
  toFun i := i.val + 1
  inj' := fun _ _ h => Fin.ext (Nat.add_right_cancel h)

/-- The main tridiagonal routine takes the requested ranks as one-based naturals. -/
def oneBasedRanks (call : TridiagonalCall n k p) : Finset ℕ :=
  (rankSet call.slots call.low).map (toOneBased _)

theorem mem_oneBasedRanks_iff (call : TridiagonalCall n k p)
    (r : ℕ) :
    r ∈ call.oneBasedRanks ↔ (∃ j, n + 1 + ((call.slots j).val + 1) = r) ∨
      (∃ j, call.low j = true ∧ n + 1 - ((call.slots j).val + 1) + 1 = r) := by
  rw [oneBasedRanks, Finset.mem_map]
  constructor
  · rintro ⟨i, hi, hval⟩
    rcases (mem_rankSet_iff call.slots call.low i).mp hi with ⟨j, rfl⟩ | ⟨j, hlow, rfl⟩
    · exact Or.inl ⟨j, (positive_rank_oneBased call.slots call.low j).symm.trans hval⟩
    · exact Or.inr ⟨j, hlow, (negative_rank_oneBased call.slots call.low ⟨j, hlow⟩).symm.trans hval⟩
  · rintro (⟨j, hj⟩ | ⟨j, hlow, hj⟩)
    · exact ⟨_, (mem_rankSet_iff call.slots call.low _).mpr (Or.inl ⟨j, rfl⟩),
        (positive_rank_oneBased call.slots call.low j).trans hj⟩
    · exact ⟨_, (mem_rankSet_iff call.slots call.low _).mpr (Or.inr ⟨j, hlow, rfl⟩),
        (negative_rank_oneBased call.slots call.low ⟨j, hlow⟩).trans hj⟩

theorem oneBasedRanks_card (call : TridiagonalCall n k p) :
    (call.oneBasedRanks).card = (rankSet call.slots call.low).card :=
  Finset.card_map _

theorem oneBasedRanks_subset (call : TridiagonalCall n k p) :
    call.oneBasedRanks ⊆ Finset.Icc 1 (edgeCount n + 1) := by
  intro r hr
  obtain ⟨i, _, rfl⟩ := Finset.mem_map.mp hr
  have h := i.isLt
  change i.val < (n + 1) + (n + 1) at h
  apply Finset.mem_Icc.mpr
  change 1 ≤ i.val + 1 ∧ i.val + 1 ≤ edgeCount n + 1
  unfold edgeCount
  omega

/-- Enumerate the same requested ranks in the tridiagonal matrix's ascending index order. -/
def orderedIndices (call : TridiagonalCall n k p) :
    Fin (rankSet call.slots call.low).card → Fin (edgeCount n + 1) :=
  (bidiagonalRefinementCoord (n := n + 1) (by omega)).symm ∘ orderedRanks call.slots call.low

theorem orderedIndices_strictMono (call : TridiagonalCall n k p) :
    StrictMono (call.orderedIndices) :=
  (orderedRanks call.slots call.low).strictMono

theorem orderedIndices_mem_oneBasedRanks (call : TridiagonalCall n k p)
    (j : Fin (rankSet call.slots call.low).card) :
    (call.orderedIndices j).val + 1 ∈ call.oneBasedRanks :=
  Finset.mem_map.mpr ⟨orderedRanks call.slots call.low j,
    (rankSet call.slots call.low).orderEmbOfFin_mem rfl j, rfl⟩

/-- The tridiagonal request is legal at auxiliary precision and fits the SVD working
precision. -/
theorem admissible (call : TridiagonalCall n k p)
    (hk : 1 ≤ k) (hguard : precisionGuard (n + 1) p) :
    2 ≤ edgeCount n + 1 ∧ call.oneBasedRanks.Nonempty ∧ call.oneBasedRanks ⊆ Finset.Icc 1 (edgeCount n + 1) ∧
      k ≤ (call.oneBasedRanks).card ∧ (call.oneBasedRanks).card ≤ 2 * k ∧
      precisionGuard (edgeCount n + 1) (svdAuxiliaryPrecision k p) ∧
      workingPrecision (edgeCount n + 1) (call.oneBasedRanks).card
        (svdAuxiliaryPrecision k p) ≤ svdWorkingPrecision (n + 1) k p := by
  obtain ⟨hlo, hhi⟩ := card_rankSet_bounds call.slots call.low
  obtain ⟨hg, hw⟩ := call_precision_bounds call.slots call.low (by omega) (by omega) hguard
  rw [← call.oneBasedRanks_card] at hlo hhi hw
  refine ⟨?_, Finset.card_pos.mp (hk.trans hlo), call.oneBasedRanks_subset, hlo, hhi, hg, hw⟩
  unfold edgeCount
  omega

end TridiagonalCall

/-- Use the actual cached cut, and widen each scaled edge to the call precision. -/
noncomputable def assembleTridiagonalCall (upper : Bool) (a : Fin (n + 1) → Word p hp)
    (b : Fin n → Word p hp) (I : Fin k ↪ Fin (n + 1))
    (cmp : EmptyBinScan.Comparison (svdLabelPrecision k p) (svdLabelPrecision_ge_two k p))
    (pre : BidiagonalPreprocessing k p) (hlen : pre.cache.labels.length = k) :
    TridiagonalCall n k p :=
  let lower := pre.cutExecution.result.state.lower
  ⟨I, pre, hlen, fun j => cmp.lt (pre.cache.labels.get (Fin.cast hlen.symm j)) lower,
    shiftedDiagonal n k p upper, shiftedEdges k a b pre.scaleExponent⟩

private theorem preprocessing_labelCount
    (upper : Bool) (a : Fin (n + 1) → Word p hp) (b : Fin n → Word p hp)
    (I : Fin k → Fin (n + 1))
    (cmp : EmptyBinScan.Comparison (svdLabelPrecision k p) (svdLabelPrecision_ge_two k p))
    (hn : 2 ≤ n + 1) (hk : 1 ≤ k) (hkn : k ≤ n + 1) (hguard : precisionGuard (n + 1) p)
    (hI : StrictMono I) (pre : BidiagonalPreprocessing k p)
    (hpre : preprocessBidiagonal upper a b I cmp = some pre) :
    pre.cache.labels.length = k := by
  cases he : normalizationExponent a b with
  | none => simp [preprocessBidiagonal, he] at hpre
  | some e =>
    obtain ⟨selected, hselected, _, hlen, _⟩ :=
      preprocessBidiagonal_spec upper a b I cmp hn hk hkn hguard hI he
    simpa only [Option.some.inj (hpre.symm.trans hselected)] using hlen

/-- The deterministic nonzero path yields the typed input for the single call. -/
noncomputable def prepareTridiagonalCall (upper : Bool) (a : Fin (n + 1) → Word p hp)
    (b : Fin n → Word p hp) (I : Fin k → Fin (n + 1))
    (cmp : EmptyBinScan.Comparison (svdLabelPrecision k p) (svdLabelPrecision_ge_two k p))
    (hn : 2 ≤ n + 1) (hk : 1 ≤ k) (hguard : precisionGuard (n + 1) p)
    (hI : StrictMono I) : Option (TridiagonalCall n k p) :=
  let hkn : k ≤ n + 1 := by
    simpa using Fintype.card_le_of_injective I hI.injective
  Option.pmap (assembleTridiagonalCall upper a b ⟨I, hI.injective⟩ cmp)
    (preprocessBidiagonal upper a b I cmp)
    (preprocessing_labelCount upper a b I cmp hn hk hkn hguard hI)

/-- The assembled input retains the prescribed scale, label error, and low/high cut. -/
theorem prepareTridiagonalCall_spec (upper : Bool) (a : Fin (n + 1) → Word p hp)
    (b : Fin n → Word p hp) (I : Fin k → Fin (n + 1))
    (cmp : EmptyBinScan.Comparison (svdLabelPrecision k p) (svdLabelPrecision_ge_two k p))
    (hn : 2 ≤ n + 1) (hk : 1 ≤ k) (hguard : precisionGuard (n + 1) p)
    (hI : StrictMono I) {e : ℤ} (he : normalizationExponent a b = some e) :
    ∃ call : TridiagonalCall n k p,
      prepareTridiagonalCall upper a b I cmp hn hk hguard hI = some call ∧
      (∀ j, call.slots j = I j) ∧ call.preprocessing.scaleExponent = e ∧
      (∀ j, |call.label j - ascendingRealSpectrum (scaledBidiagonal upper a b e) (I j)| ≤
        unitRoundoff (svdAuxiliaryPrecision k p) / 64) ∧
      let cut := call.preprocessing.cutExecution.result.state
      1 ≤ cut.j ∧ cut.j ≤ k + 1 ∧
      cut.lower.val = (cut.j : ℝ) * svdAlpha k p ∧
      cut.upper.val = ((cut.j + 1 : ℕ) : ℝ) * svdAlpha k p ∧
      (∀ j, call.low j = true ↔ call.label j < cut.lower.val) ∧
      (∀ j, call.low j = true → call.label j ≤ 2 * unitRoundoff p) ∧
      (∀ j, call.low j = false →
        cut.upper.val ≤ call.label j ∧ 2 * svdAlpha k p ≤ call.label j) ∧
      call.matrix = (bidiagonalMassShift upper (scaledBidiagonal upper a b e)
        (svdAlpha k p)).submatrix (bidiagonalRefinementCoord (by omega))
          (bidiagonalRefinementCoord (by omega)) := by
  have hkn : k ≤ n + 1 := by
    simpa using Fintype.card_le_of_injective I hI.injective
  obtain ⟨pre, hpre, hscale, hlen, hlabel, hfirst, hlast, _, _, hlower, hupper, hsides, _⟩ :=
    preprocessBidiagonal_spec upper a b I cmp hn hk hkn hguard hI he
  let call := assembleTridiagonalCall upper a b ⟨I, hI.injective⟩ cmp pre hlen
  have hcompare (j : Fin k) :
      call.low j = true ↔ call.label j < pre.cutExecution.result.state.lower.val :=
    cmp.correct _ _
  refine ⟨call, ?_, fun _ => rfl, hscale, ?_, hfirst, hlast, hlower, hupper,
    hcompare, ?_, ?_, ?_⟩
  · simp only [prepareTridiagonalCall]
    exact Option.pmap_eq_some_iff.mpr ⟨pre, hlen, hpre, rfl⟩
  · intro j
    simpa only [TridiagonalCall.label, call, assembleTridiagonalCall, Fin.cast_cast, Fin.cast_eq_self]
      using hlabel (Fin.cast hlen.symm j)
  · intro j hlow
    rcases hsides (Fin.cast hlen.symm j) with hlo | hhi
    · exact hlo.2
    · have hα : 0 ≤ svdAlpha k p := by
        rw [svdAlpha_eq_unitRoundoff]
        exact (unitRoundoff_pos _).le
      have hends : pre.cutExecution.result.state.lower.val ≤
          pre.cutExecution.result.state.upper.val := by
        rw [hlower, hupper]
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.le_succ _) hα
      exact False.elim ((not_lt_of_ge (hends.trans hhi.1)) ((hcompare j).mp hlow))
  · intro j hhigh
    rcases hsides (Fin.cast hlen.symm j) with hlo | hhi
    · exact False.elim (Bool.false_ne_true (hhigh ▸ (hcompare j).mpr hlo.1))
    · exact hhi
  · change storedTridiagonal (p := svdAuxiliaryPrecision k p) _ (shiftedEdges k a b pre.scaleExponent).get = _
    rw [hscale]
    exact shiftedBands_matrix k upper a b e

private theorem orderedEigenvalue_finCongr {l m : ℕ} (h : l = m)
    (A : Matrix (Fin m) (Fin m) ℝ) (hA : A.IsHermitian) (j : Fin m) :
    hermitianOrderedEigenvalue (hA.submatrix (finCongr h)) ((finCongr h).symm j).rev =
      hermitianOrderedEigenvalue hA j.rev := by
  subst l
  simp [finCongr]

private theorem operatorNorm_finCongr {l m : ℕ} (h : l = m)
    (A : Matrix (Fin m) (Fin m) ℝ) :
    realMatrixOperatorNorm (A.submatrix (finCongr h) (finCongr h)) =
      realMatrixOperatorNorm A := by
  subst l
  simp [finCongr]

private theorem svdAlpha_pos (k p : ℕ) : 0 < svdAlpha k p := by
  rw [svdAlpha_eq_unitRoundoff]
  exact unitRoundoff_pos _

/-- The packed tridiagonal matrix has the complete ascending shifted spectrum. -/
theorem TridiagonalCall.orderedEigenvalue (call : TridiagonalCall n k p) (upper : Bool)
    (C : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (hC : bidiagonalSupport upper C)
    (hcall : call.matrix = (bidiagonalMassShift upper C (svdAlpha k p)).submatrix
      (bidiagonalRefinementCoord (by omega)) (bidiagonalRefinementCoord (by omega)))
    (j : Fin ((n + 1) + (n + 1))) :
    NoisyRankCertificate.ascendingEigenvalue call.matrix_isHermitian
      ((bidiagonalRefinementCoord (by omega)).symm j) =
      ascendingMassValues (svdAlpha k p) (ascendingRealSpectrum C) j := by
  let A := bidiagonalMassShift upper C (svdAlpha k p)
  let hA := bidiagonalMassShift_isHermitian upper C (svdAlpha k p)
  let c := bidiagonalRefinementCoord (n := n + 1) (by omega)
  let hB := hA.submatrix c
  change hermitianOrderedEigenvalue call.matrix_isHermitian (c.symm j).rev = _
  calc
    _ = hermitianOrderedEigenvalue hB (c.symm j).rev :=
      orderedEigenvalue_eq_of_charpoly _ _ (congrArg Matrix.charpoly hcall) _
    _ = hermitianOrderedEigenvalue hA j.rev :=
      orderedEigenvalue_finCongr (by omega) A hA j
    _ = _ := bidiagonalMassShift_orderedEigenvalue upper C _ hC (svdAlpha_pos k p) j

/-- Each output position that supplies a parity has the corresponding exact signed
mass magnitude in the same packed tridiagonal input. -/
theorem TridiagonalCall.selectedEigenvalue (call : TridiagonalCall n k p) (upper : Bool)
    (C : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (hC : bidiagonalSupport upper C)
    (hcall : call.matrix = (bidiagonalMassShift upper C (svdAlpha k p)).submatrix
      (bidiagonalRefinementCoord (by omega)) (bidiagonalRefinementCoord (by omega)))
    (j : Column call.low) :
    NoisyRankCertificate.ascendingEigenvalue call.matrix_isHermitian
      (call.orderedIndices (outputIndex call.slots call.low j)) =
      signedMass call.low (svdAlpha k p) (ascendingRealSpectrum C ∘ call.slots) j := by
  change NoisyRankCertificate.ascendingEigenvalue call.matrix_isHermitian
    ((bidiagonalRefinementCoord (by omega)).symm (orderedRanks call.slots call.low (outputIndex call.slots call.low j))) = _
  rw [call.orderedEigenvalue upper C hC hcall, orderedRanks_outputIndex]
  cases j with
  | inl i => exact ascendingMassValues_natAdd _ _ _
  | inr i =>
    change ascendingMassValues (svdAlpha k p) (ascendingRealSpectrum C)
      (Fin.castAdd (n + 1) (call.slots i.val).rev) = _
    rw [ascendingMassValues_castAdd, Fin.rev_rev]
    rfl

/-- The precise shifted input norm bound used in the oracle error transfer. -/
theorem TridiagonalCall.operatorNorm_le (call : TridiagonalCall n k p)
    (hp : 2 ≤ p) (upper : Bool)
    (C : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (hC : bidiagonalSupport upper C) (hCnorm : realMatrixOperatorNorm C ≤ 1 / 2)
    (hcall : call.matrix = (bidiagonalMassShift upper C (svdAlpha k p)).submatrix
      (bidiagonalRefinementCoord (by omega)) (bidiagonalRefinementCoord (by omega))) :
    realMatrixOperatorNorm call.matrix ≤ 1 / 2 + unitRoundoff p ∧
      realMatrixOperatorNorm call.matrix < 1 := by
  have hκ : (1 : ℝ) ≤ svdKappa k := by
    have h : 0 < svdKappa k := by unfold svdKappa; positivity
    exact_mod_cast h
  have hαu : svdAlpha k p ≤ unitRoundoff p := by
    unfold svdAlpha
    exact div_le_self (unitRoundoff_pos _).le hκ
  rw [hcall]
  change _ ∧ realMatrixOperatorNorm
    ((bidiagonalMassShift upper C (svdAlpha k p)).submatrix (finCongr _) (finCongr _)) < _
  rw [operatorNorm_finCongr (by unfold edgeCount; omega)]
  exact bidiagonalMassShift_operatorNorm_lt_one upper C _ _ hC (svdAlpha_pos k p)
    hαu hCnorm ((unitRoundoff_le_quarter p hp).trans_lt (by norm_num))

end NumStability.CertifiedTridiagonalEigenpairs.BidiagonalSVDRequest
