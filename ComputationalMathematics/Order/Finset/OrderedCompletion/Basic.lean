import ComputationalMathematics.Order.Finset.OrderedCompletion.Defs
import Mathlib.Tactic.Linarith

/-!
# Bounds for ordered completion at selected positions

The selected lower envelope grows with the position. Clipping each raised
reference entry by the following selected values yields an ascending completion
that preserves the selected labels and their uniform error budget.
-/

namespace NumStability.OrderStatistics

/-- The zero-seeded lower envelope is nonnegative for any selected values. -/
theorem selectedLowerEnvelope_nonneg {n k : ℕ} (I : Fin k → Fin n)
    (s : Fin k → ℝ) (i : Fin n) : 0 ≤ selectedLowerEnvelope I s i := by
  exact (Finset.le_fold_max _).mpr (Or.inl le_rfl)

/-- An upper bound on zero and all preceding selected values bounds the envelope. -/
theorem selectedLowerEnvelope_le {n k : ℕ} (I : Fin k → Fin n)
    (s : Fin k → ℝ) (i : Fin n) (b : ℝ)
    (hzero : 0 ≤ b) (hs : ∀ j, I j ≤ i → s j ≤ b) :
    selectedLowerEnvelope I s i ≤ b := by
  apply (Finset.fold_max_le _).mpr
  exact ⟨hzero, fun j hj => hs j (Finset.mem_filter.mp hj).2⟩

/-- A selected value participates in the lower envelope at its own position. -/
theorem selected_le_selectedLowerEnvelope {n k : ℕ}
    (I : Fin k → Fin n) (s : Fin k → ℝ) (j : Fin k) :
    s j ≤ selectedLowerEnvelope I s (I j) := by
  exact (Finset.le_fold_max _).mpr
    (Or.inr ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, le_rfl⟩, le_rfl⟩)

/-- Preceding selected sets grow with the position, so their envelope ascends. -/
theorem selectedLowerEnvelope_monotone {n k : ℕ}
    (I : Fin k → Fin n) (s : Fin k → ℝ) : Monotone (selectedLowerEnvelope I s) := by
  intro i h hih
  apply selectedLowerEnvelope_le I s i _ (selectedLowerEnvelope_nonneg I s h)
  intro j hj
  exact (Finset.le_fold_max _).mpr
    (Or.inr ⟨j, Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, hj.trans hih⟩, le_rfl⟩)

/-- Raising an entry retains the original value as a lower bound. -/
theorem truth_le_raiseToSelectedLower {n k : ℕ}
    (I : Fin k → Fin n) (truth : Fin n → ℝ) (s : Fin k → ℝ) (i : Fin n) :
    truth i ≤ raiseToSelectedLower I truth s i := le_max_left _ _

/-- Raising an entry retains the selected lower envelope as a lower bound. -/
theorem selectedLowerEnvelope_le_raiseToSelectedLower {n k : ℕ}
    (I : Fin k → Fin n) (truth : Fin n → ℝ) (s : Fin k → ℝ) (i : Fin n) :
    selectedLowerEnvelope I s i ≤ raiseToSelectedLower I truth s i := le_max_right _ _

/-- Raising an ascending reference list to its ascending lower envelope preserves order. -/
theorem raiseToSelectedLower_monotone {n k : ℕ}
    (I : Fin k → Fin n) (truth : Fin n → ℝ) (s : Fin k → ℝ)
    (htruth : Monotone truth) : Monotone (raiseToSelectedLower I truth s) := by
  intro i h hih
  exact max_le_max (htruth hih) (selectedLowerEnvelope_monotone I s hih)

/-- The final minimum fold cannot exceed its raised reference seed. -/
theorem completeSelectedValues_le_raise {n k : ℕ}
    (I : Fin k → Fin n) (truth : Fin n → ℝ) (s : Fin k → ℝ) (i : Fin n) :
    completeSelectedValues I truth s i ≤ raiseToSelectedLower I truth s i := by
  exact (Finset.fold_min_le _).mpr (Or.inl le_rfl)

/-- Every following selected value bounds the completion from above. -/
theorem completeSelectedValues_le_selected {n k : ℕ}
    (I : Fin k → Fin n) (truth : Fin n → ℝ) (s : Fin k → ℝ)
    (i : Fin n) (j : Fin k) (hij : i ≤ I j) :
    completeSelectedValues I truth s i ≤ s j := by
  exact (Finset.fold_min_le _).mpr
    (Or.inr ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hij⟩, le_rfl⟩)

/-- A lower bound on the seed and every following selected value bounds the completion. -/
theorem le_completeSelectedValues {n k : ℕ}
    (I : Fin k → Fin n) (truth : Fin n → ℝ) (s : Fin k → ℝ)
    (i : Fin n) (b : ℝ)
    (hseed : b ≤ raiseToSelectedLower I truth s i)
    (hs : ∀ j, i ≤ I j → b ≤ s j) : b ≤ completeSelectedValues I truth s i := by
  exact (Finset.le_fold_min _).mpr
    ⟨hseed, fun j hj => hs j (Finset.mem_filter.mp hj).2⟩

/-- Completion preserves the order of an ascending reference list. -/
theorem completeSelectedValues_monotone {n k : ℕ}
    (I : Fin k → Fin n) (truth : Fin n → ℝ) (s : Fin k → ℝ)
    (htruth : Monotone truth) : Monotone (completeSelectedValues I truth s) := by
  intro i h hih
  apply le_completeSelectedValues
  · exact (completeSelectedValues_le_raise I truth s i).trans
      (raiseToSelectedLower_monotone I truth s htruth hih)
  · intro j hj
    exact completeSelectedValues_le_selected I truth s i j (hih.trans hj)

/-- Nonnegative selected labels give a nonnegative completion. -/
theorem completeSelectedValues_nonneg {n k : ℕ}
    (I : Fin k → Fin n) (truth : Fin n → ℝ) (s : Fin k → ℝ)
    (hs : ∀ j, 0 ≤ s j) (i : Fin n) : 0 ≤ completeSelectedValues I truth s i := by
  apply le_completeSelectedValues
  · exact (selectedLowerEnvelope_nonneg I s i).trans
      (selectedLowerEnvelope_le_raiseToSelectedLower I truth s i)
  · intro j _
    exact hs j

/-- Ascending labels at strictly increasing positions are preserved exactly. -/
theorem completeSelectedValues_apply_selected {n k : ℕ}
    (I : Fin k → Fin n) (truth : Fin n → ℝ) (s : Fin k → ℝ)
    (hI : StrictMono I) (hs : Monotone s) (j : Fin k) :
    completeSelectedValues I truth s (I j) = s j := by
  apply le_antisymm (completeSelectedValues_le_selected I truth s (I j) j le_rfl)
  apply le_completeSelectedValues
  · exact (selected_le_selectedLowerEnvelope I s j).trans
      (selectedLowerEnvelope_le_raiseToSelectedLower I truth s (I j))
  · intro h hjh
    exact hs (hI.le_iff_le.mp hjh)

/-- Completion preserves the selected labels' uniform absolute-error budget
relative to a nonnegative ascending reference list at every coordinate.
-/
theorem completeSelectedValues_abs_sub_le {n k : ℕ}
    (I : Fin k → Fin n) (truth : Fin n → ℝ) (s : Fin k → ℝ) (δ : ℝ)
    (htruth : Monotone truth) (htruth0 : ∀ i, 0 ≤ truth i) (hδ : 0 ≤ δ)
    (herror : ∀ j, |s j - truth (I j)| ≤ δ) (i : Fin n) :
    |completeSelectedValues I truth s i - truth i| ≤ δ := by
  have hlo : truth i - δ ≤ completeSelectedValues I truth s i := by
    apply le_completeSelectedValues
    · exact (sub_le_self _ hδ).trans (truth_le_raiseToSelectedLower I truth s i)
    · intro j hij
      have horder := htruth hij
      have he := (abs_le.mp (herror j)).1
      linarith
  have hhi : completeSelectedValues I truth s i ≤ truth i + δ := by
    apply (completeSelectedValues_le_raise I truth s i).trans
    apply max_le
    · linarith
    · apply selectedLowerEnvelope_le I s i _ (by linarith [htruth0 i])
      intro j hji
      have horder := htruth hji
      have he := (abs_le.mp (herror j)).2
      linarith
  exact abs_le.mpr ⟨by linarith, by linarith⟩

end NumStability.OrderStatistics
