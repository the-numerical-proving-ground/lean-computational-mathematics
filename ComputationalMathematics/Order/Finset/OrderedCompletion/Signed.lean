import Mathlib.Data.Finset.Fold
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Real.Basic
import Mathlib.Order.Fin.Basic

/-!
# Ordered completion of signed labels

The reference entry seeds the lower fold, so the construction can retain
negative values and needs no finite stand-in for a missing bound.
-/

namespace NumStability.OrderStatistics

noncomputable section

private def raiseToPrecedingLabels {n k : ℕ} (I : Fin k → Fin n)
    (reference : Fin n → ℝ) (label : Fin k → ℝ) (i : Fin n) : ℝ :=
  (Finset.univ.filter fun j : Fin k => I j ≤ i).fold max (reference i) label

/-- Clip a reference entry from below by preceding selected labels and from
above by following selected labels. The inclusive comparisons also replace the
entries at selected positions. -/
def clipSelectedValues {n k : ℕ} (I : Fin k → Fin n)
    (reference : Fin n → ℝ) (label : Fin k → ℝ) (i : Fin n) : ℝ :=
  (Finset.univ.filter fun j : Fin k => i ≤ I j).fold min
    (raiseToPrecedingLabels I reference label i) label

private theorem clip_le_raise {n k : ℕ} (I : Fin k → Fin n)
    (reference : Fin n → ℝ) (label : Fin k → ℝ) (i : Fin n) :
    clipSelectedValues I reference label i ≤ raiseToPrecedingLabels I reference label i :=
  (Finset.fold_min_le _).2 (Or.inl le_rfl)

private theorem clip_le_following {n k : ℕ} (I : Fin k → Fin n)
    (reference : Fin n → ℝ) (label : Fin k → ℝ) (i : Fin n) (j : Fin k) (hij : i ≤ I j) :
    clipSelectedValues I reference label i ≤ label j :=
  (Finset.fold_min_le _).2 (Or.inr ⟨j, Finset.mem_filter.2 ⟨Finset.mem_univ _, hij⟩, le_rfl⟩)

private theorem le_clip {n k : ℕ} (I : Fin k → Fin n)
    (reference : Fin n → ℝ) (label : Fin k → ℝ) (i : Fin n) (a : ℝ)
    (hseed : a ≤ raiseToPrecedingLabels I reference label i)
    (hfollowing : ∀ j, i ≤ I j → a ≤ label j) :
    a ≤ clipSelectedValues I reference label i :=
  (Finset.le_fold_min _).2 ⟨hseed, fun j hj => hfollowing j (Finset.mem_filter.1 hj).2⟩

theorem clipSelectedValues_monotone {n k : ℕ} (I : Fin k → Fin n)
    (reference : Fin n → ℝ) (label : Fin k → ℝ) (hreference : Monotone reference) :
    Monotone (clipSelectedValues I reference label) := by
  intro i j hij
  apply le_clip
  · apply (clip_le_raise I reference label i).trans
    apply (Finset.fold_max_le _).2
    refine ⟨(Finset.le_fold_max _).2 (Or.inl (hreference hij)), ?_⟩
    intro l hl
    exact (Finset.le_fold_max _).2 (Or.inr ⟨l,
      Finset.mem_filter.2 ⟨Finset.mem_univ _, (Finset.mem_filter.1 hl).2.trans hij⟩, le_rfl⟩)
  · intro l hl
    exact clip_le_following I reference label i l (hij.trans hl)

theorem clipSelectedValues_apply_selected {n k : ℕ} (I : Fin k → Fin n)
    (reference : Fin n → ℝ) (label : Fin k → ℝ) (hI : StrictMono I)
    (hlabel : Monotone label) (j : Fin k) :
    clipSelectedValues I reference label (I j) = label j := by
  apply le_antisymm (clip_le_following I reference label (I j) j le_rfl)
  apply le_clip
  · exact (Finset.le_fold_max _).2
      (Or.inr ⟨j, Finset.mem_filter.2 ⟨Finset.mem_univ _, le_rfl⟩, le_rfl⟩)
  · intro l hl
    exact hlabel (hI.le_iff_le.1 hl)

theorem clipSelectedValues_abs_sub_le {n k : ℕ} (I : Fin k → Fin n)
    (reference : Fin n → ℝ) (label : Fin k → ℝ) (hrefer : Monotone reference)
    {δ : ℝ} (hδ : 0 ≤ δ) (herror : ∀ j, |label j - reference (I j)| ≤ δ) (i : Fin n) :
    |clipSelectedValues I reference label i - reference i| ≤ δ := by
  apply abs_sub_le_iff.2
  constructor
  · apply sub_le_iff_le_add.2
    apply (clip_le_raise I reference label i).trans
    apply (Finset.fold_max_le _).2
    refine ⟨le_add_of_nonneg_left hδ, ?_⟩
    intro j hj
    exact (sub_le_iff_le_add.1 (abs_sub_le_iff.1 (herror j)).1).trans
      (add_le_add le_rfl (hrefer (Finset.mem_filter.1 hj).2))
  · apply sub_le_comm.1
    apply le_clip
    · exact (Finset.le_fold_max _).2 (Or.inl (sub_le_self _ hδ))
    · intro j hj
      exact (sub_le_sub_right (hrefer hj) _).trans
        (sub_le_comm.1 (abs_sub_le_iff.1 (herror j)).2)

end

end NumStability.OrderStatistics
