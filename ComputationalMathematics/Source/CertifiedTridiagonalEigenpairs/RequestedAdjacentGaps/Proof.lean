import ComputationalMathematics.Source.CertifiedTridiagonalEigenpairs.RequestedAdjacentGaps.Target

/-! Counting the distinct existing adjacent pairs that border a requested rank. -/

namespace NumStability.CertifiedTridiagonalEigenpairs

theorem requestedAdjacentGapIndices_card_le (n : ℕ) (J : Finset ℕ) :
    (requestedAdjacentGapIndices n J).card ≤ 2 * J.card := by
  let predecessors := J.image (fun j => j - 1)
  have hsubset : requestedAdjacentGapIndices n J ⊆ J ∪ predecessors := by
    intro i hi
    rcases (Finset.mem_filter.mp hi).2 with hleft | hright
    · exact Finset.mem_union.mpr (Or.inl hleft)
    · apply Finset.mem_union.mpr
      exact Or.inr (Finset.mem_image.mpr ⟨i + 1, hright, Nat.add_sub_cancel i 1⟩)
  calc
    (requestedAdjacentGapIndices n J).card ≤ (J ∪ predecessors).card :=
      Finset.card_le_card hsubset
    _ ≤ J.card + predecessors.card := Finset.card_union_le _ _
    _ ≤ J.card + J.card := Nat.add_le_add_left Finset.card_image_le _
    _ = 2 * J.card := by omega

theorem requestedAdjacentGapCardinality : SourceTargets.requestedAdjacentGapCardinality := by
  intro n J _ _
  exact requestedAdjacentGapIndices_card_le n J

end NumStability.CertifiedTridiagonalEigenpairs
