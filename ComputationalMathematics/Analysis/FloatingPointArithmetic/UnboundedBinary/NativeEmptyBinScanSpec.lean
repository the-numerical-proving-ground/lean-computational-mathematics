import ComputationalMathematics.Analysis.FloatingPointArithmetic.UnboundedBinary.NativeEmptyBinScanWork

/-!
# Correctness of the cached first-empty-bin execution

The scan returns the exact first empty positive-indexed bin and its two
endpoints. Its low and high sides have bounds in units of the bin width.
-/

namespace NumStability.FloatingPointFormat.UnboundedBinary.EmptyBinScan.SourceWork

variable {p : ℕ} {hp : 2 ≤ p}

/-- The model's actual linear scan returns the first empty half-open bin.
The final disjunction gives the two endpoint conventions and their sharp
bounds in terms of the label count and the width. -/
theorem runStored_cut_spec (cmp : Comparison p hp) (alpha : Word p hp) (e : ℤ)
    (ha : alpha.val = (2 : ℝ) ^ e) (labels : List (Word p hp))
    (hsize : labels.length + 2 < 2 ^ p)
    (hsorted : labels.Pairwise (fun a b => a.val ≤ b.val)) :
    let s := fun i : Fin labels.length => (labels.get i).val
    let cut := (runStored cmp alpha labels).result.state
    1 ≤ cut.j ∧ cut.j ≤ labels.length + 1 ∧ EmptyCutBin alpha.val s cut.j ∧
    (∀ m : ℕ, 1 ≤ m → m < cut.j → ∃ i, InCutBin alpha.val m (s i)) ∧
    cut.lower.val = (cut.j : ℝ) * alpha.val ∧
    cut.upper.val = ((cut.j + 1 : ℕ) : ℝ) * alpha.val ∧
    (∀ i : Fin labels.length,
      (s i < cut.lower.val ∧ s i ≤ ((labels.length : ℝ) + 1) * alpha.val) ∨
      (cut.upper.val ≤ s i ∧ 2 * alpha.val ≤ s i)) := by
  dsimp only
  let s := fun i : Fin labels.length => (labels.get i).val
  let cut := (runStored cmp alpha labels).result.state
  let a := (2 : ℝ) ^ e
  have hpos : 0 < a := zpow_pos (by norm_num) e
  have hj : cut.j = firstEmptyCutBin a s hpos :=
    runStored_firstEmptyCutBin cmp alpha e ha labels hsize hsorted
  have hv : cut.Valid e := by
    change (runStored cmp alpha labels).result.state.Valid e
    rw [runStored_result_eq cmp alpha e ha]
    exact (scan_from_initial_valid_bounds cmp e labels hsize).1
  obtain ⟨hfirst, hlast, hempty⟩ := firstEmptyCutBin_spec a s hpos
  have hfirst' : 1 ≤ cut.j := hj.symm ▸ hfirst
  have hlast' : cut.j ≤ labels.length + 1 := hj.symm ▸ hlast
  have hlo : cut.lower.val = (cut.j : ℝ) * a := hv.2.2.1
  have hhi : cut.upper.val = ((cut.j + 1 : ℕ) : ℝ) * a := hv.2.2.2
  rw [ha]
  refine ⟨hfirst', hlast', hj.symm ▸ hempty, ?_, hlo, hhi, ?_⟩
  · intro m hm hbefore
    exact firstEmptyCutBin_min a s hpos hm (hj ▸ hbefore)
  · intro i
    have hdich : s i < cut.lower.val ∨ cut.upper.val ≤ s i := by
      rw [hlo, hhi, hj]
      exact firstEmptyCutBin_dichotomy a s hpos i
    rcases hdich with hl | hh
    · have hindex : (cut.j : ℝ) ≤ (labels.length : ℝ) + 1 := by exact_mod_cast hlast'
      exact Or.inl ⟨hl, (hl.le.trans_eq hlo).trans
        (mul_le_mul_of_nonneg_right hindex hpos.le)⟩
    · have hindex : (2 : ℝ) ≤ ((cut.j + 1 : ℕ) : ℝ) := by
        exact_mod_cast (show 2 ≤ cut.j + 1 by omega)
      exact Or.inr ⟨hh, (mul_le_mul_of_nonneg_right hindex hpos.le).trans
        (hhi.symm.trans_le hh)⟩

end NumStability.FloatingPointFormat.UnboundedBinary.EmptyBinScan.SourceWork
