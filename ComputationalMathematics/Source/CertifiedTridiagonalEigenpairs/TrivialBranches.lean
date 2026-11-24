import ComputationalMathematics.Source.CertifiedTridiagonalEigenpairs.TrivialBranchesTarget

/-!
# Correctness of the exact tridiagonal branches
-/

namespace NumStability.CertifiedTridiagonalEigenpairs

open FloatingPointFormat.UnboundedBinary

theorem exactBranchOutputWords_length {p n k : ℕ} {hp : 2 ≤ p}
    (out : ExactBranchOutput p hp n k) :
    (exactBranchOutputWords out).length = k + (n + 1) * k := by
  simp [exactBranchOutputWords, Nat.mul_comm]

theorem exactBranchOutputWords_length_le {p n k : ℕ} {hp : 2 ≤ p}
    (out : ExactBranchOutput p hp n k) :
    (exactBranchOutputWords out).length ≤ 2 * ((n + 1) * k) := by
  rw [exactBranchOutputWords_length]
  have h : k ≤ (n + 1) * k := Nat.le_mul_of_pos_left k (Nat.succ_pos _)
  omega

theorem tridiagonalExactBranches : SourceTargets.tridiagonalExactBranches := by
  intro p n k hp a b J hk _hguard
  dsimp only
  have hdispatch := exactBranchLabel_isSome_iff a b
  constructor
  · constructor
    · intro h
      have hn : ¬(exactBranchLabel a b).isSome := by
        unfold exactBranch at h
        cases H : exactBranchLabel a b <;> simp [H] at h ⊢
      have hs := not_or.mp (hdispatch.not.mp hn)
      exact ⟨hs.1, by omega⟩
    · rintro ⟨hT, hn⟩
      have hne : n ≠ 0 := by omega
      have hnotsome : ¬(exactBranchLabel a b).isSome :=
        hdispatch.not.mpr (not_or.mpr ⟨hT, hne⟩)
      unfold exactBranch
      cases H : exactBranchLabel a b <;> simp [H] at hnotsome ⊢
  · intro hi
    have his := hdispatch.mpr hi
    cases H : exactBranchLabel a b with
    | none => simp [H] at his
    | some label =>
      let out : ExactBranchOutput p hp n k :=
        ⟨fun _ => label, fun i j => coordinateWord p hp i (J j), 0⟩
      have hout : exactBranch a b J = some out := by simp [exactBranch, H, out]
      obtain ⟨htrials, hlabels, hcoord, hres, hgram⟩ := exactBranch_correct hout
      refine ⟨out, hout, ?_, ?_, hcoord, hlabels, hres, hgram, htrials,
        exactBranchOutputWords_length out, exactBranchOutputWords_length_le out, ?_⟩
      · intro hz j
        have hzero := exactBranchLabel_eq_some_zero hz
        rw [H, Option.some.injEq] at hzero
        exact hzero
      · intro hn
        subst n
        have hkn : k ≤ 1 := by
          simpa only [Fintype.card_fin] using Fintype.card_le_of_injective J J.injective
        refine ⟨by omega, fun j => ⟨?_, ?_⟩⟩
        · rw [exactBranchLabel_eq_some_scalar, Option.some.injEq] at H
          exact H.symm
        · intro i
          have hij : i = J j := by
            exact Fin.ext (by have hi := i.isLt; have hj := (J j).isLt; omega)
          exact (hcoord i j).trans (if_pos hij)
      · rw [htrials, zero_add, mul_one]
        have hp' : 0 < p := by omega
        exact (exactBranchWorkBound_le hk).trans (Nat.le_mul_of_pos_right _ hp')

end NumStability.CertifiedTridiagonalEigenpairs
