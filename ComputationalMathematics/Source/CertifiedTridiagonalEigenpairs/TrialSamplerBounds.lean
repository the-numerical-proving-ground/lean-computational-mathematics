import ComputationalMathematics.Source.CertifiedTridiagonalEigenpairs.PerturbationCoupling
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.LinearAlgebra.Matrix.Hermitian

/-!
# Work and matrix perturbation bounds for the trial sampler

The sampled and coupled matrices change only diagonal entries of the fixed
matrix. A pointwise error bound therefore controls the Euclidean operator norm.
-/

namespace NumStability.CertifiedTridiagonalEigenpairs

open MeasureTheory
open scoped Matrix.Norms.L2Operator

theorem samplerTrace_work_le {n k : ℕ} (hn : 2 ≤ n) (hkn : k ≤ n) (p : ℕ) :
    ScalarWork.work (samplerTrace n k p) ≤ 87 * n * Nat.clog 2 n := by
  have hb := rngBits_le hkn
  have hL := Nat.clog_pos (by decide : 1 < 2) (by omega : 1 < n)
  rw [samplerTrace_work, Nat.mul_comm 87 n, Nat.mul_assoc]
  exact Nat.mul_le_mul_left n (by omega)

private theorem norm_sub_le_of_offDiag_eq {n : ℕ} {A B : Matrix (Fin n) (Fin n) ℝ}
    {ε : ℝ} (hε : 0 ≤ ε) (hoff : ∀ i j, i ≠ j → A i j = B i j)
    (hdiag : ∀ i, |A i i - B i i| ≤ ε) :
    ‖A - B‖ ≤ ε := by
  have hEq : A - B = Matrix.diagonal (fun i => A i i - B i i) := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp
    · simp [Matrix.diagonal_apply_ne _ hij, hoff i j hij]
  rw [hEq, Matrix.l2_opNorm_diagonal, pi_norm_le_iff_of_nonneg hε]
  simpa only [Real.norm_eq_abs] using hdiag

/-- The new diagonal consists of working-precision words and the original
off-diagonal words retain their denotations. -/
theorem sampledMatrix_native (n k p : ℕ) (S : Matrix (Fin n) (Fin n) ℝ)
    (words : Fin n → FairBitWord (rngBits n k))
    (hS : ∀ i j, i ≠ j → FloatingPointFormat.UnboundedBinary.Native
      (workingPrecision n k p) (workingPrecision_ge_two n k p) (S i j))
    (i j : Fin n) :
    FloatingPointFormat.UnboundedBinary.Native (workingPrecision n k p)
      (workingPrecision_ge_two n k p) (sampledMatrix n k p S words i j) := by
  by_cases hij : i = j
  · subst j
    rw [sampledMatrix_diag]
    exact FloatingPointFormat.UnboundedBinary.roundToEven_native _ _ _
  · rw [sampledMatrix_offDiag _ _ _ _ _ hij]
    exact hS i j hij

theorem sampledMatrix_isHermitian {n k p : ℕ} {S : Matrix (Fin n) (Fin n) ℝ}
    (hS : S.IsHermitian) (words : Fin n → FairBitWord (rngBits n k)) :
    (sampledMatrix n k p S words).IsHermitian := by
  ext i j
  rw [Matrix.conjTranspose_apply]
  by_cases hij : i = j
  · subst j
    exact star_trivial _
  · rw [sampledMatrix_offDiag _ _ _ _ _ hij,
      sampledMatrix_offDiag _ _ _ _ _ (Ne.symm hij)]
    exact hS.apply i j

/-- Both bounds on the stored matrix in `rand:matrix-error`. -/
theorem sampledMatrix_norm_bounds {n k p : ℕ} (hn : 2 ≤ n)
    (guard : precisionGuard n p) (S : Matrix (Fin n) (Fin n) ℝ)
    (hSdiag : ∀ i, |S i i| ≤ 1 / 4) (hS : ‖S‖ ≤ 3 / 4)
    (words : Fin n → FairBitWord (rngBits n k)) :
    ‖sampledMatrix n k p S words - S‖ ≤ perturbationScale p + 2 * workingRoundoff n k p ∧
    perturbationScale p + 2 * workingRoundoff n k p ≤
      FloatingPointFormat.UnboundedBinary.unitRoundoff p / 128 ∧
    ‖sampledMatrix n k p S words‖ < 1 := by
  have hδ : 0 < perturbationScale p :=
    div_pos (FloatingPointFormat.UnboundedBinary.unitRoundoff_pos p) (by norm_num)
  have hω : 0 < workingRoundoff n k p :=
    FloatingPointFormat.UnboundedBinary.unitRoundoff_pos _
  have hsub : ‖sampledMatrix n k p S words - S‖ ≤
      perturbationScale p + 2 * workingRoundoff n k p := by
    apply norm_sub_le_of_offDiag_eq (by positivity)
    · exact fun _ _ hij => sampledMatrix_offDiag n k p S words hij
    · intro i
      let center := cellCenter (perturbationScale p) (rngBits n k) (trialDraws n k words i)
      have hround := sampledMatrix_diag_roundoff hn guard S words i (hSdiag i)
      have hcenter := abs_cellCenter_lt hδ (trialDraws n k words i)
      calc
        _ = |(sampledMatrix n k p S words i i - (S i i + center)) + center| := by
          congr 1
          ring
        _ ≤ _ := by
          apply (abs_add_le _ _).trans
          dsimp [center]
          linarith
  have hbudget := (trialPrecisionBudget (k := k) hn guard).2.2.2.1
  refine ⟨hsub, hbudget, ?_⟩
  have hp : 2 ≤ p := by
    have := clog_add_le_of_precisionGuard (by omega : 0 < n) guard
    omega
  calc
    _ = ‖(sampledMatrix n k p S words - S) + S‖ := by rw [sub_add_cancel]
    _ ≤ ‖sampledMatrix n k p S words - S‖ + ‖S‖ := norm_add_le _ _
    _ < 1 := by
      linarith [FloatingPointFormat.UnboundedBinary.unitRoundoff_le_quarter p hp]

noncomputable section

/-- The comparison matrix (A_V) is formed with the coupled continuous diagonal. -/
def coupledMatrix (n k p : ℕ) (S : Matrix (Fin n) (Fin n) ℝ)
    (batch : Fin n → Fin (2 ^ rngBits n k) × ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  S + Matrix.diagonal (fun i => coupledCoordinate (perturbationScale p) (rngBits n k) (batch i))

theorem coupledMatrix_isHermitian {n k p : ℕ} {S : Matrix (Fin n) (Fin n) ℝ}
    (hS : S.IsHermitian) (batch : Fin n → Fin (2 ^ rngBits n k) × ℝ) :
    (coupledMatrix n k p S batch).IsHermitian :=
  hS.add (Matrix.isHermitian_diagonal _)

/-- On the enlarged space, the actual stored matrix and the coupled matrix
differ by at most `g / 32` in Euclidean operator norm. -/
theorem norm_sampledMatrix_sub_coupledMatrix_le {n k p : ℕ} (hn : 2 ≤ n)
    (guard : precisionGuard n p) (S : Matrix (Fin n) (Fin n) ℝ) (hS : ∀ i, |S i i| ≤ 1 / 4) :
    ∀ᵐ batch ∂vectorCoupling n (perturbationScale p) (rngBits n k),
      ‖sampledMatrix n k p S (couplingWords n k batch) - coupledMatrix n k p S batch‖ ≤
        gapScale n k p / 32 := by
  filter_upwards [vectorCoupling_trial_close n k p] with batch hb
  have hbudget := (trialPrecisionBudget (k := k) hn guard).1
  have hω : 0 < workingRoundoff n k p :=
    FloatingPointFormat.UnboundedBinary.unitRoundoff_pos _
  have hg : 0 ≤ gapScale n k p / 32 := by
    unfold gapLabelError at hbudget
    linarith
  apply norm_sub_le_of_offDiag_eq hg
  · intro i j hij
    rw [sampledMatrix_offDiag _ _ _ _ _ hij, coupledMatrix]
    simp [Matrix.diagonal_apply_ne _ hij]
  · intro i
    have hround := sampledMatrix_diag_roundoff hn guard S (couplingWords n k batch) i (hS i)
    let center := cellCenter (perturbationScale p) (rngBits n k)
      (trialDraws n k (couplingWords n k batch) i)
    let value := coupledCoordinate (perturbationScale p) (rngBits n k) (batch i)
    have hclose : |center - value| ≤ gapLabelError n k p := by
      rw [abs_sub_comm]
      exact hb i
    simp only [coupledMatrix, Matrix.add_apply, Matrix.diagonal_apply_eq]
    change |sampledMatrix n k p S (couplingWords n k batch) i i - (S i i + value)| ≤ _
    calc
      _ = |(sampledMatrix n k p S (couplingWords n k batch) i i -
             (S i i + center)) + (center - value)| := by
        congr 1
        ring
      _ ≤ _ := by
        apply (abs_add_le _ _).trans
        change |sampledMatrix n k p S (couplingWords n k batch) i i -
            (S i i + center)| + |center - value| ≤ _
        unfold gapLabelError at hclose hbudget
        linarith

end

end NumStability.CertifiedTridiagonalEigenpairs
