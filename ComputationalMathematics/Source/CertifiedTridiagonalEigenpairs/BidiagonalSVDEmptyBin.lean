import ComputationalMathematics.Analysis.FloatingPointArithmetic.UnboundedBinary.NativeEmptyBinScanSpec
import ComputationalMathematics.Source.CertifiedTridiagonalEigenpairs.BidiagonalSVDPrecision

/-!
# Exact first-empty-bin cut for selected bidiagonal singular values

The input to this phase is the sorted stream of stored, nonnegative labels
at the scalar-refinement working precision. All bin endpoints also fit at
the input precision. The theorem covers `svd:bins` and `svd:low-high`.
-/

namespace NumStability.CertifiedTridiagonalEigenpairs

open FloatingPointFormat.UnboundedBinary
open FloatingPointFormat.UnboundedBinary.EmptyBinScan
open FloatingPointFormat.UnboundedBinary.EmptyBinScan.SourceWork

theorem svdBinLabelPrecision_ge_two (k p : ℕ) : 2 ≤ svdAuxiliaryPrecision k p + 15 := by
  omega

/-- The common scale used by the cached endpoint scan. -/
noncomputable def svdBinWidthWord (k p : ℕ) :
    Word (svdAuxiliaryPrecision k p + 15) (svdBinLabelPrecision_ge_two k p) := by
  refine ⟨svdAlpha k p, ?_⟩
  rw [svdAlpha_eq_unitRoundoff]
  exact native_zpow _ _ (-((p + Nat.clog 2 k : ℕ) : ℤ))

/-- Exact endpoints and source low/high bounds for the first empty bin. -/
theorem svd_empty_bin_cut (n k p : ℕ) (hp : 2 ≤ p)
    (cmp : Comparison (svdAuxiliaryPrecision k p + 15) (svdBinLabelPrecision_ge_two k p))
    (labels : List (Word (svdAuxiliaryPrecision k p + 15) (svdBinLabelPrecision_ge_two k p)))
    (hn : 2 ≤ n) (hk : 1 ≤ k) (hkn : k ≤ n) (hlength : labels.length = k)
    (hguard : precisionGuard n p) (_hnonneg : ∀ a ∈ labels, 0 ≤ a.val)
    (hsorted : labels.Pairwise (fun a b => a.val ≤ b.val)) :
    let u := unitRoundoff p
    let alpha := (svdBinWidthWord k p).val
    let s := fun i : Fin labels.length => (labels.get i).val
    let execution := runStored cmp (svdBinWidthWord k p) labels
    let cut := execution.result.state
    alpha = svdAlpha k p ∧
    k + 2 ≤ 2 * n ∧ 2 * n < 2 ^ p ∧
    (∀ m : ℕ, 1 ≤ m → m ≤ k + 2 → Native p hp ((m : ℝ) * alpha)) ∧
    (∀ m l : ℕ, m < l → ∀ x : ℝ, InCutBin alpha m x → ¬ InCutBin alpha l x) ∧
    1 ≤ cut.j ∧ cut.j ≤ k + 1 ∧ EmptyCutBin alpha s cut.j ∧
    (∀ m : ℕ, 1 ≤ m → m < cut.j → ∃ i, InCutBin alpha m (s i)) ∧
    cut.lower.val = (cut.j : ℝ) * alpha ∧
    cut.upper.val = ((cut.j + 1 : ℕ) : ℝ) * alpha ∧
    ((k : ℝ) + 1) * alpha ≤ 2 * u ∧
    (∀ i : Fin labels.length,
      (s i < cut.lower.val ∧ s i ≤ ((k : ℝ) + 1) * alpha) ∨
      (cut.upper.val ≤ s i ∧ 2 * alpha ≤ s i)) ∧
    execution.trace.length ≤ 71 * k
 := by
  dsimp only
  let e : ℤ := -((p + Nat.clog 2 k : ℕ) : ℤ)
  let alpha := (svdBinWidthWord k p).val
  let cut := (runStored cmp (svdBinWidthWord k p) labels).result.state
  have ha : alpha = (2 : ℝ) ^ e :=
    svdAlpha_eq_unitRoundoff k p
  have hpositive : 0 < alpha := by rw [ha]; exact zpow_pos (by norm_num) e
  have hwidth : alpha = svdAlpha k p := rfl
  have hbefore : k + 2 ≤ 2 * n := by omega
  have hpow : 0 < (2 : ℝ) ^ p := by positivity
  have hreal : (n : ℝ) / (2 : ℝ) ^ p ≤ 1 / 128 := by
    simpa only [precisionGuard, unitRoundoff, zpow_neg, zpow_natCast, div_eq_mul_inv] using hguard
  have hnsmall := (div_le_iff₀ hpow).mp hreal
  have hprecision : 2 * n < 2 ^ p := by
    exact_mod_cast (show (2 : ℝ) * n < (2 : ℝ) ^ p by linarith)
  have hsize : k + 2 < 2 ^ p := hbefore.trans_lt hprecision
  have hlabelPrecision : p ≤ svdAuxiliaryPrecision k p + 15 := by
    unfold svdAuxiliaryPrecision
    omega
  have hscanSize : labels.length + 2 < 2 ^ (svdAuxiliaryPrecision k p + 15) := by
    rw [hlength]
    exact hsize.trans_le (Nat.pow_le_pow_right (by decide) hlabelPrecision)
  obtain ⟨hfirst, hlast, hempty, hoccupied, hlo, hhi, hsides⟩ :=
    runStored_cut_spec cmp (svdBinWidthWord k p) e ha labels hscanSize hsorted
  have hlast' : cut.j ≤ k + 1 := by simpa only [← hlength] using hlast
  have hκ : (k : ℝ) ≤ svdKappa k := by exact_mod_cast le_svdKappa k
  have hwidthBound : ((k : ℝ) + 1) * alpha ≤ 2 * unitRoundoff p := by
    have hκpos : 0 < (svdKappa k : ℝ) := by unfold svdKappa; positivity
    have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
    have h2κ : (k : ℝ) + 1 ≤ 2 * (svdKappa k : ℝ) := by linarith
    change ((k : ℝ) + 1) * svdAlpha k p ≤ 2 * unitRoundoff p
    rw [svdAlpha, ← mul_div_assoc]
    apply (div_le_iff₀ hκpos).mpr
    have h := mul_le_mul_of_nonneg_right h2κ (unitRoundoff_pos p).le
    nlinarith only [h]
  have hwork := runStored_work_linear cmp (svdBinWidthWord k p) labels (by simpa only [hlength] using hk)
  refine ⟨hwidth, hbefore, hprecision, ?_, ?_, hfirst, hlast', hempty, hoccupied, hlo, hhi,
    hwidthBound, ?_, ?_⟩
  · intro m _ hm
    change Native p hp ((m : ℝ) * alpha)
    rw [ha]
    exact native_mul_zpow (native_natCast_of_lt_two_pow p hp (hm.trans_lt hsize)) e
  · intro m l hml x hx hy
    have hindex : ((m + 1 : ℕ) : ℝ) ≤ (l : ℝ) := by exact_mod_cast hml
    have hscale := mul_le_mul_of_nonneg_right hindex hpositive.le
    exact (not_lt_of_ge (hscale.trans hy.1)) hx.2
  · intro i
    simpa only [hlength] using hsides i
  · simpa only [hlength] using hwork

end NumStability.CertifiedTridiagonalEigenpairs
