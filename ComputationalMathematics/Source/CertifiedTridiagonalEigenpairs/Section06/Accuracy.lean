import ComputationalMathematics.Source.CertifiedTridiagonalEigenpairs.Section06.AccuracyCore
import ComputationalMathematics.Source.CertifiedTridiagonalEigenpairs.Section06.ScoreSelection

/-! # Section 6 deterministic vector accuracy -/

open Matrix WithLp
open scoped Matrix.Norms.L2Operator

namespace NumStability.CertifiedTridiagonalEigenpairs

open FloatingPointFormat.UnboundedBinary

private theorem realEigenvalue_mem_spectrum {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.IsSymm) (j : Fin n) :
    (MatrixResolvent.isHermitian_map_ofReal hA).eigenvalues j ∈ spectrum ℝ A := by
  let μ := (MatrixResolvent.isHermitian_map_ofReal hA).eigenvalues j
  have hμ : μ ∈ spectrum ℝ (A.map Complex.ofReal) :=
    (MatrixResolvent.isHermitian_map_ofReal hA).eigenvalues_mem_spectrum_real j
  rw [← spectrum.algebraMap_mem_iff ℂ, Matrix.mem_spectrum_iff_isRoot_charpoly] at hμ
  change (A.map Complex.ofRealHom).charpoly.IsRoot (Complex.ofRealHom μ) at hμ
  rw [Matrix.charpoly_map, Polynomial.isRoot_map_iff Complex.ofReal_injective] at hμ
  exact Matrix.mem_spectrum_iff_isRoot_charpoly.mpr hμ

/-- The dimension-dependent roundoff restriction places the output
precision below the working precision. -/
theorem vectorOutputPrecision_le_workingPrecision {n p q : ℕ} (hn : 2 ≤ n)
    (hωn : unitRoundoff q ≤ unitRoundoff p / (65536 * (n : ℝ))) : p ≤ q := by
  have hn1 : 1 ≤ (n : ℝ) := by exact_mod_cast (show 1 ≤ n by omega)
  have hden : 1 ≤ 65536 * (n : ℝ) := by linarith
  have hω : unitRoundoff q ≤ unitRoundoff p :=
    hωn.trans (div_le_self (unitRoundoff_pos p).le hden)
  unfold unitRoundoff at hω
  have h := (zpow_right_strictMono₀ (show (1 : ℝ) < 2 by norm_num)).le_iff_le.mp hω
  exact_mod_cast (neg_le_neg_iff.mp h)

private theorem sqrt_sqrt_eq_quarter_rpow (n : ℕ) :
    Real.sqrt (Real.sqrt (n : ℝ)) = (n : ℝ) ^ (1 / 4 : ℝ) := by
  rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul (Nat.cast_nonneg n)]
  norm_num

/-- Numerical guarantees for the stored imaginary vector at the least
maximizing score index. The imaginary words can be obtained from a shared
forward and reverse sweep followed by one outward pass. Their stored values
determine all the normalization operations in the theorem. -/
theorem roundedTridiagonalVectorAccuracy_of_cache
    {n p q : ℕ} (hn : 2 ≤ n) (hp : 2 ≤ p) (hq : 2 ≤ q)
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsSymm) (hAnorm : ‖A‖ ≤ 2)
    (hband : ∀ i j : Fin n, i.val + 1 < j.val ∨ j.val + 1 < i.val → A i j = 0)
    (hb : ∀ i j : Fin n, i.val + 1 = j.val → |A i j| ≤ 1)
    (_hNativeA : ∀ i j : Fin n, Native q hq (A i j))
    (j : Fin n) (v : EuclideanSpace ℝ (Fin n)) (hv : ‖v‖ = 1)
    (heig : A *ᵥ v.ofLp = (MatrixResolvent.isHermitian_map_ofReal hA).eigenvalues j • v.ofLp)
    {shift η Δ : ℝ} (_hNativeShift : Native q hq shift)
    (hηpow : ∃ m : ℤ, η = (2 : ℝ) ^ m) (hηmax : η ≤ 1 / 2)
    (hΔ : 0 < Δ) (hguard : (n : ℝ) * unitRoundoff p ≤ 1 / 128)
    (hηprec : η ≤ Δ * Real.sqrt (unitRoundoff p) / (16 * (n : ℝ) ^ (1 / 4 : ℝ)))
    (hnear : |shift - (MatrixResolvent.isHermitian_map_ofReal hA).eigenvalues j| ≤ η)
    (hgap : ∀ i ≠ j, Δ ≤ |(MatrixResolvent.isHermitian_map_ofReal hA).eigenvalues i -
      (MatrixResolvent.isHermitian_map_ofReal hA).eigenvalues j|)
    (hωη : unitRoundoff q ≤ η / 4096)
    (hωΔ : unitRoundoff q ≤ unitRoundoff p * Δ / 8192)
    (hωn : unitRoundoff q ≤ unitRoundoff p / (65536 * (n : ℝ)))
    (r : Fin n)
    (hr : r = vectorSelectedIndex q hq n (by omega)
      (vectorInputDiagonal A shift) (vectorInputEdge A) η)
    (x : Fin n → Word q hq)
    (hcache : ∀ i, (x i).value = (vectorRoundedInverseColumn q hq n
      (vectorInputDiagonal A shift) (vectorInputEdge A) η r i).im) :
    vectorPivotDivisorsPositive n q hq (vectorInputDiagonal A shift) (vectorInputEdge A) η ∧
      ∃ hx : Word.euclidean x ≠ 0,
        0 < (Word.roundedNorm x).value ∧
          ∃ σ : ℝ, (σ = -1 ∨ σ = 1) ∧
            ‖Word.euclidean (Word.normalizeTo p hp x hx) - σ • v‖ < 9 * unitRoundoff p / 4 ∧
            ‖Word.euclidean (Word.normalizeTo p hp x hx) - σ • v‖ ≤ 4 * unitRoundoff p := by
  obtain ⟨m, hm⟩ := hηpow
  have hη : 0 < η := hm ▸ (by positivity : 0 < (2 : ℝ) ^ m)
  have hηnative : Native q hq η := hm ▸ native_zpow q hq m
  have htarget := realEigenvalue_mem_spectrum hA j
  let a := vectorInputDiagonal A shift
  let b := vectorInputEdge A
  have hK := vectorShiftedMatrix_eq_imaginaryShift A hA hband shift η
  obtain ⟨ha, hbe⟩ := vectorSweepInputBounds hn A hAnorm hb hηmax htarget hnear
  have hscore := (roundedVectorScoreSelection hn q hq a b A hA hη hηmax hηnative
    hωη ha hbe hK htarget hnear).2.2.2.2.2
  have hselected : (4 * (n : ℝ) * η)⁻¹ ≤ ((vectorShiftedMatrix n a b η)⁻¹ r r).im := by
    rw [hr, hK]
    exact hscore
  exact roundedVectorAccuracy_of_selectedScore hn hp hq a b hA j r v hv heig
    hη hηmax hηnative hΔ hguard (by simpa only [sqrt_sqrt_eq_quarter_rpow] using hηprec)
    hnear hgap hωη hωΔ hωn ha hbe hK hselected x hcache

end NumStability.CertifiedTridiagonalEigenpairs
