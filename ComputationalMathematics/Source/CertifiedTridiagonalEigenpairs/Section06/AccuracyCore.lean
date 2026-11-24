import ComputationalMathematics.Source.CertifiedTridiagonalEigenpairs.RoundedVectorLocal.Assembly
import ComputationalMathematics.Source.CertifiedTridiagonalEigenpairs.Section06.InverseRecurrence
import ComputationalMathematics.Source.CertifiedTridiagonalEigenpairs.Section06.PerturbedColumn
import ComputationalMathematics.Source.CertifiedTridiagonalEigenpairs.Section06.VectorOutput

/-! # Accuracy of the selected Section 6 inverse column -/

open Matrix WithLp
open scoped Matrix.Norms.L2Operator

namespace NumStability.CertifiedTridiagonalEigenpairs

open FloatingPointFormat.UnboundedBinary

/-- Expose the stored imaginary components as words at their existing
precision. The native representation is carried by the outward recurrence. -/
noncomputable def vectorImaginaryWords {n q : ℕ} (hq : 2 ≤ q) (wHat : Fin n → ℂ)
    (hNative : ∀ i, Native q hq (wHat i).im) : Fin n → Word q hq :=
  fun i => Classical.choose (Word.exists_value_iff_native.mpr (hNative i))

@[simp] theorem vectorImaginaryWords_value {n q : ℕ} (hq : 2 ≤ q) (wHat : Fin n → ℂ)
    (hNative : ∀ i, Native q hq (wHat i).im) (i : Fin n) :
    (vectorImaginaryWords hq wHat hNative i).value = (wHat i).im :=
  Classical.choose_spec (Word.exists_value_iff_native.mpr (hNative i))

/-- Every squared-modulus divisor in the directional sweeps and scores is
positive. Outward propagation reuses the directional pivot divisors and the
central reciprocal reuses the selected score divisor. -/
def vectorPivotDivisorsPositive (n q : ℕ) (hq : 2 ≤ q) (a b : ℕ → ℝ) (η : ℝ) : Prop :=
  ∀ i : Fin n,
    let l := vectorLeftSweep q hq a b η i.val
    let d := vectorRightSweep q hq n a b η i.val
    let t := vectorSweepTwist q hq n a b η i
    0 < vectorSquaredModulus q hq l.1 l.2 ∧
    0 < vectorSquaredModulus q hq d.1 d.2 ∧
    0 < vectorSquaredModulus q hq t.1 t.2

/-- The actual quotient at an outward step uses one of the positive
directional squared moduli. -/
theorem vectorPivotDivisorsPositive_outward {n q : ℕ} {hq : 2 ≤ q}
    {a b : ℕ → ℝ} {η : ℝ} (h : vectorPivotDivisorsPositive n q hq a b η)
    (r i : Fin n) :
    let e := vectorOutwardEdge q hq n a b η r i 0
    0 < vectorSquaredModulus q hq e.pivotRe e.pivotNegIm := by
  by_cases hleft : i.val < r.val
  · simpa [vectorOutwardEdge, hleft] using (h i).1
  · simpa [vectorOutwardEdge, hleft] using (h i).2.1

/-- The actual outward column and final normalization are accurate at any
coordinate whose exact score meets the source's selection threshold. The
cached-column equality allows the algorithm to compute the outward path
once, while the perturbation and path estimates use its coordinatewise
description. -/
theorem roundedVectorAccuracy_of_selectedScore
    {n p q : ℕ} (hn : 2 ≤ n) (hp : 2 ≤ p) (hq : 2 ≤ q)
    (a b : ℕ → ℝ) {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsSymm)
    (j r : Fin n) (v : EuclideanSpace ℝ (Fin n)) (hv : ‖v‖ = 1)
    (heig : A *ᵥ v.ofLp = (MatrixResolvent.isHermitian_map_ofReal hA).eigenvalues j • v.ofLp)
    {shift η Δ : ℝ} (hη : 0 < η) (hηmax : η ≤ 1 / 2) (hηnative : Native q hq η)
    (hΔ : 0 < Δ) (hguard : (n : ℝ) * unitRoundoff p ≤ 1 / 128)
    (hηprec : η ≤ Δ * Real.sqrt (unitRoundoff p) / (16 * Real.sqrt (Real.sqrt (n : ℝ))))
    (hnear : |shift - (MatrixResolvent.isHermitian_map_ofReal hA).eigenvalues j| ≤ η)
    (hgap : ∀ i ≠ j, Δ ≤ |(MatrixResolvent.isHermitian_map_ofReal hA).eigenvalues i -
      (MatrixResolvent.isHermitian_map_ofReal hA).eigenvalues j|)
    (hωη : unitRoundoff q ≤ η / 4096)
    (hωΔ : unitRoundoff q ≤ unitRoundoff p * Δ / 8192)
    (hωn : unitRoundoff q ≤ unitRoundoff p / (65536 * (n : ℝ)))
    (ha : ∀ i < n, |a i| ≤ 5) (hb : ∀ i, i + 1 < n → |b i| ≤ 1)
    (hK : vectorShiftedMatrix n a b η = MatrixResolvent.imaginaryShift (A.map Complex.ofReal) shift η)
    (hselected : (4 * (n : ℝ) * η)⁻¹ ≤ ((vectorShiftedMatrix n a b η)⁻¹ r r).im)
    (x : Fin n → Word q hq)
    (hcache : ∀ i, (x i).value = (vectorRoundedInverseColumn q hq n a b η r i).im) :
    vectorPivotDivisorsPositive n q hq a b η ∧
      ∃ hx : Word.euclidean x ≠ 0,
        0 < (Word.roundedNorm x).value ∧
          ∃ σ : ℝ, (σ = -1 ∨ σ = 1) ∧
            ‖Word.euclidean (Word.normalizeTo p hp x hx) - σ • v‖ < 9 * unitRoundoff p / 4 ∧
            ‖Word.euclidean (Word.normalizeTo p hp x hx) - σ • v‖ ≤ 4 * unitRoundoff p := by
  have hn1 : 1 ≤ (n : ℝ) := by exact_mod_cast (show 1 ≤ n by omega)
  have hn0 : 0 < (n : ℝ) := zero_lt_one.trans_le hn1
  have hu := unitRoundoff_pos p
  have hu128 : unitRoundoff p ≤ 1 / 128 :=
    (le_mul_of_one_le_left hu.le hn1).trans hguard
  have hω128 : unitRoundoff q ≤ 1 / 128 := by linarith
  have hnω : (n : ℝ) * unitRoundoff q ≤ unitRoundoff p / 65536 := by
    have h := (le_div_iff₀ (by positivity : 0 < 65536 * (n : ℝ))).mp hωn
    linarith
  have hnω128 : (n : ℝ) * unitRoundoff q ≤ 1 / 128 := by linarith
  obtain ⟨hpivots, htwists⟩ :=
    roundedVectorStructuredBackward n q hn hq a b η hω128 hη hηmax hηnative ha hb
  have hdivisors : vectorPivotDivisorsPositive n q hq a b η := by
    intro i
    exact ⟨(hpivots i).2.2.1, (hpivots i).2.2.2, (htwists i).2.1⟩
  obtain ⟨htwist, _, E, β, hEsymm, _, hfactor, _, _, hEω, hedge, hperturb⟩ := htwists r
  have hEη : ‖E‖ ≤ η / 64 := by linarith
  have hselect : (4 * (n : ℝ) * η)⁻¹ ≤
      ((MatrixResolvent.imaginaryShift (A.map Complex.ofReal) shift η)⁻¹ r r).im :=
    hK ▸ hselected
  obtain ⟨_, _, hw, hy, _, σ, hσ, _, hdirection⟩ :=
    exactResolventPerturbedDirection (E := E) hA j r v hv heig hη hΔ hu hguard hηprec
      hnear hgap hEη hEω hωΔ hselect
  let y : EuclideanSpace ℝ (Fin n) :=
    toLp 2 (Complex.im ∘ (vectorShiftedMatrix n a b η + E)⁻¹.col r)
  have hyne : y ≠ 0 := norm_pos_iff.mp (by simpa only [y, hK] using hy)
  have hpath := vectorRoundedInverseColumn_bounds q hq n hn a b η r hη hu128 hnω128 hnω
    (fun i => ⟨(hpivots i).1.2.1, (hpivots i).2.1.2.1⟩)
    htwist E β hEsymm hfactor hedge hperturb
  have hpathImag := hpath.2.2 (by simpa only [hK, Matrix.col_apply] using hw.le)
  have hxValues : Word.euclidean x =
      toLp 2 (Complex.im ∘ vectorRoundedInverseColumn q hq n a b η r) := by
    ext i
    exact hcache i
  have hpathWords : ‖Word.euclidean x - y‖ ≤ (3 * unitRoundoff p / 1024) * ‖y‖ := by
    rw [hxValues]
    exact hpathImag.1
  have hx := roundedImaginaryVector_ne_zero x hyne hp hpathWords
  have hangle : ∃ σ : ℝ, (σ = -1 ∨ σ = 1) ∧
      ‖‖y‖⁻¹ • y - σ • v‖ < unitRoundoff p / 4 :=
    ⟨σ, hσ, by simpa only [y, hK] using hdirection⟩
  obtain ⟨s, hs, hstrict, hfinal⟩ :=
    roundedRealVector_direction hp x hyne hn hguard hnω
      hpathWords hangle
  exact ⟨hdivisors, hx, Word.roundedNorm_pos _ hx, s, hs, hstrict, hfinal.le⟩

end NumStability.CertifiedTridiagonalEigenpairs
