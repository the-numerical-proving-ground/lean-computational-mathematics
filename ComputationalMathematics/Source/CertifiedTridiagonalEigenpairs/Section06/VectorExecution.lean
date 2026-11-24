import ComputationalMathematics.Analysis.FloatingPointArithmetic.UnboundedBinary.VectorNormalizationScan
import ComputationalMathematics.Source.CertifiedTridiagonalEigenpairs.Section06.Accuracy
import ComputationalMathematics.Source.CertifiedTridiagonalEigenpairs.Section06.CachedExecution

/-! # Deterministic Section 6 vector computation -/

open Matrix WithLp
open scoped Matrix.Norms.L2Operator

namespace NumStability.CertifiedTridiagonalEigenpairs

open FloatingPointFormat.UnboundedBinary

/-- Run both directional sweeps, scan the twisted scores, propagate once
from the selected coordinate, and expose the stored imaginary components. -/
noncomputable def vectorComputedImaginaryArray {n q : ℕ} (hq : 2 ≤ q) (hn : 0 < n)
    (A : Matrix (Fin n) (Fin n) ℝ) (shift η : ℝ) : Vector (Word q hq) n :=
  let a := vectorInputDiagonal A shift
  let b := vectorInputEdge A
  let run := vectorCachedExecution q hq n hn a b η
  let imag := vectorImaginaryWords hq (fun i => run.column.get i) (by
    intro i
    change Native q hq ((vectorCachedExecution q hq n hn a b η).column.get i).im
    rw [vectorCachedExecution_column_get]
    exact vectorRoundedInverseColumn_im_native q hq n a b η run.root i)
  Vector.ofFn imag

/-- The represented imaginary components read in row order. -/
noncomputable def vectorComputedImaginary {n q : ℕ} (hq : 2 ≤ q) (hn : 0 < n)
    (A : Matrix (Fin n) (Fin n) ℝ) (shift η : ℝ) : Fin n → Word q hq :=
  (vectorComputedImaginaryArray hq hn A shift η).get

/-- The real vector returned by the Section 6 computation at precision p. -/
noncomputable def vectorComputedOutput {n p q : ℕ} (hp : 2 ≤ p) (hq : 2 ≤ q) (hn : 0 < n)
    (A : Matrix (Fin n) (Fin n) ℝ) (shift η : ℝ)
    (hx : Word.euclidean (vectorComputedImaginary hq hn A shift η) ≠ 0) :
    Fin n → Word p hp :=
  (Word.normalizeToScan p hp (vectorComputedImaginaryArray hq hn A shift η) hx).get

theorem vectorComputedOutput_eq_normalize {n p q : ℕ} (hp : 2 ≤ p) (hq : 2 ≤ q) (hn : 0 < n)
    (A : Matrix (Fin n) (Fin n) ℝ) (shift η : ℝ)
    (hx : Word.euclidean (vectorComputedImaginary hq hn A shift η) ≠ 0) :
    vectorComputedOutput hp hq hn A shift η hx =
      Word.normalizeTo p hp (vectorComputedImaginary hq hn A shift η) hx :=
  Word.normalizeToScan_get hp _ hx

/-- The Section 6 run has positive divisors and returns a real p-bit vector
within 4u of a signed unit eigenvector. -/
theorem roundedTridiagonalVectorAccuracy
    {n p q : ℕ} (hn : 2 ≤ n) (hp : 2 ≤ p) (hq : 2 ≤ q)
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsSymm) (hAnorm : ‖A‖ ≤ 2)
    (hband : ∀ i j : Fin n, i.val + 1 < j.val ∨ j.val + 1 < i.val → A i j = 0)
    (hb : ∀ i j : Fin n, i.val + 1 = j.val → |A i j| ≤ 1)
    (hNativeA : ∀ i j : Fin n, Native q hq (A i j))
    (j : Fin n) (v : EuclideanSpace ℝ (Fin n)) (hv : ‖v‖ = 1)
    (heig : A *ᵥ v.ofLp = (MatrixResolvent.isHermitian_map_ofReal hA).eigenvalues j • v.ofLp)
    {shift η Δ : ℝ} (hNativeShift : Native q hq shift)
    (hηpow : ∃ m : ℤ, η = (2 : ℝ) ^ m) (hηmax : η ≤ 1 / 2)
    (hΔ : 0 < Δ) (hguard : (n : ℝ) * unitRoundoff p ≤ 1 / 128)
    (hηprec : η ≤ Δ * Real.sqrt (unitRoundoff p) / (16 * (n : ℝ) ^ (1 / 4 : ℝ)))
    (hnear : |shift - (MatrixResolvent.isHermitian_map_ofReal hA).eigenvalues j| ≤ η)
    (hgap : ∀ i ≠ j, Δ ≤ |(MatrixResolvent.isHermitian_map_ofReal hA).eigenvalues i -
      (MatrixResolvent.isHermitian_map_ofReal hA).eigenvalues j|)
    (hωη : unitRoundoff q ≤ η / 4096)
    (hωΔ : unitRoundoff q ≤ unitRoundoff p * Δ / 8192)
    (hωn : unitRoundoff q ≤ unitRoundoff p / (65536 * (n : ℝ))) :
    vectorPivotDivisorsPositive n q hq (vectorInputDiagonal A shift) (vectorInputEdge A) η ∧
      ∃ hx : Word.euclidean (vectorComputedImaginary hq (by omega) A shift η) ≠ 0,
        0 < (Word.roundedNormScan (vectorComputedImaginaryArray hq (by omega) A shift η)).value ∧
          ∃ σ : ℝ, (σ = -1 ∨ σ = 1) ∧
            ‖Word.euclidean (vectorComputedOutput hp hq (by omega) A shift η hx) - σ • v‖ <
              9 * unitRoundoff p / 4 ∧
            ‖Word.euclidean (vectorComputedOutput hp hq (by omega) A shift η hx) - σ • v‖ ≤
              4 * unitRoundoff p := by
  have hn' : 0 < n := by omega
  let a := vectorInputDiagonal A shift
  let b := vectorInputEdge A
  let run := vectorCachedExecution q hq n hn' a b η
  let x := vectorComputedImaginary hq hn' A shift η
  have hx (i : Fin n) :
      (x i).value = (vectorRoundedInverseColumn q hq n a b η run.root i).im := by
    change ((vectorComputedImaginaryArray hq hn' A shift η)[i.val]).value = _
    rw [vectorComputedImaginaryArray, Vector.getElem_ofFn]
    simp only [vectorImaginaryWords_value, vectorCachedExecution_column_get, run, a, b]
  obtain ⟨hdivs, hnonzero, hnorm, σ, hσ, hstrict, hle⟩ :=
    roundedTridiagonalVectorAccuracy_of_cache hn hp hq A hA hAnorm hband hb hNativeA
      j v hv heig hNativeShift hηpow hηmax hΔ hguard hηprec hnear hgap hωη hωΔ hωn
      run.root (vectorCachedExecution_root q hq n hn' a b η) x hx
  refine ⟨hdivs, hnonzero, ?_, σ, hσ, ?_, ?_⟩
  · exact (Word.roundedNormScan_eq _).symm ▸ hnorm
  · rwa [vectorComputedOutput_eq_normalize]
  · rwa [vectorComputedOutput_eq_normalize]

end NumStability.CertifiedTridiagonalEigenpairs
