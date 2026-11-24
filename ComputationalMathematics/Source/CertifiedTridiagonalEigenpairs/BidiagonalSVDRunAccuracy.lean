import ComputationalMathematics.Source.CertifiedTridiagonalEigenpairs.BidiagonalSVDOracleWitness
import ComputationalMathematics.Source.CertifiedTridiagonalEigenpairs.BidiagonalSVDRun

/-!
# Stability of every returned selected bidiagonal SVD

The same accuracy statement applies to the exact output and to the p-bit
triplets returned after one prepared tridiagonal solve.
-/

namespace NumStability.CertifiedTridiagonalEigenpairs.BidiagonalSVDRequest

open FloatingPointFormat.UnboundedBinary MeasureTheory NormalizedGram
open scoped Matrix.Norms.L2Operator

variable {n k p : ℕ} {hp : 2 ≤ p}

/-- The source's value, vector, and common backward-error bounds, with both
vector families measured at their returned p-bit values. -/
structure RunAccuracy {m : ℕ} (B : Matrix (Fin m) (Fin m) ℝ)
    (I : Fin k → Fin m) (out : NativeSVDTriplets m k p hp) : Prop where
  nonnegative : ∀ j, 0 ≤ (out.labels j).value
  ordered : Monotone (fun j => (out.labels j).value)
  values : ∀ j, |(out.labels j).value - ascendingRealSpectrum B (I j)| ≤
    16 * unitRoundoff p * ‖B‖
  residuals : ∀ j,
    max (vecNorm2 (fun i => (B * out.rightMatrix -
      out.leftMatrix * Matrix.diagonal (fun j => (out.labels j).value)) i j))
      (vecNorm2 (fun i => (B.transpose * out.leftMatrix -
      out.rightMatrix * Matrix.diagonal (fun j => (out.labels j).value)) i j)) ≤
    160 * unitRoundoff p * ‖B‖
  pairs : ∀ j h, j ≠ h →
    max |(out.leftMatrix.transpose * out.leftMatrix) j h|
      |(out.rightMatrix.transpose * out.rightMatrix) j h| ≤ 6 * unitRoundoff p
  norms : ∀ j,
    max |columnNorm out.leftMatrix j - 1| |columnNorm out.rightMatrix j - 1| ≤
    2 * unitRoundoff p
  grams :
    max ‖out.leftMatrix.transpose * out.leftMatrix - 1‖
      ‖out.rightMatrix.transpose * out.rightMatrix - 1‖ ≤
    7 * Real.sqrt (k : ℝ) * unitRoundoff p
  common : HasIndexedSVDWitness B I out.leftMatrix out.rightMatrix
    (fun j => (out.labels j).value) (unitRoundoff p)

/-- The refined branch composes its deterministic returned-word estimates with
the common SVD witness for those same words. -/
theorem ReturnedTripletAccuracy.runAccuracy {m : ℕ}
    {B : Matrix (Fin m) (Fin m) ℝ} {I : Fin k → Fin m} {out : NativeSVDTriplets m k p hp}
    (h : ReturnedTripletAccuracy B I out) (hn : 2 ≤ m) (hk : 1 ≤ k) (hI : StrictMono I) :
    RunAccuracy B I out :=
  ⟨h.labels_nonnegative, h.labels_monotone, fun j => (h.value_error j).le,
    fun j => max_le (h.left_residual j) (h.right_residual j),
    fun j l hjl => max_le (h.left_pairs j l hjl) (h.right_pairs j l hjl),
    fun j => max_le (h.left_norm j) (h.right_norm j), max_le h.left_gram.le h.right_gram.le,
    h.hasIndexedSVDWitness hn hk hI⟩

private theorem columnNorm_eq_one_of_gram {m : ℕ}
    (X : Matrix (Fin m) (Fin k) ℝ) (hX : X.transpose * X = 1) (j : Fin k) :
    columnNorm X j = 1 := by
  have hs := gram_diag X j
  rw [hX, Matrix.one_apply_eq] at hs
  have hn : 0 ≤ columnNorm X j := norm_nonneg _
  nlinarith

/-- The exact branches satisfy the same source constants with zero matrix
perturbation and their exact selected columns. -/
theorem exactOutput_runAccuracy (upper : Bool)
    {a : Fin (n + 1) → Word p hp} {b : Fin n → Word p hp}
    {I : Fin k ↪o Fin (n + 1)} {out : BidiagonalExactOutput p hp n k}
    (hout : bidiagonalExactBranch a b I = some out) :
    RunAccuracy (storedBidiagonal upper a b) I (exactOutput out).triplets := by
  let B := storedBidiagonal upper a b
  let U := (exactOutput out).triplets.leftMatrix
  let V := (exactOutput out).triplets.rightMatrix
  let s := fun j : Fin k => ((exactOutput out).triplets.labels j).value
  let u := unitRoundoff p
  have hu : 0 ≤ u := (unitRoundoff_pos p).le
  obtain ⟨_, hvalues, hs₀, hs, hleft, hright, hU, hV, Uf, Vf, hUf, hVf, hB, hUcols, hVcols⟩ :=
    bidiagonalExactBranch_correct upper hout
  change (∀ j, s j = ascendingRealSpectrum B (I j)) at hvalues
  change B * V = U * Matrix.diagonal s at hleft
  change B.transpose * U = V * Matrix.diagonal s at hright
  change U.transpose * U = 1 at hU
  change V.transpose * V = 1 at hV
  have hUeq : U = Uf.submatrix id I := by
    ext i j
    exact hUcols i j
  have hVeq : V = Vf.submatrix id I := by
    ext i j
    exact hVcols i j
  have hbNorm : 0 ≤ ‖B‖ := norm_nonneg _
  have hVecZero : vecNorm2 (fun _ : Fin (n + 1) => (0 : ℝ)) = 0 := by
    simp [vecNorm2, vecNorm2Sq]
  refine ⟨hs₀, hs, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro j
    change |s j - ascendingRealSpectrum B (I j)| ≤ 16 * u * ‖B‖
    rw [hvalues j, sub_self, abs_zero]
    positivity
  · intro j
    change max (vecNorm2 (fun i => (B * V - U * Matrix.diagonal s) i j))
      (vecNorm2 (fun i => (B.transpose * U - V * Matrix.diagonal s) i j)) ≤
        160 * u * ‖B‖
    simp only [hleft, hright, sub_self, Matrix.zero_apply, hVecZero, max_self]
    positivity
  · intro j l hjl
    change max |(U.transpose * U) j l| |(V.transpose * V) j l| ≤ 6 * u
    simp only [hU, hV, Matrix.one_apply_ne hjl, abs_zero, max_self]
    positivity
  · intro j
    change max |columnNorm U j - 1| |columnNorm V j - 1| ≤ 2 * u
    simp only [columnNorm_eq_one_of_gram U hU j, columnNorm_eq_one_of_gram V hV j,
      sub_self, abs_zero, max_self]
    positivity
  · change max ‖U.transpose * U - 1‖ ‖V.transpose * V - 1‖ ≤ 7 * Real.sqrt (k : ℝ) * u
    simp only [hU, hV, sub_self, norm_zero, max_self]
    positivity
  · change HasIndexedSVDWitness B I U V s u
    obtain ⟨_, _, hd, hd₀, _⟩ := exists_orthonormalBases_ascendingRealSpectrum B
    refine ⟨Uf, Vf, 0, ascendingRealSpectrum B, hUf, mul_eq_one_comm.mp hUf, hVf,
      mul_eq_one_comm.mp hVf, hd, hd₀, fun j => (hvalues j).symm, ?_, ?_, ?_⟩
    · simpa only [add_zero] using hB
    · change ‖(0 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)‖ ≤ 1952 * (k : ℝ) * u * ‖B‖
      rw [norm_zero]
      positivity
    · rw [hUeq, hVeq, sub_self, sub_self]
      change max ‖(0 : Matrix (Fin (n + 1)) (Fin k) ℝ)‖
        ‖(0 : Matrix (Fin (n + 1)) (Fin k) ℝ)‖ ≤ 4 * Real.sqrt (k : ℝ) * u
      simp only [norm_zero, max_self]
      positivity

variable {upper : Bool} {a : Fin (n + 1) → Word p hp} {b : Fin n → Word p hp}
  {I : Fin k ↪o Fin (n + 1)}
  {cmp : EmptyBinScan.Comparison (svdLabelPrecision k p) (svdLabelPrecision_ge_two k p)}
  {hk : 1 ≤ k} {hguard : precisionGuard (n + 1) p}

/-- Deterministic accuracy for every returned output, regardless of its bit stream. -/
theorem RunPlan.accuracy (plan : RunPlan upper a b I cmp hk hguard) (bits : plan.Bits)
    (out : RunOutput n k p hp) (hrun : plan.run bits = some out) :
    RunAccuracy (storedBidiagonal upper a b) I out.triplets := by
  cases plan with
  | exact exactOut he =>
    change some (exactPackedOutput exactOut) = some out at hrun
    rw [exactPackedOutput_eq] at hrun
    obtain rfl := Option.some.inj hrun
    exact exactOutput_runAccuracy upper he
  | nontrivial hn call hprep hscale =>
    change (ℕ → GateBits (edgeCount n) call.oneBasedRanks) at bits
    simp only [RunPlan.run] at hrun
    split at hrun
    · contradiction
    · rename_i result hresult
      have hsolved := (call.solvePreparedParities_eq hn hprep bits).symm.trans hresult
      rw [TridiagonalCall.finishPacked_eq] at hrun
      obtain rfl := Option.some.inj hrun
      obtain ⟨r, hr⟩ := hscale
      obtain ⟨hL, hR, hAccuracy⟩ :=
        TridiagonalCall.prepared_solve_finish_accuracy hp upper a b I cmp hn hk hguard
          I.strictMono hr call hprep bits result hsolved
      exact hAccuracy.runAccuracy hn hk I.strictMono

/-- Correctness and almost-sure termination of the prepared top-level dispatch. -/
theorem prepareRun_correct (upper : Bool) (a : Fin (n + 1) → Word p hp)
    (b : Fin n → Word p hp) (I : Fin k ↪o Fin (n + 1))
    (cmp : EmptyBinScan.Comparison (svdLabelPrecision k p) (svdLabelPrecision_ge_two k p))
    (hk : 1 ≤ k) (hguard : precisionGuard (n + 1) p) :
    let plan := prepareRun upper a b I cmp hk hguard
    (∀ᵐ bits ∂plan.bitMeasure, ∃ out, plan.run bits = some out) ∧
    ∀ bits out, plan.run bits = some out →
      RunAccuracy (storedBidiagonal upper a b) I out.triplets := by
  dsimp only
  exact ⟨RunPlan.ae_returns _, RunPlan.accuracy _⟩

end NumStability.CertifiedTridiagonalEigenpairs.BidiagonalSVDRequest
