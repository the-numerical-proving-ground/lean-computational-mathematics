import ComputationalMathematics.Source.CertifiedTridiagonalEigenpairs.ReturnedErrorsTarget
import ComputationalMathematics.Source.CertifiedTridiagonalEigenpairs.AcceptedOutput.ExecutionProof

/-! The returned errors of the actual unified execution. -/

namespace NumStability.CertifiedTridiagonalEigenpairs

open Matrix WithLp NoisyRankCertificate FloatingPointFormat.UnboundedBinary
open scoped Matrix.Norms.L2Operator RealInnerProductSpace

variable {n p : ℕ} {J : Finset ℕ} {hp : 2 ≤ p}

private theorem orthonormal_column_matrix
    (V : Fin J.card → EuclideanSpace ℝ (Fin (n + 1))) (hV : Orthonormal ℝ V) :
    let A : Matrix (Fin (n + 1)) (Fin J.card) ℝ := .of fun i j => V j i
    Aᵀ * A = 1 := by
  intro A
  ext i j
  calc
    _ = (V j).ofLp ⬝ᵥ star (V i).ofLp := by
      rw [star_trivial, dotProduct_comm]
      rfl
    _ = inner ℝ (V i) (V j) := (EuclideanSpace.inner_eq_star_dotProduct (V i) (V j)).symm
    _ = if i = j then 1 else 0 := (orthonormal_iff_ite.mp hV) i j
    _ = _ := Matrix.one_apply.symm

private theorem norm_le_one_of_gram
    (U : Matrix (Fin (n + 1)) (Fin J.card) ℝ) (hU : Uᵀ * U = 1) : ‖U‖ ≤ 1 := by
  have h := l2_opNorm_conjTranspose_mul_self U
  rw [conjTranspose_eq_transpose_of_trivial, hU] at h
  have hId : ‖(1 : Matrix (Fin J.card) (Fin J.card) ℝ)‖ ≤ 1 := by
    rw [← diagonal_one, l2_opNorm_diagonal]
    exact (pi_norm_le_iff_of_nonneg (by norm_num)).2 fun _ => by simp
  nlinarith [norm_nonneg U]

set_option maxHeartbeats 1200000 in
/-- The nontrivial branch's intermediate errors use its actual stored output
and signed exact columns from the same accepted matrix. -/
theorem normalizedEigenpairRun_errorBounds
    {a : Fin (n + 1) → Word p hp} {b : Fin n → Word p hp}
    {bits : ℕ → GateBits n J} {hn : 2 ≤ n + 1} {guard : precisionGuard (n + 1) p}
    {hJ : J.Nonempty} {valid : J ⊆ Finset.Icc 1 (n + 1)}
    {out : NativeAcceptedEigenpairs n p J hp}
    (h : normalizedEigenpairRun a b bits hn guard hJ valid = some out) :
    TridiagonalAcceptedErrorBounds a b valid out := by
  let r := out.scaleExponent
  let R := (2 : ℝ) ^ r
  let T := storedTridiagonal a b
  let S := normalizedTridiagonal a b r
  let aW := fun i => normalizeTrialWord (n := n) (J := J) r (a i)
  let bW := fun i => normalizeTrialWord (n := n) (J := J) r (b i)
  let M := out.accepted.matrix bW
  let hM := out.accepted.matrix_isHermitian bW
  let I := requestedRankOrder valid
  let rank := (requestedRankArray J valid).get
  let θ := fun j => (runAcceptedRefinement out.accepted.trial bW (rank j)).value
  let μ := fun j => roundToEven p hp (θ j)
  let D := Matrix.diagonal μ
  let Q := out.columns
  let u := unitRoundoff p
  let rootk := Real.sqrt (J.card : ℝ)
  let ℓ := ascendingEigenvalue hM
  obtain ⟨hr, htrial⟩ := normalizedEigenpairRun_retry_some h
  obtain ⟨ha, hb⟩ := normalizedTrialInput_bounds (J := J) a b hr
  have hFacts (j : Fin J.card) := runAcceptedRefinement_facts aW bW bits out.accepted hp hn
    guard hJ valid ha hb htrial (rank j)
  have hk : 0 < J.card := Finset.card_pos.mpr hJ
  let j₀ : Fin J.card := ⟨0, hk⟩
  have hClose : ‖M - S‖ ≤ u / 128 := by
    have hNormEq : S = sturmTridiagonal (fun i => (aW i).value) (fun i => (bW i).value) :=
      (normalizedTrialMatrix_eq (J := J) a b r).symm
    rw [hNormEq]
    exact (hFacts j₀).1
  have hNormM : ‖M‖ < 1 := (hFacts j₀).2.1
  have hVec (j : Fin J.card) :
      ∃ v : EuclideanSpace ℝ (Fin (n + 1)),
        (‖v‖ = 1 ∧ M.toEuclideanLin v = ℓ (I j) • v) ∧
        ‖toLp 2 (Q.col j) - v‖ ≤ 4 * u := by
    obtain ⟨_, _, _, _, v, hv, herr⟩ := normalizedEigenpairRun_column h j
    exact ⟨v, hv, herr⟩
  choose V hEig hColumn using hVec
  have hSimple (j : Fin J.card) (i : Fin (n + 1)) (hi : i ≠ I j) :
      ℓ i ≠ ℓ (I j) := by
    have hgap := (hFacts j).2.2.1 i hi
    have hΔ : 0 < certifiedGap (n + 1) J.card p := by
      rw [certifiedGap_eq_roundoff]
      exact unitRoundoff_pos _
    intro he
    change certifiedGap (n + 1) J.card p < |ℓ i - ℓ (I j)| at hgap
    rw [he, sub_self, abs_zero] at hgap
    exact (not_lt_of_ge hΔ.le) hgap
  obtain ⟨basis, _, hbasis⟩ := exists_ascendingEigenbasis_preserving_selected hM I
    I.injective V hSimple hEig
  have hV : Orthonormal ℝ V := by
    have heq : (fun j => basis (I j)) = V := funext hbasis
    rw [← heq]
    exact basis.orthonormal.comp I I.injective
  let U : Matrix (Fin (n + 1)) (Fin J.card) ℝ := .of fun i j => V j i
  have hUGram : Uᵀ * U = 1 := orthonormal_column_matrix V hV
  have hUEig : M * U = U * diagonal (fun j => ℓ (I j)) := by
    ext i j
    rw [Matrix.mul_diagonal]
    have he := congrArg (fun v : EuclideanSpace ℝ (Fin (n + 1)) => v i) (hEig j).2
    simpa [U, Matrix.mul_apply, Matrix.toLpLin_apply, Matrix.mulVec, dotProduct,
      PiLp.smul_apply, smul_eq_mul, mul_comm] using he
  have hCols (j : Fin J.card) : ‖toLp 2 (Q.col j) - toLp 2 (U.col j)‖ ≤ 4 * u := hColumn j
  have hη : finalLabelTolerance (n + 1) J.card p = vectorTolerance (n + 1) J.card p := by
    rw [vectorTolerance_eq_roundoff]
    rfl
  have hθ (j : Fin J.card) :
      |θ j - ℓ (I j)| ≤ finalLabelTolerance (n + 1) J.card p := by
    rw [hη]
    exact (hFacts j).2.2.2.1
  obtain ⟨hR, hScale, hScaleBound, _⟩ := normalization_for_returned_errors a b hr
  change 0 < R at hR
  change T = R • S at hScale
  change R < 8 * ‖T‖ at hScaleBound
  obtain ⟨⟨hEop, hEfrob⟩, _, _, hμM, hResM, hResS, _, _, hμS⟩ :=
    returnedEigenpairErrors hp hn hk
      (by simpa only [Fintype.card_fin] using Fintype.card_le_of_injective I I.injective)
      I T S M (sturmTridiagonal_isHermitian _ _) (sturmTridiagonal_isHermitian _ _) hM
      R hR hScale hScaleBound U Q θ guard hClose hNormM hUGram hUEig hθ hCols
  have hE : Q = U + (Q - U) := by abel
  have hQnorm : ‖Q‖ ≤ 1 + 4 * rootk * u := by
    calc
      _ = ‖U + (Q - U)‖ := congrArg norm hE
      _ ≤ ‖U‖ + ‖Q - U‖ := norm_add_le _ _
      _ ≤ _ := add_le_add (norm_le_one_of_gram U hUGram) (hEop.trans hEfrob)
  have hD : diagonal out.labels = R • D := by
    unfold D
    rw [← diagonal_smul]
    congr 1
    funext j
    have hLabel := (normalizedEigenpairRun_column h j).1
    change (out.pairs[j.val].label).value = R * μ j
    rw [hLabel]
    exact rescaledLabel_value p hp r (θ j)
  have hStrict : ‖T * Q - Q * diagonal out.labels‖ < 120 * rootk * u * ‖T‖ := by
    calc
      _ = R * ‖S * Q - Q * D‖ := by
        rw [hD, hScale, Matrix.smul_mul, Matrix.mul_smul, ← smul_sub, norm_smul,
          Real.norm_eq_abs, abs_of_pos hR]
      _ < R * (15 * rootk * u) := mul_lt_mul_of_pos_left hResS hR
      _ ≤ (8 * ‖T‖) * (15 * rootk * u) :=
        mul_le_mul_of_nonneg_right hScaleBound.le (mul_nonneg (mul_nonneg (by norm_num) (Real.sqrt_nonneg _)) (unitRoundoff_pos p).le)
      _ = _ := by ring
  refine ⟨U, hUGram, hUEig, hE, hCols, hEop, hEfrob, hQnorm, ?_, hResM, hResS, hD, hStrict, ?_⟩
  · intro j
    simpa only [hη] using hμM j
  · intro j
    exact ⟨by simpa only [hη] using (hμS j).1, (hμS j).2.1⟩

theorem tridiagonalReturnedErrors : SourceTargets.tridiagonalReturnedErrors := by
  intro n p J hp a b bits guard hJ valid out h
  obtain ⟨hvalues, hres, hgram, hpairs, hcols, _⟩ :=
    runTridiagonalEigenpairs_accuracy a b bits guard hJ valid out h
  refine ⟨⟨hvalues, hres, hgram, hpairs, hcols⟩, ?_⟩
  cases out with
  | exact out words => trivial
  | refined out =>
    obtain ⟨_, _, hrun⟩ := runTridiagonalEigenpairs_refined_some h
    exact normalizedEigenpairRun_errorBounds hrun

end NumStability.CertifiedTridiagonalEigenpairs
