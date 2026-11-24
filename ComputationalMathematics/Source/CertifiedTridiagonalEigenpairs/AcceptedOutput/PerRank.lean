import ComputationalMathematics.Analysis.Eigenvalues.TridiagonalRefinementExecution
import ComputationalMathematics.Source.CertifiedTridiagonalEigenpairs.AcceptedLabels.Proof
import ComputationalMathematics.Source.CertifiedTridiagonalEigenpairs.AcceptedOutput.ComplexRanks
import ComputationalMathematics.Source.CertifiedTridiagonalEigenpairs.Retry.Execution
import ComputationalMathematics.Source.CertifiedTridiagonalEigenpairs.Section06.VectorExecution

/-! Bind the accepted trial and working precision to both numerical kernels. -/

namespace NumStability.CertifiedTridiagonalEigenpairs

open Matrix WithLp NoisyRankCertificate FloatingPointFormat.UnboundedBinary
open scoped Matrix.Norms.L2Operator

noncomputable section

variable {n p : ℕ} {J : Finset ℕ}

/-- The finer label used by the native return loop, computed without a trace. -/
def runAcceptedRefinement (trial : AcceptedTrial n J p) (b : Fin n → TrialWord n J p)
    (j : RequestedTrialRank n J) : TrialWord n J p :=
  runTridiagonalRefinement (vectorToleranceExponent (n + 1) J.card p + 1) j.val
    (fun i => trial.val.diagonal[i.val]) b

theorem runAcceptedRefinement_eq (trial : AcceptedTrial n J p)
    (b : Fin n → TrialWord n J p) (j : RequestedTrialRank n J) :
    runAcceptedRefinement trial b j = acceptedRefinedLabel trial b j :=
  runTridiagonalRefinement_eq _ _ _ _

/-- The dyadic imaginary shift is formed by shifting the exponent of one. -/
def acceptedShiftWord (n p : ℕ) (J : Finset ℕ) : TrialWord n J p :=
  (Word.round _ _ 1).scale (-(vectorToleranceExponent (n + 1) J.card p : ℤ))

theorem acceptedShiftWord_value :
    (acceptedShiftWord n p J).value = vectorTolerance (n + 1) J.card p := by
  rw [acceptedShiftWord, Word.value_scale, Word.value_round,
    roundToEven_eq_self_of_native (native_one _ _), mul_one, vectorTolerance_eq_roundoff]
  rfl

/-- The Hermitian certificate refers to the same stored bands read by the
Section 6 computation. -/
theorem RetryResult.matrix_isHermitian (trial : RetryResult n J p)
    (b : Fin n → TrialWord n J p) : (trial.matrix b).IsHermitian :=
  sturmTridiagonal_isHermitian _ _

/-- The matrix certified by the accepted trial and the native fine label
supply the numerical facts needed after acceptance. -/
theorem runAcceptedRefinement_facts
    (a : Fin (n + 1) → TrialWord n J p) (b : Fin n → TrialWord n J p)
    (bits : ℕ → GateBits n J) (trial : RetryResult n J p) (hp : 2 ≤ p)
    (hn : 2 ≤ n + 1) (hguard : precisionGuard (n + 1) p)
    (hJ : J.Nonempty) (hJvalid : J ⊆ Finset.Icc 1 (n + 1))
    (ha : ∀ i, |(a i).value| ≤ 1 / 4) (hb : ∀ i, |(b i).value| ≤ 1 / 4)
    (htrial : retryRun a b bits = some trial) (j : RequestedTrialRank n J) :
    let M := trial.matrix b
    let S := sturmTridiagonal (fun i => (a i).value) (fun e => (b e).value)
    let spectrum := ascendingEigenvalue (trial.matrix_isHermitian b)
    let θ := (runAcceptedRefinement trial.trial b j).value
    ‖M - S‖ ≤ unitRoundoff p / 128 ∧ ‖M‖ < 1 ∧
    (∀ i ≠ j.val, certifiedGap (n + 1) J.card p < |spectrum i - spectrum j.val|) ∧
    |θ - spectrum j.val| ≤ vectorTolerance (n + 1) J.card p ∧
    |roundToEven p hp θ - spectrum j.val| < 2 * unitRoundoff p := by
  have haccept := retryRun_accepts htrial
  have heq : trial.trial = (⟨trialRun n p J a b (bits trial.index), haccept⟩ : AcceptedTrial n J p) :=
    Subtype.ext (retryRun_first htrial).1
  have h := acceptedIndexedLabels n p J hp a b hn hguard hJ hJvalid ha hb
    (bits trial.index) haccept j 0
  dsimp only at h
  obtain ⟨_, hclose, hnorm, _, hgap, _, _, _, _, _, _, _, _, _, _, _, _, _, hlabel,
    _, _, _, _, hrounded, _, _, _, _, _⟩ := h
  dsimp only
  rw [runAcceptedRefinement_eq]
  change realMatrixOperatorNorm (trial.matrix b - _) ≤ _ ∧
    realMatrixOperatorNorm (trial.matrix b) < 1 ∧ _ ∧ _ ∧ _
  simpa only [RetryResult.matrix, heq] using
    (And.intro hclose (And.intro hnorm (And.intro hgap (And.intro hlabel.le hrounded))))

private theorem adjacent_indices {i j : Fin (n + 1)} (h : i.val + 1 = j.val) :
    ∃ e : Fin n, e.castSucc = i ∧ e.succ = j := by
  let e : Fin n := ⟨i.val, by have := j.isLt; omega⟩
  exact ⟨e, Fin.ext rfl, Fin.ext h⟩

private theorem accepted_matrix_native (trial : RetryResult n J p)
    (b : Fin n → TrialWord n J p) (i j : Fin (n + 1)) :
    Native (workingPrecision (n + 1) J.card p) (workingPrecision_ge_two _ _ _)
      (trial.matrix b i j) := by
  unfold RetryResult.matrix
  by_cases heq : i = j
  · subst j
    rw [sturmTridiagonal_diagonal]
    exact Word.native_value _
  by_cases ha : i.val + 1 = j.val
  · obtain ⟨e, rfl, rfl⟩ := adjacent_indices ha
    rw [sturmTridiagonal_upper]
    exact Word.native_value _
  by_cases hb : j.val + 1 = i.val
  · obtain ⟨e, rfl, rfl⟩ := adjacent_indices hb
    rw [sturmTridiagonal_lower]
    exact Word.native_value _
  rw [sturmTridiagonal_support _ _ _ _ heq ha hb]
  exact Or.inl rfl

/-- The actual output kernel on the accepted matrix has a positive computed
normalization divisor and a column close to a signed exact eigenvector. -/
theorem runAcceptedVector_accuracy
    (a : Fin (n + 1) → TrialWord n J p) (b : Fin n → TrialWord n J p)
    (bits : ℕ → GateBits n J) (trial : RetryResult n J p) (hp : 2 ≤ p)
    (hn : 2 ≤ n + 1) (hguard : precisionGuard (n + 1) p)
    (hJ : J.Nonempty) (hJvalid : J ⊆ Finset.Icc 1 (n + 1))
    (ha : ∀ i, |(a i).value| ≤ 1 / 4) (hb : ∀ i, |(b i).value| ≤ 1 / 4)
    (htrial : retryRun a b bits = some trial) (j : RequestedTrialRank n J) :
    let hq := workingPrecision_ge_two (n + 1) J.card p
    let hpos : 0 < n + 1 := Nat.succ_pos _
    let M := trial.matrix b
    let θ := (runAcceptedRefinement trial.trial b j).value
    let η := (acceptedShiftWord n p J).value
    ∃ hx : Word.euclidean (vectorComputedImaginary hq hpos M θ η) ≠ 0,
      0 < (Word.roundedNormScan (vectorComputedImaginaryArray hq hpos M θ η)).value ∧
      ∃ v : EuclideanSpace ℝ (Fin (n + 1)),
        ‖v‖ = 1 ∧ M.toEuclideanLin v =
          ascendingEigenvalue (trial.matrix_isHermitian b) j.val • v ∧
        ‖Word.euclidean (vectorComputedOutput hp hq hpos M θ η hx) - v‖ ≤
          4 * unitRoundoff p := by
  let M := trial.matrix b
  let hM := trial.matrix_isHermitian b
  have hMs : M.IsSymm := by
    change Mᵀ = M
    rw [← Matrix.conjTranspose_eq_transpose_of_trivial]
    exact hM
  let q := workingPrecision (n + 1) J.card p
  let hq := workingPrecision_ge_two (n + 1) J.card p
  let θ := (runAcceptedRefinement trial.trial b j).value
  let η := vectorTolerance (n + 1) J.card p
  let Δ := certifiedGap (n + 1) J.card p
  let e := sectionSixRank (n + 1)
  let v := hermitianOrderedEigenbasis hM j.val.rev
  obtain ⟨_, hnorm, hgap, hnear, _⟩ :=
    runAcceptedRefinement_facts a b bits trial hp hn hguard hJ hJvalid ha hb htrial j
  have hnorm' : ‖M‖ ≤ 2 := hnorm.le.trans (by norm_num)
  have hband (i l : Fin (n + 1)) (h : i.val + 1 < l.val ∨ l.val + 1 < i.val) :
      M i l = 0 := by
    have hne : i ≠ l := by intro hl; subst l; omega
    exact sturmTridiagonal_support _ _ _ _ hne (by omega) (by omega)
  have hedge (i l : Fin (n + 1)) (h : i.val + 1 = l.val) : |M i l| ≤ 1 := by
    obtain ⟨f, rfl, rfl⟩ := adjacent_indices h
    change |sturmTridiagonal _ _ f.castSucc f.succ| ≤ 1
    rw [sturmTridiagonal_upper]
    exact (hb f).trans (by norm_num)
  have hηpow : ∃ m : ℤ, η = (2 : ℝ) ^ m := by
    refine ⟨-(vectorToleranceExponent (n + 1) J.card p : ℤ), ?_⟩
    exact vectorTolerance_eq_roundoff _ _ _
  have hΔ : 0 < Δ := by
    dsimp [Δ]
    rw [certifiedGap_eq_roundoff]
    exact unitRoundoff_pos _
  have hηmax : η ≤ 1 / 2 := (vectorTolerance_lt_half _ _ _).le
  have hηprec := vectorTolerance_le_root_scale (n := n + 1) (Nat.succ_pos n) J.card p
  have heigenvalue := sectionSixRank_eigenvalue hM hMs j.val
  have hEig : M.toEuclideanLin v = ascendingEigenvalue hM j.val • v :=
    hermitianOrderedEigenbasis_apply hM j.val.rev
  have hEig' : M *ᵥ v.ofLp =
      (MatrixResolvent.isHermitian_map_ofReal hMs).eigenvalues (e j.val) • v.ofLp := by
    rw [show (MatrixResolvent.isHermitian_map_ofReal hMs).eigenvalues (e j.val) =
      ascendingEigenvalue hM j.val from heigenvalue]
    simpa [Matrix.toLpLin_apply] using congrArg WithLp.ofLp hEig
  have hnear' : |θ - (MatrixResolvent.isHermitian_map_ofReal hMs).eigenvalues (e j.val)| ≤ η := by
    rw [show (MatrixResolvent.isHermitian_map_ofReal hMs).eigenvalues (e j.val) =
      ascendingEigenvalue hM j.val from heigenvalue]
    exact hnear
  have hgap' (i : Fin (n + 1)) (hi : i ≠ e j.val) :
      Δ ≤ |(MatrixResolvent.isHermitian_map_ofReal hMs).eigenvalues i -
        (MatrixResolvent.isHermitian_map_ofReal hMs).eigenvalues (e j.val)| := by
    rw [show (MatrixResolvent.isHermitian_map_ofReal hMs).eigenvalues (e j.val) =
      ascendingEigenvalue hM j.val from heigenvalue]
    have heq := sectionSixRank_eigenvalue hM hMs (e.symm i)
    change (MatrixResolvent.isHermitian_map_ofReal hMs).eigenvalues (e (e.symm i)) =
      ascendingEigenvalue hM (e.symm i) at heq
    rw [e.apply_symm_apply] at heq
    rw [heq]
    apply (hgap (e.symm i) ?_).le
    intro h
    exact hi (e.symm_apply_eq.mp h)
  obtain ⟨hωη, hωeq, hωdim⟩ := acceptedPrecisionBudget (k := J.card) hn hguard
  have hωn : unitRoundoff q ≤ unitRoundoff p / (65536 * ((n + 1 : ℕ) : ℝ)) := by
    apply (le_div_iff₀ (by positivity)).2
    calc
      _ = (((n + 1 : ℕ) : ℝ) * workingRoundoff (n + 1) J.card p) * 65536 := by
        change unitRoundoff q * (65536 * ((n + 1 : ℕ) : ℝ)) =
          (((n + 1 : ℕ) : ℝ) * unitRoundoff q) * 65536
        ring
      _ ≤ (unitRoundoff p / 65536) * 65536 := mul_le_mul_of_nonneg_right hωdim (by norm_num)
      _ = _ := by ring
  obtain ⟨_, hx, hDivisor, σ, hσ, _, herror⟩ :=
    roundedTridiagonalVectorAccuracy hn hp hq M hMs hnorm' hband hedge
      (accepted_matrix_native trial b) (e j.val) v (norm_hermitianOrderedEigenbasis hM j.val.rev)
      hEig' (Word.native_value (runAcceptedRefinement trial.trial b j))
      hηpow hηmax hΔ hguard hηprec hnear' hgap' hωη hωeq.le hωn
  dsimp only
  rw [acceptedShiftWord_value]
  refine ⟨hx, hDivisor, σ • v, ?_, ?_, herror⟩
  · rw [norm_smul, norm_hermitianOrderedEigenbasis, mul_one]
    rcases hσ with rfl | rfl <;> norm_num
  · rw [map_smul, hEig, smul_comm]

end

end NumStability.CertifiedTridiagonalEigenpairs
