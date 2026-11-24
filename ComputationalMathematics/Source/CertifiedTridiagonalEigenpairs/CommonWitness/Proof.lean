import ComputationalMathematics.Analysis.Eigenvalues.SelectedEigenbasis
import ComputationalMathematics.Source.CertifiedTridiagonalEigenpairs.CommonWitness.Target

namespace NumStability.CertifiedTridiagonalEigenpairs

open NoisyRankCertificate OrderStatistics FloatingPointFormat.UnboundedBinary
open scoped BigOperators

private theorem basis_eigenvector_iff {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ)
    (b : OrthonormalBasis (Fin n) ℝ (EuclideanSpace ℝ (Fin n))) (d : Fin n → ℝ) :
    (∀ i, A.toEuclideanLin (b i) = d i • b i) ↔
      A * orthonormalBasisMatrix b = orthonormalBasisMatrix b * Matrix.diagonal d := by
  constructor
  · intro he
    ext i j
    rw [Matrix.mul_diagonal]
    have hj := congrArg (fun x : EuclideanSpace ℝ (Fin n) => x i) (he j)
    simpa only [Matrix.toLpLin_apply, Matrix.mulVec, dotProduct, PiLp.smul_apply,
      smul_eq_mul, orthonormalBasisMatrix, Matrix.mul_apply,
      mul_comm (d j)] using hj
  · intro he j
    apply PiLp.ext
    intro i
    have hj := congrArg (fun H : Matrix (Fin n) (Fin n) ℝ => H i j) he
    change (A * orthonormalBasisMatrix b) i j =
      (orthonormalBasisMatrix b * Matrix.diagonal d) i j at hj
    rw [Matrix.mul_diagonal] at hj
    simpa only [Matrix.toLpLin_apply, Matrix.mulVec, dotProduct, PiLp.smul_apply,
      smul_eq_mul, orthonormalBasisMatrix, Matrix.mul_apply,
      mul_comm (d j)] using hj

open scoped Matrix.Norms.L2Operator in
private theorem basis_diagonal_opNorm_le {n : ℕ}
    (b : OrthonormalBasis (Fin n) ℝ (EuclideanSpace ℝ (Fin n))) (d : Fin n → ℝ)
    {D : ℝ} (hD : 0 ≤ D) (hd : ∀ i, |d i| ≤ D) :
    realMatrixOperatorNorm
      (orthonormalBasisMatrix b * Matrix.diagonal d * (orthonormalBasisMatrix b).transpose) ≤ D := by
  let V := orthonormalBasisMatrix b
  change ‖V * Matrix.diagonal d * V.transpose‖ ≤ D
  have hOne : ‖(1 : Matrix (Fin n) (Fin n) ℝ)‖ ≤ 1 := by
    rw [← Matrix.diagonal_one, Matrix.l2_opNorm_diagonal]
    exact (pi_norm_le_iff_of_nonneg zero_le_one).2 (by simp)
  have hV : ‖V‖ ≤ 1 := by
    have h := Matrix.l2_opNorm_conjTranspose_mul_self V
    rw [Matrix.conjTranspose_eq_transpose_of_trivial,
      orthonormalBasisMatrix_transpose_mul_self] at h
    nlinarith [norm_nonneg V]
  have hVT : ‖V.transpose‖ ≤ 1 := by
    rwa [← Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.l2_opNorm_conjTranspose]
  calc
    _ ≤ ‖V * Matrix.diagonal d‖ * ‖V.transpose‖ := Matrix.l2_opNorm_mul _ _
    _ ≤ ‖V * Matrix.diagonal d‖ := mul_le_of_le_one_right (norm_nonneg _) hVT
    _ ≤ ‖V‖ * ‖Matrix.diagonal d‖ := Matrix.l2_opNorm_mul _ _
    _ ≤ ‖Matrix.diagonal d‖ := mul_le_of_le_one_left (norm_nonneg _) hV
    _ = ‖d‖ := Matrix.l2_opNorm_diagonal _
    _ ≤ D := (pi_norm_le_iff_of_nonneg hD).2 fun i => by
      simpa only [Real.norm_eq_abs] using hd i

open scoped Matrix.Norms.L2Operator in
private theorem scaled_perturbation_le {n : ℕ}
    {W M S : Matrix (Fin n) (Fin n) ℝ} {R a c : ℝ} (hR : 0 ≤ R)
    (hWM : realMatrixOperatorNorm (W - M) ≤ a)
    (hMS : realMatrixOperatorNorm (M - S) ≤ c) :
    realMatrixOperatorNorm (R • W - R • S) ≤ R * (a + c) := by
  change ‖R • W - R • S‖ ≤ _
  change ‖W - M‖ ≤ a at hWM
  change ‖M - S‖ ≤ c at hMS
  rw [← smul_sub, norm_smul, Real.norm_of_nonneg hR]
  apply mul_le_mul_of_nonneg_left _ hR
  rw [← sub_add_sub_cancel W M S]
  exact (norm_add_le _ _).trans (add_le_add hWM hMS)

open scoped Matrix.Norms.Frobenius in
private theorem frobeniusNorm_of_columns_le {n k : ℕ}
    (e : Fin k → EuclideanSpace ℝ (Fin n)) {c : ℝ}
    (hc : 0 ≤ c) (he : ∀ j, ‖e j‖ ≤ c) :
    let E : Matrix (Fin n) (Fin k) ℝ := fun i j => e j i
    ‖E‖ ≤ Real.sqrt k * c := by
  intro E
  rw [Matrix.frobenius_norm_def, ← Real.sqrt_eq_rpow, Finset.sum_comm]
  dsimp only [E]
  calc
    _ = Real.sqrt (∑ j, ‖e j‖ ^ 2) := by
      congr 1
      exact Finset.sum_congr rfl fun j _ => by
        simpa only [Real.rpow_two] using (EuclideanSpace.norm_sq_eq (e j)).symm
    _ ≤ Real.sqrt (∑ _ : Fin k, c ^ 2) :=
      Real.sqrt_le_sqrt (Finset.sum_le_sum fun j _ =>
        pow_le_pow_left₀ (norm_nonneg (e j)) (he j) 2)
    _ = Real.sqrt k * c := by simp [Real.sqrt_mul, Real.sqrt_sq_eq_abs, abs_of_nonneg hc]

/-- The clipped spectrum gives one symmetric witness retaining the signed
exact columns and every requested position. -/
theorem tridiagonalCommonWitness_proof : SourceTargets.tridiagonalCommonWitness := by
  intro n k p hp I T S M hM R Δ η θ U Qhat u ℓ μ ζ
    _hn hk hI hR hscale hT hMS hηΔ hgap hθ hμ hU hQhat
  have hu : 0 < u := unitRoundoff_pos p
  have hℓ : Monotone ℓ := ascendingEigenvalue_monotone hM
  have hη : 0 ≤ η := by
    exact (abs_nonneg _).trans (hθ ⟨0, by omega⟩)
  have hΔ : 0 < Δ := by linarith
  have hθorder : StrictMono θ := by
    intro i j hij
    have hij' : I i ≠ I j := (hI hij).ne
    have hdiff : ℓ (I i) - ℓ (I j) ≤ 0 := sub_nonpos.mpr (hℓ (hI hij).le)
    have hsep := hgap j (I i) hij'
    rw [abs_of_nonpos hdiff] at hsep
    linarith [(abs_le.mp (hθ i)).2, (abs_le.mp (hθ j)).1]
  have hμorder : Monotone μ := (roundToEven_monotone p hp).comp hθorder.monotone
  have hζorder : Monotone ζ := clipSelectedValues_monotone I ℓ μ hℓ
  have hζsel : ∀ j, ζ (I j) = μ j := clipSelectedValues_apply_selected I ℓ μ hI hμorder
  have hζerror : ∀ i, |ζ i - ℓ i| ≤ 2 * u :=
    clipSelectedValues_abs_sub_le I ℓ μ hℓ (by positivity) fun j => (hμ j).le
  refine ⟨hθorder, hμorder, hζorder, hζsel, hζerror, ?_⟩
  have hsimple (j : Fin k) (i : Fin n) (hij : i ≠ I j) :
      ℓ i ≠ ℓ (I j) := by
    intro he
    simpa [he, not_lt_of_ge hΔ.le] using hgap j i hij
  obtain ⟨b, hbEig, hbU⟩ := exists_ascendingEigenbasis_preserving_selected hM I
    hI.injective U hsimple hU
  let V := orthonormalBasisMatrix b
  let Z := V * Matrix.diagonal ζ * V.transpose
  let W := R • Z
  have hWmat : W = V * Matrix.diagonal (fun i => R * ζ i) * V.transpose := by
    change R • (V * Matrix.diagonal ζ * V.transpose) =
      V * Matrix.diagonal (R • ζ) * V.transpose
    rw [Matrix.diagonal_smul, Matrix.mul_smul, Matrix.smul_mul]
  have hW : W.IsHermitian := by
    rw [hWmat]
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      Matrix.isHermitian_mul_mul_conjTranspose V (Matrix.isHermitian_diagonal (fun i => R * ζ i))
  have hWeig : ∀ i, W.toEuclideanLin (b i) = (R * ζ i) • b i := by
    apply (basis_eigenvector_iff W b (fun i => R * ζ i)).2
    change W * V = V * Matrix.diagonal (fun i => R * ζ i)
    rw [hWmat, Matrix.mul_assoc _ V.transpose V, orthonormalBasisMatrix_transpose_mul_self,
      Matrix.mul_one]
  have hWordered (i : Fin n) : ascendingEigenvalue hW i = R * ζ i :=
    ascendingEigenvalue_eq_of_eigenbasis hW b (fun j => R * ζ j)
      (fun _ _ hij => mul_le_mul_of_nonneg_left (hζorder hij) hR.le) hWeig i
  have hMrec : M = V * Matrix.diagonal ℓ * V.transpose := by
    have hMV : M * V = V * Matrix.diagonal ℓ := (basis_eigenvector_iff M b ℓ).1 hbEig
    rw [← hMV, Matrix.mul_assoc, orthonormalBasisMatrix_mul_transpose, Matrix.mul_one]
  have hZdiff : Z - M = V * Matrix.diagonal (fun i => ζ i - ℓ i) * V.transpose := by
    change V * Matrix.diagonal ζ * V.transpose - M = _
    rw [hMrec, ← Matrix.sub_mul, ← Matrix.mul_sub, Matrix.diagonal_sub]
  have hZnorm : realMatrixOperatorNorm (Z - M) ≤ 2 * u := by
    rw [hZdiff]
    exact basis_diagonal_opNorm_le b _ (by positivity) hζerror
  have hback : realMatrixOperatorNorm (W - T) ≤ R * (2 * u + u / 128) := by
    rw [hT]
    exact scaled_perturbation_le hR.le hZnorm hMS
  have hback' : R * (2 * u + u / 128) < 24 * u * realMatrixOperatorNorm T := by
    calc
      _ < R * (3 * u) := mul_lt_mul_of_pos_left (by linarith) hR
      _ < (8 * realMatrixOperatorNorm T) * (3 * u) :=
        mul_lt_mul_of_pos_right hscale (by positivity)
      _ = _ := by ring
  refine ⟨b, W, hW, hbEig, hbU, rfl, hback, hback', hback.trans hback'.le, ?_, ?_, ?_⟩
  · have h : U = b ∘ I := funext fun j => (hbU j).symm
    rw [h]
    exact b.orthonormal.comp I hI.injective
  · have h := frobeniusNorm_of_columns_le (fun j => Qhat j - U j) (by positivity) hQhat
    simpa only [← mul_assoc, mul_comm (Real.sqrt (k : ℝ)) (4 : ℝ)] using h
  · intro j
    refine ⟨?_, ?_, hQhat j⟩
    · rw [← hbU, hWeig, hζsel]
    · rw [hWordered, hζsel]

end NumStability.CertifiedTridiagonalEigenpairs
