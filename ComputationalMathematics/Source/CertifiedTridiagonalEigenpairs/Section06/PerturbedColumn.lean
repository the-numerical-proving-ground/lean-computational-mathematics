import ComputationalMathematics.Analysis.FunctionalCalculus.Resolvent.ShiftPerturbation
import ComputationalMathematics.Source.CertifiedTridiagonalEigenpairs.Section06.FilteredColumn

/-! # Exact imaginary columns of the perturbed inverse -/

open Matrix WithLp
open scoped Matrix.Norms.L2Operator

namespace NumStability.CertifiedTridiagonalEigenpairs

private lemma norm_euclidean_im_le {ι : Type*} [Fintype ι] (x : ι → ℂ) :
    ‖toLp 2 (Complex.im ∘ x)‖ ≤ ‖toLp 2 x‖ := by
  refine (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1 ?_
  rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [Real.norm_eq_abs]
  exact (sq_le_sq₀ (abs_nonneg _) (norm_nonneg _)).2 (Complex.abs_im_le_norm _)

private lemma mulVec_im_eq_im_mulVec {ι : Type*} [Fintype ι] (P : Matrix ι ι ℝ) (x : ι → ℂ) :
    P *ᵥ (Complex.im ∘ x) = Complex.im ∘ (P.map Complex.ofReal *ᵥ x) := by
  funext i
  simp only [Matrix.mulVec, dotProduct, Function.comp_apply, Complex.im_sum,
    Matrix.map_apply, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]

private lemma norm_euclidean_mulVec_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℂ) (x : ι → ℂ) :
    ‖toLp 2 (M *ᵥ x)‖ ≤ ‖M‖ * ‖toLp 2 x‖ :=
  Matrix.l2_opNorm_mulVec M (toLp 2 x)

/-- Two orders of the resolvent identity control the perturbed column and its real projection.
The inputs on the exact column are the signal, phase, and complementary bounds already
established in Section 6. -/
theorem exactResolventPerturbedColumnBounds {n : ℕ} {A E : Matrix (Fin n) (Fin n) ℂ}
    (hA : A.IsHermitian) (P : Matrix (Fin n) (Fin n) ℝ) (r : Fin n)
    {shift η Δ : ℝ} (hη : 0 < η) (hE : ‖E‖ ≤ η / 64) :
    let K := MatrixResolvent.imaginaryShift A shift η
    let G := K⁻¹
    let H := (K + E)⁻¹
    let g := G.col r
    let f := Complex.im ∘ g
    let w := H.col r
    let y := Complex.im ∘ w
    0 < ‖toLp 2 f‖ →
    ‖toLp 2 g‖ ≤ 2 * ‖toLp 2 f‖ →
    ‖toLp 2 (P *ᵥ f)‖ ≤ 4 * η / Δ^2 →
    ‖P.map Complex.ofReal * G‖ ≤ 2 / Δ →
    (61 / 63) * ‖toLp 2 f‖ ≤ ‖toLp 2 y‖ ∧
      ‖toLp 2 w‖ ≤ (128 / 63) * ‖toLp 2 f‖ ∧
      ‖toLp 2 w‖ < 3 * ‖toLp 2 y‖ ∧
      ‖toLp 2 (P *ᵥ y)‖ ≤
        4 * η / Δ^2 + (2 * ‖E‖ / Δ) * ‖toLp 2 w‖ := by
  intro K G H g f w y hf hphase hPf hPG
  have hE' : ‖E‖ < η := by linarith
  obtain ⟨_, hHnorm, hLeft, hRight⟩ :=
    MatrixResolvent.imaginaryShift_perturbation hA hη hE'
  change ‖H‖ ≤ (η - ‖E‖)⁻¹ at hHnorm
  change H - G = -(H * E * G) at hLeft
  change H = G - G * E * H at hRight
  have hwg : w - g = -((H * E) *ᵥ g) := by
    exact congrArg (fun M => M.col r) hLeft
  have hdiff : ‖toLp 2 (w - g)‖ ≤ (2 / 63) * ‖toLp 2 f‖ := by
    have hrel : (η - ‖E‖)⁻¹ * ‖E‖ ≤ 1 / 63 := by
      rw [mul_comm, ← div_eq_mul_inv, div_le_div_iff₀ (sub_pos.mpr hE') (by norm_num)]
      linarith
    rw [hwg, WithLp.toLp_neg, norm_neg]
    calc
      _ ≤ ‖H * E‖ * ‖toLp 2 g‖ := norm_euclidean_mulVec_le _ _
      _ ≤ (‖H‖ * ‖E‖) * ‖toLp 2 g‖ :=
        mul_le_mul_of_nonneg_right (Matrix.l2_opNorm_mul _ _) (norm_nonneg _)
      _ ≤ ((η - ‖E‖)⁻¹ * ‖E‖) * ‖toLp 2 g‖ :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hHnorm (norm_nonneg _)) (norm_nonneg _)
      _ ≤ (1 / 63) * ‖toLp 2 g‖ := mul_le_mul_of_nonneg_right hrel (norm_nonneg _)
      _ ≤ (1 / 63) * (2 * ‖toLp 2 f‖) := mul_le_mul_of_nonneg_left hphase (by norm_num)
      _ = _ := by ring
  have himdiff : ‖toLp 2 y - toLp 2 f‖ ≤ (2 / 63) * ‖toLp 2 f‖ := by
    rw [← WithLp.toLp_sub]
    have him : y - f = Complex.im ∘ (w - g) := by
      funext i
      simp [f, y]
    exact (congrArg (fun x => ‖toLp 2 x‖) him ▸ norm_euclidean_im_le (w - g)).trans hdiff
  have hyLower : (61 / 63) * ‖toLp 2 f‖ ≤ ‖toLp 2 y‖ := by
    have h := norm_sub_le (toLp 2 y) (toLp 2 y - toLp 2 f)
    rw [sub_sub_cancel] at h
    linarith
  have hwUpper : ‖toLp 2 w‖ ≤ (128 / 63) * ‖toLp 2 f‖ := by
    have h := norm_add_le (toLp 2 (w - g)) (toLp 2 g)
    rw [← WithLp.toLp_add, sub_add_cancel] at h
    linarith
  have hWRight : w = g - (G * E) *ᵥ w := by exact congrArg (fun M => M.col r) hRight
  have hYRight : y = f - Complex.im ∘ ((G * E) *ᵥ w) := by
    change Complex.im ∘ w = Complex.im ∘ g - Complex.im ∘ ((G * E) *ᵥ w)
    nth_rw 1 [hWRight]
    funext i
    simp
  have hPsub : P *ᵥ y = P *ᵥ f - Complex.im ∘ ((P.map Complex.ofReal * G * E) *ᵥ w) := by
    rw [hYRight, Matrix.mulVec_sub, mulVec_im_eq_im_mulVec P ((G * E) *ᵥ w),
      Matrix.mulVec_mulVec, ← Matrix.mul_assoc]
  have hcomp : ‖toLp 2 (P *ᵥ y)‖ ≤ 4 * η / Δ^2 + (2 * ‖E‖ / Δ) * ‖toLp 2 w‖ := by
    rw [hPsub, WithLp.toLp_sub]
    refine (norm_sub_le _ _).trans (add_le_add hPf ?_)
    refine (norm_euclidean_im_le _).trans ((norm_euclidean_mulVec_le _ _).trans ?_)
    calc
      _ ≤ (‖P.map Complex.ofReal * G‖ * ‖E‖) * ‖toLp 2 w‖ :=
        mul_le_mul_of_nonneg_right (Matrix.l2_opNorm_mul _ _) (norm_nonneg _)
      _ ≤ ((2 / Δ) * ‖E‖) * ‖toLp 2 w‖ :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hPG (norm_nonneg _))
          (norm_nonneg _)
      _ = _ := by ring
  exact ⟨hyLower, hwUpper, by linarith, hcomp⟩

/-- The two contributions to the imaginary angle are bounded by `3u/32` and `15u/512`. -/
theorem exactImaginaryAngleBudget {n : ℕ} (hn : 0 < n) {η Δ δ ω u F W Y Q : ℝ}
    (hη : 0 < η) (hΔ : 0 < Δ) (hδ : 0 ≤ δ)
    (hShift : η^2 ≤ Δ^2 * u / (256 * Real.sqrt (n : ℝ)))
    (hPert : δ ≤ 40 * ω) (hω : ω ≤ u * Δ / 8192)
    (hF : (Real.sqrt (32 * (n : ℝ)) * η)⁻¹ ≤ F)
    (hY : (61 / 63) * F ≤ Y) (hW : W < 3 * Y)
    (hQ : Q ≤ 4 * η / Δ^2 + (2 * δ / Δ) * W) :
    Q / Y ≤ (63 / 512) * u := by
  have hn0 : 0 < (n : ℝ) := by exact_mod_cast hn
  have hscale : 0 < Real.sqrt (32 * (n : ℝ)) * η := by positivity
  have hYmin : (61 / 63) * (Real.sqrt (32 * (n : ℝ)) * η)⁻¹ ≤ Y :=
    (mul_le_mul_of_nonneg_left hF (by norm_num)).trans hY
  have hYpos : 0 < Y := (by positivity :
    0 < (61 / 63) * (Real.sqrt (32 * (n : ℝ)) * η)⁻¹).trans_le hYmin
  have hInvY : Y⁻¹ ≤ (63 / 61) * (Real.sqrt (32 * (n : ℝ)) * η) := by
    calc
      _ ≤ ((61 / 63) * (Real.sqrt (32 * (n : ℝ)) * η)⁻¹)⁻¹ :=
        inv_anti₀ (by positivity) hYmin
      _ = _ := by rw [mul_inv, inv_inv]; norm_num
  have hcoef : 4 * (63 / 61) * Real.sqrt 32 ≤ (24 : ℝ) := by
    have hroot : Real.sqrt 32 ≤ (23 / 4 : ℝ) :=
      (Real.sqrt_le_left (by norm_num)).2 (by norm_num)
    linarith
  have htermF : (4 * η / Δ^2) / Y ≤ 24 * Real.sqrt (n : ℝ) * η^2 / Δ^2 := by
    rw [div_eq_mul_inv (4 * η / Δ^2) Y]
    calc
      _ ≤ (4 * η / Δ^2) * ((63 / 61) * (Real.sqrt (32 * (n : ℝ)) * η)) :=
        mul_le_mul_of_nonneg_left hInvY (by positivity)
      _ = (4 * (63 / 61) * Real.sqrt 32) * (Real.sqrt (n : ℝ) * η^2 / Δ^2) := by
        rw [Real.sqrt_mul (by norm_num)]
        ring
      _ ≤ 24 * (Real.sqrt (n : ℝ) * η^2 / Δ^2) :=
        mul_le_mul_of_nonneg_right hcoef (by positivity)
      _ = _ := by ring
  have htermF' : 24 * Real.sqrt (n : ℝ) * η^2 / Δ^2 ≤ (3 / 32) * u := by
    have h := (le_div_iff₀ (by positivity : 0 < 256 * Real.sqrt (n : ℝ))).1 hShift
    apply (div_le_iff₀ (by positivity : 0 < Δ^2)).2
    nlinarith
  have hδ' : δ ≤ 40 * (u * Δ / 8192) :=
    hPert.trans (mul_le_mul_of_nonneg_left hω (by norm_num))
  have htermW : ((2 * δ / Δ) * W) / Y ≤ (15 / 512) * u := by
    calc
      _ = (2 * δ / Δ) * (W / Y) := by ring
      _ ≤ (2 * δ / Δ) * 3 := mul_le_mul_of_nonneg_left
        ((div_le_iff₀ hYpos).2 hW.le) (by positivity)
      _ = 6 * δ / Δ := by ring
      _ ≤ (15 / 512) * u := by
        apply (div_le_iff₀ hΔ).2
        linarith
  calc
    Q / Y ≤ (4 * η / Δ^2 + (2 * δ / Δ) * W) / Y :=
      div_le_div_of_nonneg_right hQ hYpos.le
    _ ≤ (3 / 32) * u + (15 / 512) * u := by
      rw [add_div]
      exact add_le_add (htermF.trans htermF') htermW
    _ = _ := by ring

private lemma exists_sign_dist_le_projection {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] (v x : V) (hv : ‖v‖ = 1) (hx : ‖x‖ = 1) :
    ∃ σ : ℝ, (σ = -1 ∨ σ = 1) ∧
      ‖x - σ • v‖ ≤ Real.sqrt 2 * ‖x - (inner ℝ v x) • v‖ := by
  let t := inner ℝ v x
  let σ : ℝ := if 0 ≤ t then 1 else -1
  have hσ : σ = -1 ∨ σ = 1 := by by_cases ht : 0 ≤ t <;> simp [σ, ht]
  have hσsq : σ^2 = 1 := by rcases hσ with h | h <;> simp [h]
  have hsign : σ * t = |t| := by
    by_cases ht : 0 ≤ t
    · simp [σ, ht, abs_of_nonneg ht]
    · simp [σ, ht, abs_of_neg (lt_of_not_ge ht)]
  have htBound : |t| ≤ 1 := by
    simpa [t, hv, hx] using abs_real_inner_le_norm v x
  have htSquare : t^2 ≤ |t| := by
    rw [← sq_abs]
    nlinarith [mul_nonneg (abs_nonneg t) (sub_nonneg.mpr htBound)]
  have hNormSq (a : ℝ) : ‖x - a • v‖^2 = 1 - 2 * (a * t) + a^2 := by
    rw [norm_sub_sq_real, hx, norm_smul, hv, mul_one, Real.norm_eq_abs, sq_abs,
      real_inner_smul_right, real_inner_comm v x]
    norm_num [t]
  refine ⟨σ, hσ, (sq_le_sq₀ (norm_nonneg _) (by positivity)).1 ?_⟩
  change ‖x - σ • v‖^2 ≤ (Real.sqrt 2 * ‖x - t • v‖)^2
  rw [mul_pow, Real.sq_sqrt (by norm_num), hNormSq, hNormSq, hσsq, hsign]
  nlinarith

/-- Choosing the closer sign turns the sine bound into the exact-direction estimate. -/
theorem exactDirection_of_imaginaryAngle {n : ℕ} (v y : EuclideanSpace ℝ (Fin n))
    (hv : ‖v‖ = 1) (hy : 0 < ‖y‖) {u : ℝ} (hu : 0 < u)
    (hAngle : ‖toLp 2 ((1 - Matrix.vecMulVec v.ofLp v.ofLp) *ᵥ y.ofLp)‖ / ‖y‖ ≤
      (63 / 512) * u) :
    ∃ σ : ℝ, (σ = -1 ∨ σ = 1) ∧
      ‖‖y‖⁻¹ • y - σ • v‖ ≤ (63 * Real.sqrt 2 / 512) * u ∧
      ‖‖y‖⁻¹ • y - σ • v‖ < u / 4 := by
  let x := ‖y‖⁻¹ • y
  have hx : ‖x‖ = 1 := by
    simp [x, norm_smul, inv_mul_cancel₀ hy.ne']
  have hProj : y - (inner ℝ v y) • v =
      toLp 2 ((1 - Matrix.vecMulVec v.ofLp v.ofLp) *ᵥ y.ofLp) := by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.vecMulVec_mulVec, op_smul_eq_smul,
      WithLp.toLp_sub, WithLp.toLp_smul]
    have hinner : inner ℝ v y = v.ofLp ⬝ᵥ y.ofLp := by
      exact (EuclideanSpace.inner_eq_star_dotProduct (𝕜 := ℝ) v y).trans
        (by simpa using dotProduct_comm y.ofLp v.ofLp)
    exact congrArg (fun c : ℝ => y - c • v) hinner
  have hProjX : x - (inner ℝ v x) • v = ‖y‖⁻¹ • (y - (inner ℝ v y) • v) := by
    change ‖y‖⁻¹ • y - (inner ℝ v (‖y‖⁻¹ • y)) • v =
      ‖y‖⁻¹ • (y - (inner ℝ v y) • v)
    rw [real_inner_smul_right, smul_sub, smul_smul]
  have hProjNorm : ‖x - (inner ℝ v x) • v‖ ≤ (63 / 512) * u := by
    rw [hProjX, hProj, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hy), ← div_eq_inv_mul]
    exact hAngle
  obtain ⟨σ, hσ, hDist⟩ := exists_sign_dist_le_projection v x hv hx
  have hDist' : ‖x - σ • v‖ ≤ (63 * Real.sqrt 2 / 512) * u := by
    refine hDist.trans ((mul_le_mul_of_nonneg_left hProjNorm (Real.sqrt_nonneg _)).trans_eq ?_)
    ring
  have hSqrt : Real.sqrt 2 ≤ (3 / 2 : ℝ) :=
    (Real.sqrt_le_left (by norm_num)).2 (by norm_num)
  have hc : 63 * Real.sqrt 2 / 512 < (1 / 4 : ℝ) := by linarith
  refine ⟨σ, hσ, hDist', hDist'.trans_lt ?_⟩
  rw [show u / 4 = (1 / 4) * u by ring]
  exact mul_lt_mul_of_pos_right hc hu

/-- The exact imaginary part of the perturbed selected inverse column is nonzero and satisfies
the angle and signed direction bounds in Section 6. The input perturbation has the bounds
established by the directional factorization and score analysis. -/
theorem exactResolventPerturbedDirection {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    {E : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsSymm) (j r : Fin n)
    (v : EuclideanSpace ℝ (Fin n)) (hv : ‖v‖ = 1)
    (heig : A *ᵥ v.ofLp = (MatrixResolvent.isHermitian_map_ofReal hA).eigenvalues j • v.ofLp)
    {shift η Δ u ω : ℝ} (hη : 0 < η) (hΔ : 0 < Δ) (hu : 0 < u)
    (hnu : (n : ℝ) * u ≤ 1 / 128)
    (hprec : η ≤ Δ * Real.sqrt u / (16 * Real.sqrt (Real.sqrt (n : ℝ))))
    (hnear : |shift - (MatrixResolvent.isHermitian_map_ofReal hA).eigenvalues j| ≤ η)
    (hgap : ∀ i ≠ j, Δ ≤ |(MatrixResolvent.isHermitian_map_ofReal hA).eigenvalues i -
      (MatrixResolvent.isHermitian_map_ofReal hA).eigenvalues j|)
    (hE : ‖E‖ ≤ η / 64) (hEω : ‖E‖ ≤ 40 * ω) (hω : ω ≤ u * Δ / 8192) :
    let P := 1 - Matrix.vecMulVec v.ofLp v.ofLp
    let K := MatrixResolvent.imaginaryShift (A.map Complex.ofReal) shift η
    let G := K⁻¹
    let H := (K + E)⁻¹
    let f := Complex.im ∘ G.col r
    let w := H.col r
    let y := toLp 2 (Complex.im ∘ w)
    (4 * (n : ℝ) * η)⁻¹ ≤ (G r r).im →
      (61 / 63) * ‖toLp 2 f‖ ≤ ‖y‖ ∧
      ‖toLp 2 w‖ ≤ (128 / 63) * ‖toLp 2 f‖ ∧ ‖toLp 2 w‖ < 3 * ‖y‖ ∧
      0 < ‖y‖ ∧ ‖toLp 2 (P *ᵥ y.ofLp)‖ / ‖y‖ ≤ (63 / 512) * u ∧
        ∃ σ : ℝ, (σ = -1 ∨ σ = 1) ∧
          ‖‖y‖⁻¹ • y - σ • v‖ ≤ (63 * Real.sqrt 2 / 512) * u ∧
          ‖‖y‖⁻¹ • y - σ • v‖ < u / 4 := by
  intro P K G H f w y hselected
  have hn : 0 < n := Nat.zero_lt_of_lt r.isLt
  have hn' : 1 ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0 : 0 < (n : ℝ) := by exact_mod_cast hn
  obtain ⟨hηgap, _, _, hηsq⟩ := exactShiftPrecisionBounds hn' hη hΔ hu.le hnu hprec
  obtain ⟨_, _, hSignal, _, hPhase⟩ :=
    exactResolventSelectedColumnPhase hA j r v hv heig hη hΔ hu.le hnu hprec hnear hgap hselected
  have hPForig := (exactResolventFilteredComplement hA j r v hv heig hη hΔ
    hηgap hnear hgap).1
  have hPG := (exactResolventFilteredOperatorBounds hA j v hv heig hη hΔ hηgap hnear hgap).1
  have hf : 0 < ‖toLp 2 f‖ :=
    (by positivity : 0 < (Real.sqrt (32 * (n : ℝ)) * η)⁻¹).trans_le hSignal
  obtain ⟨hyLower, hwUpper, hwStrict, hQ⟩ := exactResolventPerturbedColumnBounds
    (MatrixResolvent.isHermitian_map_ofReal hA) P r hη hE hf hPhase.le hPForig hPG
  have hy : 0 < ‖y‖ := (by positivity : 0 < (61 / 63) * ‖toLp 2 f‖).trans_le hyLower
  have hAngle : ‖toLp 2 (P *ᵥ y.ofLp)‖ / ‖y‖ ≤ (63 / 512) * u :=
    exactImaginaryAngleBudget hn hη hΔ (norm_nonneg E) hηsq hEω hω hSignal hyLower hwStrict hQ
  exact ⟨hyLower, hwUpper, hwStrict, hy, hAngle, exactDirection_of_imaginaryAngle v y hv hy hu hAngle⟩

end NumStability.CertifiedTridiagonalEigenpairs
