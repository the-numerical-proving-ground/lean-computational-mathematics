import ComputationalMathematics.Analysis.FunctionalCalculus.Resolvent.ImaginaryShift

/-! # Complementary eigenvector bounds for an imaginary resolvent column -/

open Matrix WithLp
open scoped Matrix.Norms.L2Operator

namespace NumStability.CertifiedTridiagonalEigenpairs

private lemma norm_toLp_ofReal {n : Type*} [Fintype n] (x : n → ℝ) :
    ‖toLp 2 (Complex.ofReal ∘ x)‖ = ‖toLp 2 x‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
  simp

/-- Complementary operator bounds for the real projection `I - v vᵀ`. -/
theorem exactResolventFilteredOperatorBounds {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.IsSymm) (j : Fin n) (v : EuclideanSpace ℝ (Fin n))
    (hv : ‖v‖ = 1)
    (heig : A *ᵥ v.ofLp = (MatrixResolvent.isHermitian_map_ofReal hA).eigenvalues j • v.ofLp)
    {shift η Δ : ℝ} (hη : 0 < η) (hΔ : 0 < Δ) (hηgap : η ≤ Δ / 2)
    (hnear : |shift - (MatrixResolvent.isHermitian_map_ofReal hA).eigenvalues j| ≤ η)
    (hgap : ∀ i ≠ j, Δ ≤ |(MatrixResolvent.isHermitian_map_ofReal hA).eigenvalues i -
      (MatrixResolvent.isHermitian_map_ofReal hA).eigenvalues j|) :
    let P := 1 - Matrix.vecMulVec v.ofLp v.ofLp
    let G := (MatrixResolvent.imaginaryShift (A.map Complex.ofReal) shift η)⁻¹
    let F : Matrix (Fin n) (Fin n) ℂ := (2 * Complex.I : ℂ)⁻¹ • (G - Gᴴ)
    ‖P.map Complex.ofReal * G‖ ≤ 2 / Δ ∧ ‖P.map Complex.ofReal * F‖ ≤ 4 * η / Δ^2 := by
  let Ac := A.map Complex.ofReal
  let hAc := MatrixResolvent.isHermitian_map_ofReal hA
  let P := 1 - Matrix.vecMulVec v.ofLp v.ofLp
  let G := (MatrixResolvent.imaginaryShift Ac shift η)⁻¹
  let F : Matrix (Fin n) (Fin n) ℂ := (2 * Complex.I : ℂ)⁻¹ • (G - Gᴴ)
  let u := toLp 2 (Complex.ofReal ∘ v.ofLp)
  have hu : ‖u‖ = 1 := (norm_toLp_ofReal v.ofLp).trans hv
  have heigC : Ac *ᵥ u.ofLp = (hAc.eigenvalues j : ℂ) • u.ofLp := by
    funext i
    have h := congrFun heig i
    have hC := congrArg Complex.ofRealHom h
    rw [RingHom.map_mulVec] at hC
    simpa [Ac, u, Function.comp_apply, Pi.smul_apply, smul_eq_mul] using hC
  have hsep (i : Fin n) (hi : i ≠ j) : hAc.eigenvalues i ≠ hAc.eigenvalues j := by
    intro h
    have hp := hgap i hi
    change Δ ≤ |hAc.eigenvalues i - hAc.eigenvalues j| at hp
    rw [h, sub_self, abs_zero] at hp
    exact hΔ.not_ge hp
  have hP : MatrixResolvent.eigenvectorComplement hAc j = P.map Complex.ofReal := by
    rw [MatrixResolvent.eigenvectorComplement_eq_of_unit_eigenvector hAc j u hu heigC hsep]
    ext i k
    by_cases hik : i = k <;>
      simp [P, u, Matrix.vecMulVec_apply, hik]
  have hnorm := MatrixResolvent.norm_eigenvectorComplement_mul_inv_imaginaryShift_le
    hAc j hη hΔ hηgap hnear hgap
  change ‖MatrixResolvent.eigenvectorComplement hAc j * G‖ ≤ _ ∧
    ‖MatrixResolvent.eigenvectorComplement hAc j * F‖ ≤ _ at hnorm
  rw [hP] at hnorm
  exact hnorm

/-- The column estimates in `vec:filtered-complement` of the certified tridiagonal
eigenpairs paper. The projection is the real matrix `I - v vᵀ` formed from an arbitrary
real unit eigenvector for the isolated target eigenvalue. -/
theorem exactResolventFilteredComplement {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.IsSymm) (j r : Fin n) (v : EuclideanSpace ℝ (Fin n))
    (hv : ‖v‖ = 1)
    (heig : A *ᵥ v.ofLp = (MatrixResolvent.isHermitian_map_ofReal hA).eigenvalues j • v.ofLp)
    {shift η Δ : ℝ} (hη : 0 < η) (hΔ : 0 < Δ) (hηgap : η ≤ Δ / 2)
    (hnear : |shift - (MatrixResolvent.isHermitian_map_ofReal hA).eigenvalues j| ≤ η)
    (hgap : ∀ i ≠ j, Δ ≤ |(MatrixResolvent.isHermitian_map_ofReal hA).eigenvalues i -
      (MatrixResolvent.isHermitian_map_ofReal hA).eigenvalues j|) :
    let P := 1 - Matrix.vecMulVec v.ofLp v.ofLp
    let G := (MatrixResolvent.imaginaryShift (A.map Complex.ofReal) shift η)⁻¹
    let g := G.col r
    let f := Complex.im ∘ g
    ‖toLp 2 (P *ᵥ f)‖ ≤ 4 * η / Δ^2 ∧
      ‖toLp 2 (P.map Complex.ofReal *ᵥ g)‖ ≤ 2 / Δ := by
  let Ac := A.map Complex.ofReal
  let P := 1 - Matrix.vecMulVec v.ofLp v.ofLp
  let G := (MatrixResolvent.imaginaryShift Ac shift η)⁻¹
  let F : Matrix (Fin n) (Fin n) ℂ := (2 * Complex.I : ℂ)⁻¹ • (G - Gᴴ)
  have hAcSymm : Ac.IsSymm := by
    ext i k
    exact congrArg Complex.ofReal (hA.apply i k)
  have hGsymm : G.IsSymm := MatrixResolvent.isSymm_inv_imaginaryShift hAcSymm shift η
  have hF (i k : Fin n) : F i k = (Complex.im (G i k) : ℂ) := by
    change (2 * Complex.I : ℂ)⁻¹ * (G i k - star (G k i)) = _
    rw [show G k i = G i k from hGsymm.apply i k, Complex.star_def, Complex.im_eq_sub_conj,
      div_eq_inv_mul]
  have hnorm :=
    exactResolventFilteredOperatorBounds hA j v hv heig hη hΔ hηgap hnear hgap
  change ‖P.map Complex.ofReal * G‖ ≤ _ ∧ ‖P.map Complex.ofReal * F‖ ≤ _ at hnorm
  have hcolumn (M : Matrix (Fin n) (Fin n) ℂ) :
      ‖toLp 2 (P.map Complex.ofReal *ᵥ M.col r)‖ ≤ ‖P.map Complex.ofReal * M‖ := by
    have h := Matrix.l2_opNorm_mulVec (P.map Complex.ofReal * M) (EuclideanSpace.single r 1)
    change ‖toLp 2 ((P.map Complex.ofReal * M) *ᵥ
      (EuclideanSpace.single r (1 : ℂ)).ofLp)‖ ≤ _ at h
    rw [EuclideanSpace.ofLp_single, EuclideanSpace.norm_single, norm_one, mul_one,
      ← Matrix.mulVec_mulVec, Matrix.mulVec_single_one] at h
    exact h
  have hmap : Complex.ofReal ∘ (P *ᵥ (Complex.im ∘ G.col r)) =
      P.map Complex.ofReal *ᵥ F.col r := by
    have hcol : Complex.ofReal ∘ (Complex.im ∘ G.col r) = F.col r :=
      funext fun i => (hF i r).symm
    funext i
    change Complex.ofRealHom ((P *ᵥ (Complex.im ∘ G.col r)) i) = _
    rw [RingHom.map_mulVec]
    change (P.map Complex.ofReal *ᵥ (Complex.ofReal ∘ (Complex.im ∘ G.col r))) i = _
    rw [hcol]
  change ‖toLp 2 (P *ᵥ (Complex.im ∘ G.col r))‖ ≤ _ ∧
    ‖toLp 2 (P.map Complex.ofReal *ᵥ G.col r)‖ ≤ _
  constructor
  · rw [← norm_toLp_ofReal, hmap]
    exact (hcolumn F).trans hnorm.2
  · exact (hcolumn G).trans hnorm.1

/-- The exact selected column has a target signal of size at least `1 / (sqrt (32 n) η)`.
Its complex norm is bounded by the imaginary norm and the complementary gap term. -/
theorem exactResolventSelectedColumnSignal {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.IsSymm) (j r : Fin n) (v : EuclideanSpace ℝ (Fin n))
    (hv : ‖v‖ = 1)
    (heig : A *ᵥ v.ofLp = (MatrixResolvent.isHermitian_map_ofReal hA).eigenvalues j • v.ofLp)
    {shift η Δ : ℝ} (hη : 0 < η) (hΔ : 0 < Δ) (hηgap : η ≤ Δ / 2)
    (hnear : |shift - (MatrixResolvent.isHermitian_map_ofReal hA).eigenvalues j| ≤ η)
    (hgap : ∀ i ≠ j, Δ ≤ |(MatrixResolvent.isHermitian_map_ofReal hA).eigenvalues i -
      (MatrixResolvent.isHermitian_map_ofReal hA).eigenvalues j|)
    (hsmall : 4 * η^2 / Δ^2 ≤ (8 * (n : ℝ))⁻¹) :
    let G := (MatrixResolvent.imaginaryShift (A.map Complex.ofReal) shift η)⁻¹
    let g := G.col r
    let f := Complex.im ∘ g
    (4 * (n : ℝ) * η)⁻¹ ≤ (G r r).im →
      (Real.sqrt (8 * (n : ℝ)))⁻¹ ≤ |v.ofLp r| ∧
      |v.ofLp r| / (2 * η) ≤ ‖toLp 2 f‖ ∧
      (Real.sqrt (32 * (n : ℝ)) * η)⁻¹ ≤ ‖toLp 2 f‖ ∧
      ‖toLp 2 g‖ ≤ Real.sqrt 2 * ‖toLp 2 f‖ + 2 / Δ := by
  let Ac := A.map Complex.ofReal
  let hAc := MatrixResolvent.isHermitian_map_ofReal hA
  let P := 1 - Matrix.vecMulVec v.ofLp v.ofLp
  let G := (MatrixResolvent.imaginaryShift Ac shift η)⁻¹
  let g := G.col r
  let f := Complex.im ∘ g
  let u := Complex.ofReal ∘ v.ofLp
  let μ := hAc.eigenvalues j
  let d := ((μ : ℂ) - ((shift : ℂ) + (η : ℂ) * Complex.I))⁻¹
  intro _ _ _ hselected
  have hu : ‖toLp 2 u‖ = 1 := (norm_toLp_ofReal v.ofLp).trans hv
  have heigC : Ac *ᵥ u = (μ : ℂ) • u := by
    funext i
    have h := congrArg Complex.ofRealHom (congrFun heig i)
    rw [RingHom.map_mulVec] at h
    simpa [Ac, u, μ, Function.comp_apply, Pi.smul_apply, smul_eq_mul] using h
  have hAcSymm : Ac.IsSymm := by
    ext i k
    exact congrArg Complex.ofReal (hA.apply i k)
  have hGsymm : G.IsSymm := MatrixResolvent.isSymm_inv_imaginaryShift hAcSymm shift η
  have hgEig : G *ᵥ u = d • u :=
    MatrixResolvent.inv_imaginaryShift_mulVec_of_eigenvector hAc hη heigC
  have hdcomp : g ⬝ᵥ u = d * u r := by
    have hdot : g ⬝ᵥ u = (G *ᵥ u) r := by
      apply Finset.sum_congr rfl
      intro i _
      rw [show g i = G i r from rfl, hGsymm.apply r i]
    exact hdot.trans (congrFun hgEig r)
  have hdreal : f ⬝ᵥ v.ofLp = d.im * v.ofLp r := by
    simpa [dotProduct, Complex.im_sum, Complex.mul_im, u, f, Function.comp_apply] using
      congrArg Complex.im hdcomp
  have hpos := MatrixResolvent.inv_imaginaryShift_scalar_bounds hη hnear
  change (2 * η)⁻¹ ≤ d.im ∧ d.im ≤ η⁻¹ ∧ ‖d‖ ≤ Real.sqrt 2 * d.im at hpos
  have hImNonneg : 0 ≤ d.im := (by positivity : 0 ≤ (2 * η)⁻¹).trans hpos.1
  have hfiltered := exactResolventFilteredComplement hA j r v hv heig hη hΔ hηgap hnear hgap
  change ‖toLp 2 (P *ᵥ f)‖ ≤ _ ∧ ‖toLp 2 (P.map Complex.ofReal *ᵥ g)‖ ≤ _ at hfiltered
  have hPr : (P *ᵥ f) r = f r - d.im * (v.ofLp r)^2 := by
    rw [show P = 1 - Matrix.vecMulVec v.ofLp v.ofLp from rfl, Matrix.sub_mulVec,
      Matrix.one_mulVec, Matrix.vecMulVec_mulVec, dotProduct_comm v.ofLp f, hdreal, op_smul_eq_smul]
    change f r - (d.im * v.ofLp r) * v.ofLp r = _
    ring
  have hScoreUpper : f r ≤ η⁻¹ * (v.ofLp r)^2 + 4 * η / Δ^2 := by
    have hcoord := PiLp.norm_apply_le (toLp 2 (P *ᵥ f)) r
    change ‖(P *ᵥ f) r‖ ≤ _ at hcoord
    rw [hPr, Real.norm_eq_abs] at hcoord
    linarith [(le_abs_self _).trans (hcoord.trans hfiltered.1),
      mul_le_mul_of_nonneg_right hpos.2.1 (sq_nonneg (v.ofLp r))]
  have hn : 0 < (n : ℝ) := by exact_mod_cast Nat.zero_lt_of_lt r.isLt
  have hScaled : (4 * (n : ℝ))⁻¹ ≤ (v.ofLp r)^2 + 4 * η^2 / Δ^2 := by
    change (4 * (n : ℝ) * η)⁻¹ ≤ f r at hselected
    calc
      _ = η * (4 * (n : ℝ) * η)⁻¹ := by field_simp
      _ ≤ η * (η⁻¹ * (v.ofLp r)^2 + 4 * η / Δ^2) :=
        mul_le_mul_of_nonneg_left (hselected.trans hScoreUpper) hη.le
      _ = _ := by field_simp
  have hSquare : (8 * (n : ℝ))⁻¹ ≤ (v.ofLp r)^2 := by
    have hConst : (4 * (n : ℝ))⁻¹ = 2 * (8 * (n : ℝ))⁻¹ := by
      field_simp
      norm_num
    linarith
  have hAbs : (Real.sqrt (8 * (n : ℝ)))⁻¹ ≤ |v.ofLp r| := by
    rw [← Real.sqrt_inv]
    exact (Real.sqrt_le_left (abs_nonneg _)).2 (by simpa only [sq_abs] using hSquare)
  have hCoeff : d.im * |v.ofLp r| ≤ ‖toLp 2 f‖ := by
    have hInner : inner ℝ v (toLp 2 f) = d.im * v.ofLp r := by
      exact (EuclideanSpace.inner_eq_star_dotProduct (𝕜 := ℝ) v (toLp 2 f)).trans
        (by simpa using hdreal)
    have h := abs_real_inner_le_norm v (toLp 2 f)
    rw [hInner, abs_mul, abs_of_nonneg hImNonneg, hv, one_mul] at h
    exact h
  have hSignal : |v.ofLp r| / (2 * η) ≤ ‖toLp 2 f‖ := by
    rw [div_eq_inv_mul]
    exact (mul_le_mul_of_nonneg_right hpos.1 (abs_nonneg _)).trans hCoeff
  have hUniform : (Real.sqrt (32 * (n : ℝ)) * η)⁻¹ ≤ ‖toLp 2 f‖ := by
    have hsqrt : Real.sqrt (32 * (n : ℝ)) = 2 * Real.sqrt (8 * (n : ℝ)) := by
      rw [show 32 * (n : ℝ) = 4 * (8 * (n : ℝ)) by ring, Real.sqrt_mul (by norm_num)]
      rw [show (4 : ℝ) = 2^2 by norm_num, Real.sqrt_sq (by norm_num : 0 ≤ (2 : ℝ))]
    rw [hsqrt, show (2 * Real.sqrt (8 * (n : ℝ)) * η)⁻¹ =
      (Real.sqrt (8 * (n : ℝ)))⁻¹ / (2 * η) by rw [div_eq_mul_inv, ← mul_inv]; ring_nf]
    exact (div_le_div_of_nonneg_right hAbs (by positivity)).trans hSignal
  have hProject : P.map Complex.ofReal *ᵥ g = g - (d * u r) • u := by
    have hp : P.map Complex.ofReal = 1 - Matrix.vecMulVec u u := by
      ext i k
      by_cases hik : i = k <;> simp [P, u, Matrix.vecMulVec_apply, hik]
    rw [hp, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.vecMulVec_mulVec,
      dotProduct_comm u g, hdcomp, op_smul_eq_smul]
  have hDecomp : toLp 2 g = toLp 2 (P.map Complex.ofReal *ᵥ g) + (d * u r) • toLp 2 u := by
    rw [hProject, ← WithLp.toLp_smul, ← WithLp.toLp_add, sub_add_cancel]
  have hTarget : ‖(d * u r) • toLp 2 u‖ ≤ Real.sqrt 2 * ‖toLp 2 f‖ := by
    rw [norm_smul, hu, mul_one, norm_mul, show ‖u r‖ = |v.ofLp r| by
      rw [show u r = (v.ofLp r : ℂ) from rfl, Complex.norm_real, Real.norm_eq_abs]]
    calc
      _ ≤ Real.sqrt 2 * d.im * |v.ofLp r| :=
        mul_le_mul_of_nonneg_right hpos.2.2 (abs_nonneg _)
      _ = Real.sqrt 2 * (d.im * |v.ofLp r|) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hCoeff (Real.sqrt_nonneg _)
  refine ⟨hAbs, hSignal, hUniform, ?_⟩
  calc
    ‖toLp 2 g‖ ≤ ‖toLp 2 (P.map Complex.ofReal *ᵥ g)‖ + ‖(d * u r) • toLp 2 u‖ := by
      rw [hDecomp]
      exact norm_add_le _ _
    _ ≤ _ := by linarith [hfiltered.2]

/-- Consequences of the shift-height and working-precision hypotheses. -/
theorem exactShiftPrecisionBounds {n η Δ u : ℝ} (hn : 1 ≤ n) (hη : 0 < η)
    (hΔ : 0 < Δ) (hu : 0 ≤ u) (hnu : n * u ≤ 1 / 128)
    (hprec : η ≤ Δ * Real.sqrt u / (16 * Real.sqrt (Real.sqrt n))) :
    η ≤ Δ / 2 ∧ 4 * η^2 / Δ^2 ≤ (8 * n)⁻¹ ∧
      32 * Real.sqrt (32 * n) * η ≤ Δ ∧ η^2 ≤ Δ^2 * u / (256 * Real.sqrt n) := by
  have hn0 : 0 < n := by linarith
  have hOne : Real.sqrt (32 * n) ≥ 1 := (Real.le_sqrt zero_le_one (by positivity)).2 (by
    nlinarith)
  have hscaled : η * (16 * Real.sqrt (Real.sqrt n)) ≤ Δ * Real.sqrt u :=
    (le_div_iff₀ (by positivity)).1 hprec
  have hηsq := (sq_le_sq₀ (by positivity) (by positivity)).2 hscaled
  rw [mul_pow, mul_pow (16 : ℝ), Real.sq_sqrt (Real.sqrt_nonneg _),
    mul_pow Δ, Real.sq_sqrt hu] at hηsq
  have hrootn : Real.sqrt n ≤ n :=
    (Real.sqrt_le_left hn0.le).2 (by nlinarith)
  have hnu' : 128 * Real.sqrt n * u ≤ 1 := by
    calc
      _ ≤ 128 * n * u := by gcongr
      _ ≤ 1 := by linarith
  have hscaleSq : (32 * Real.sqrt (32 * n) * η)^2 ≤ Δ^2 := by
    calc
      _ = 32768 * n * η^2 := by
        rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity : 0 ≤ 32 * n)]
        ring
      _ = 128 * Real.sqrt n * (η^2 * (16^2 * Real.sqrt n)) := by
        rw [show 128 * Real.sqrt n * (η^2 * (16^2 * Real.sqrt n)) =
          32768 * (Real.sqrt n)^2 * η^2 by ring, Real.sq_sqrt hn0.le]
      _ ≤ 128 * Real.sqrt n * (Δ^2 * u) :=
        mul_le_mul_of_nonneg_left hηsq (by positivity)
      _ = (128 * Real.sqrt n * u) * Δ^2 := by ring
      _ ≤ Δ^2 := by simpa using mul_le_mul_of_nonneg_right hnu' (sq_nonneg Δ)
  have hscale : 32 * Real.sqrt (32 * n) * η ≤ Δ :=
    (sq_le_sq₀ (by positivity) hΔ.le).1 hscaleSq
  refine ⟨?_, ?_, hscale, ?_⟩
  · have h := mul_le_mul_of_nonneg_right hOne hη.le
    linarith
  · rw [inv_eq_one_div, div_le_div_iff₀ (by positivity) (by positivity), one_mul]
    have h : 32768 * n * η^2 ≤ Δ^2 := by
      convert hscaleSq using 1
      rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity : 0 ≤ 32 * n)]
      ring
    nlinarith [mul_nonneg hn0.le (sq_nonneg η)]
  · exact (le_div_iff₀ (by positivity)).2 (by simpa only [show (16 : ℝ)^2 = 256 by norm_num] using hηsq)

/-- The selected exact resolvent column satisfies the signal and phase bounds of Section 6
under the paper's precision condition on the imaginary shift. -/
theorem exactResolventSelectedColumnPhase {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.IsSymm) (j r : Fin n) (v : EuclideanSpace ℝ (Fin n))
    (hv : ‖v‖ = 1)
    (heig : A *ᵥ v.ofLp = (MatrixResolvent.isHermitian_map_ofReal hA).eigenvalues j • v.ofLp)
    {shift η Δ u : ℝ} (hη : 0 < η) (hΔ : 0 < Δ) (hu : 0 ≤ u)
    (hnu : (n : ℝ) * u ≤ 1 / 128)
    (hprec : η ≤ Δ * Real.sqrt u / (16 * Real.sqrt (Real.sqrt (n : ℝ))))
    (hnear : |shift - (MatrixResolvent.isHermitian_map_ofReal hA).eigenvalues j| ≤ η)
    (hgap : ∀ i ≠ j, Δ ≤ |(MatrixResolvent.isHermitian_map_ofReal hA).eigenvalues i -
      (MatrixResolvent.isHermitian_map_ofReal hA).eigenvalues j|) :
    let G := (MatrixResolvent.imaginaryShift (A.map Complex.ofReal) shift η)⁻¹
    let g := G.col r
    let f := Complex.im ∘ g
    (4 * (n : ℝ) * η)⁻¹ ≤ (G r r).im →
      (Real.sqrt (8 * (n : ℝ)))⁻¹ ≤ |v.ofLp r| ∧
      |v.ofLp r| / (2 * η) ≤ ‖toLp 2 f‖ ∧
      (Real.sqrt (32 * (n : ℝ)) * η)⁻¹ ≤ ‖toLp 2 f‖ ∧
      ‖toLp 2 g‖ ≤ (Real.sqrt 2 + 1 / 16) * ‖toLp 2 f‖ ∧
      ‖toLp 2 g‖ < 2 * ‖toLp 2 f‖ := by
  intro G g f hselected
  have hn : 1 ≤ (n : ℝ) := by exact_mod_cast Nat.zero_lt_of_lt r.isLt
  obtain ⟨hηgap, hsmall, hScale, _⟩ := exactShiftPrecisionBounds hn hη hΔ hu hnu hprec
  obtain ⟨hVr, hSignal, hUniform, hPhase⟩ :=
    exactResolventSelectedColumnSignal hA j r v hv heig hη hΔ hηgap hnear hgap hsmall hselected
  have hn0 : 0 < (n : ℝ) := by linarith
  have hrecip : 32 / Δ ≤ (Real.sqrt (32 * (n : ℝ)) * η)⁻¹ := by
    rw [inv_eq_one_div, div_le_div_iff₀ hΔ (by positivity), one_mul]
    linarith
  change (Real.sqrt (32 * (n : ℝ)) * η)⁻¹ ≤ ‖toLp 2 f‖ at hUniform
  change ‖toLp 2 g‖ ≤ Real.sqrt 2 * ‖toLp 2 f‖ + 2 / Δ at hPhase
  have hPos : 0 < ‖toLp 2 f‖ := (by positivity : 0 < (Real.sqrt (32 * (n : ℝ)) * η)⁻¹).trans_le
    hUniform
  have hTail : 2 / Δ ≤ (1 / 16) * ‖toLp 2 f‖ := by
    calc
      2 / Δ = (1 / 16) * (32 / Δ) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (hrecip.trans hUniform) (by positivity)
  have hPhase' : ‖toLp 2 g‖ ≤ (Real.sqrt 2 + 1 / 16) * ‖toLp 2 f‖ := by
    calc
      _ ≤ Real.sqrt 2 * ‖toLp 2 f‖ + 2 / Δ := hPhase
      _ ≤ Real.sqrt 2 * ‖toLp 2 f‖ + (1 / 16) * ‖toLp 2 f‖ :=
        add_le_add le_rfl hTail
      _ = _ := by ring
  have hsqrt : Real.sqrt 2 ≤ 3 / 2 :=
    (Real.sqrt_le_left (by norm_num : 0 ≤ (3 : ℝ) / 2)).2 (by norm_num)
  have hlt : Real.sqrt 2 + 1 / 16 < (2 : ℝ) := by linarith
  exact ⟨hVr, hSignal, hUniform, hPhase', hPhase'.trans_lt (mul_lt_mul_of_pos_right hlt hPos)⟩

end NumStability.CertifiedTridiagonalEigenpairs
