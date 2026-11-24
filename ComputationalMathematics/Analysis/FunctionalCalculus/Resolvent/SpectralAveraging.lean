import ComputationalMathematics.Analysis.FunctionalCalculus.Resolvent.ImaginaryShift
import ComputationalMathematics.Analysis.FunctionalCalculus.Resolvent.RankOnePoissonIntegral
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Integral.Prod

/-! Spectral averaging for perturbations of one diagonal coordinate. -/

open Filter MeasureTheory
open scoped ENNReal NNReal Topology

namespace NumStability

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def diagonalRankOneResolventIm (A : Matrix ι ι ℂ) (i : ι)
    (y t E : ℝ) : ℝ :=
  ((A + Matrix.diagonal (Pi.single i (t : ℂ)) - ((E : ℂ) + y * Complex.I) • 1)⁻¹ i i).im

omit [Fintype ι] in
private theorem continuous_add_diagonal_single (A : Matrix ι ι ℂ) (i : ι) :
    Continuous (fun t : ℝ => A + Matrix.diagonal (Pi.single i (t : ℂ))) := by
  apply continuous_const.add
  apply Continuous.matrix_diagonal
  apply continuous_pi
  intro j
  by_cases h : j = i
  · subst j
    simpa only [Pi.single_eq_same] using Complex.continuous_ofReal
  · simp only [Pi.single_eq_of_ne h]
    exact continuous_const

theorem continuous_diagonalRankOneResolventIm {A : Matrix ι ι ℂ} (hA : A.IsHermitian)
    (i : ι) {y : ℝ} (hy : 0 < y) :
    Continuous (Function.uncurry (diagonalRankOneResolventIm A i y)) := by
  let M (p : ℝ × ℝ) : Matrix ι ι ℂ :=
    A + Matrix.diagonal (Pi.single i (p.1 : ℂ)) - ((p.2 : ℂ) + y * Complex.I) • 1
  have hM : Continuous M := by
    apply Continuous.sub
    · exact (continuous_add_diagonal_single A i).comp continuous_fst
    · exact ((Complex.continuous_ofReal.comp continuous_snd).add continuous_const).smul
        continuous_const
  have hInv : Continuous (fun p => (M p)⁻¹) := by
    rw [continuous_iff_continuousAt]
    intro p
    have hUnit : IsUnit (M p) := MatrixResolvent.isUnit_sub_smul_one
      (isHermitian_add_diagonal_single hA i p.1) (by simpa using hy.ne')
    have hDet : (M p).det ≠ 0 := ((M p).isUnit_iff_isUnit_det.mp hUnit).ne_zero
    have hi : ContinuousAt Ring.inverse (M p).det := by
      rw [Ring.inverse_eq_inv']
      exact continuousAt_id.inv₀ hDet
    exact (continuousAt_matrix_inv (M p) hi).comp hM.continuousAt
  exact Complex.continuous_im.comp (hInv.matrix_elem i i)

theorem diagonalRankOneResolventIm_nonneg {A : Matrix ι ι ℂ} (hA : A.IsHermitian)
    (i : ι) {y : ℝ} (hy : 0 < y) (t E : ℝ) :
    0 ≤ diagonalRankOneResolventIm A i y t E := by
  let z : ℂ := (E : ℂ) + y * Complex.I
  have hz : 0 < z.im := by simpa [z] using hy
  change 0 ≤ ((A + Matrix.diagonal (Pi.single i (t : ℂ)) - z • 1)⁻¹ i i).im
  rw [diagonal_rankOne_resolvent hA i _ hz, im_inv_ofReal_sub_eq_poissonKernel]
  exact poissonKernel_nonneg (hz.le.trans (le_im_coordinateResolventCenter hA i hz)) _ _

theorem lintegral_normalized_diagonalRankOneResolventIm
    {A : Matrix ι ι ℂ} (hA : A.IsHermitian) (i : ι) {y : ℝ} (hy : 0 < y) (E : ℝ) :
    ∫⁻ t : ℝ, ENNReal.ofReal (diagonalRankOneResolventIm A i y t E / Real.pi) = 1 := by
  have heq : ∫ t, diagonalRankOneResolventIm A i y t E = Real.pi :=
    integral_im_diagonal_rankOne_resolvent hA i (by simpa using hy)
  have hint : Integrable (fun t => diagonalRankOneResolventIm A i y t E) :=
    Integrable.of_integral_ne_zero (heq ▸ Real.pi_ne_zero)
  rw [← ofReal_integral_eq_lintegral_ofReal (hint.div_const _)
    (ae_of_all _ fun t => div_nonneg (diagonalRankOneResolventIm_nonneg hA i hy t E) Real.pi_pos.le)]
  rw [integral_div, heq, div_self Real.pi_ne_zero, ENNReal.ofReal_one]

theorem lintegral_lintegral_normalized_diagonalRankOneResolventIm
    {A : Matrix ι ι ℂ} (hA : A.IsHermitian) (i : ι) {y : ℝ} (hy : 0 < y)
    (s : Set ℝ) :
    ∫⁻ t : ℝ, ∫⁻ E in s, ENNReal.ofReal (diagonalRankOneResolventIm A i y t E / Real.pi) =
      volume s := by
  have hcont : Continuous (Function.uncurry fun t E =>
      ENNReal.ofReal (diagonalRankOneResolventIm A i y t E / Real.pi)) :=
    ENNReal.continuous_ofReal.comp
      ((continuous_diagonalRankOneResolventIm hA i hy).div_const _)
  rw [lintegral_lintegral_swap hcont.measurable.aemeasurable]
  simp only [lintegral_normalized_diagonalRankOneResolventIm hA i hy, lintegral_one,
    Measure.restrict_apply_univ]

/-- The spectral mass of the coordinate vector at the eigenvalues belonging to `s`. -/
noncomputable def coordinateSpectralWeight {A : Matrix ι ι ℂ} (hA : A.IsHermitian)
    (i : ι) (s : Set ℝ) : ℝ :=
  ∑ j, s.indicator (fun _ => Complex.normSq (hA.eigenvectorUnitary i j)) (hA.eigenvalues j)

private theorem im_inv_imaginaryShift_eq_sum_poissonKernel {A : Matrix ι ι ℂ}
    (hA : A.IsHermitian) (i : ι) {y : ℝ} (hy : 0 < y) (E : ℝ) :
    ((MatrixResolvent.imaginaryShift A E y)⁻¹ i i).im =
      ∑ j, Complex.normSq (hA.eigenvectorUnitary i j) * poissonKernel y (hA.eigenvalues j) E := by
  rw [MatrixResolvent.inv_imaginaryShift_diagonal_im_eq_sum hA E hy i]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [poissonKernel, show (E - hA.eigenvalues j) ^ 2 = (hA.eigenvalues j - E) ^ 2 by ring]

private theorem diagonalRankOneResolventIm_eq_sum {A : Matrix ι ι ℂ}
    (hA : A.IsHermitian) (i : ι) {y : ℝ} (hy : 0 < y) (t E : ℝ) :
    let hH := isHermitian_add_diagonal_single hA i t
    diagonalRankOneResolventIm A i y t E =
      ∑ j, Complex.normSq (hH.eigenvectorUnitary i j) * poissonKernel y (hH.eigenvalues j) E :=
  im_inv_imaginaryShift_eq_sum_poissonKernel (isHermitian_add_diagonal_single hA i t) i hy E

private noncomputable def averagingHeight (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)

private theorem averagingHeight_pos (n : ℕ) : 0 < averagingHeight n := by
  unfold averagingHeight
  positivity

private theorem tendsto_averagingHeight : Tendsto averagingHeight atTop (𝓝[>] 0) := by
  exact tendsto_nhdsWithin_iff.mpr ⟨tendsto_one_div_add_atTop_nhds_zero_nat,
    Eventually.of_forall averagingHeight_pos⟩

private theorem lintegral_diagonalRankOneResolventIm_Ioc_eq
    {A : Matrix ι ι ℂ} (hA : A.IsHermitian) (i : ι) {y : ℝ} (hy : 0 < y)
    {a b : ℝ} (hab : a ≤ b) (t : ℝ) :
    (∫⁻ E in Set.Ioc a b, ENNReal.ofReal (diagonalRankOneResolventIm A i y t E / Real.pi)) =
      ENNReal.ofReal ((∫ E in a..b, diagonalRankOneResolventIm A i y t E) / Real.pi) := by
  have hp : Continuous (fun E : ℝ => (t, E)) := by fun_prop
  have hcomp : Continuous ((Function.uncurry (diagonalRankOneResolventIm A i y)) ∘
      (fun E : ℝ => (t, E))) :=
    (continuous_diagonalRankOneResolventIm hA i hy).comp hp
  have hcont : Continuous (fun E => diagonalRankOneResolventIm A i y t E) := hcomp
  have hfi : IntegrableOn (fun E => diagonalRankOneResolventIm A i y t E / Real.pi)
      (Set.Ioc a b) := ((hcont.div_const Real.pi).intervalIntegrable a b).1
  have hnn : 0 ≤ᵐ[volume.restrict (Set.Ioc a b)]
      (fun E => diagonalRankOneResolventIm A i y t E / Real.pi) :=
    ae_of_all _ fun E => div_nonneg (diagonalRankOneResolventIm_nonneg hA i hy t E)
      Real.pi_pos.le
  rw [← intervalIntegral.integral_div, intervalIntegral.integral_of_le hab]
  exact (ofReal_integral_eq_lintegral_ofReal hfi hnn).symm

/-- The outer Lebesgue integral of the spectral weight is bounded by the length
of any interval that contains the spectral window in its interior. -/
theorem lintegral_coordinateSpectralWeight_le_of_subset_Ioo
    {A : Matrix ι ι ℂ} (hA : A.IsHermitian) (i : ι) {s : Set ℝ} {a b : ℝ}
    (hab : a ≤ b) (hs : s ⊆ Set.Ioo a b) :
    (∫⁻ t : ℝ, ENNReal.ofReal (coordinateSpectralWeight
      (isHermitian_add_diagonal_single hA i t) i s)) ≤ ENNReal.ofReal (b - a) := by
  let F (n : ℕ) (t : ℝ) :=
    ∫⁻ E in Set.Ioc a b, ENNReal.ofReal (diagonalRankOneResolventIm A i (averagingHeight n) t E /
      Real.pi)
  have hmeas (n : ℕ) : Measurable (F n) := by
    have hcont : Continuous (Function.uncurry fun t E =>
        ENNReal.ofReal (diagonalRankOneResolventIm A i (averagingHeight n) t E / Real.pi)) :=
      ENNReal.continuous_ofReal.comp
        ((continuous_diagonalRankOneResolventIm hA i (averagingHeight_pos n)).div_const _)
    exact hcont.measurable.lintegral_prod_right
  have hF (n : ℕ) : ∫⁻ t, F n t = ENNReal.ofReal (b - a) := by
    rw [← Real.volume_Ioc]
    exact lintegral_lintegral_normalized_diagonalRankOneResolventIm hA i (averagingHeight_pos n) _
  refine le_trans (b := ∫⁻ t, liminf (fun n => F n t) atTop) (lintegral_mono fun t => ?_) ?_
  · let hH := isHermitian_add_diagonal_single hA i t
    obtain ⟨L, hlim, hle⟩ := exists_tendsto_intervalIntegral_sum_poissonKernel
      hH.eigenvalues (fun j => Complex.normSq (hH.eigenvectorUnitary i j))
      (fun _ => Complex.normSq_nonneg _) hab hs
    have hlim' : Tendsto (fun n => F n t) atTop (𝓝 (ENNReal.ofReal (L / Real.pi))) := by
      refine (ENNReal.continuous_ofReal.continuousAt.tendsto.comp
        (((hlim.comp tendsto_averagingHeight).div_const Real.pi))).congr fun n => ?_
      dsimp only [Function.comp_apply, F]
      rw [lintegral_diagonalRankOneResolventIm_Ioc_eq hA i (averagingHeight_pos n) hab]
      simp only [diagonalRankOneResolventIm_eq_sum hA i (averagingHeight_pos n)]
    rw [hlim'.liminf_eq]
    apply ENNReal.ofReal_le_ofReal
    apply (le_div_iff₀ Real.pi_pos).mpr
    simpa only [coordinateSpectralWeight, mul_comm _ Real.pi] using hle
  · simpa only [hF, liminf_const] using lintegral_liminf_le (μ := volume) hmeas

/-- Rank-one spectral averaging for closed bounded intervals. -/
theorem lintegral_coordinateSpectralWeight_Icc_le
    {A : Matrix ι ι ℂ} (hA : A.IsHermitian) (i : ι) {a b : ℝ} (hab : a ≤ b) :
    (∫⁻ t : ℝ, ENNReal.ofReal (coordinateSpectralWeight
      (isHermitian_add_diagonal_single hA i t) i (Set.Icc a b))) ≤ ENNReal.ofReal (b - a) := by
  apply ENNReal.le_of_forall_pos_le_add
  intro ε hε _
  have hε' : 0 < (ε : ℝ) := by exact_mod_cast hε
  have hsub : Set.Icc a b ⊆ Set.Ioo (a - ε / 2) (b + ε / 2) := by
    intro x hx
    exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have h := lintegral_coordinateSpectralWeight_le_of_subset_Ioo hA i
    (show a - ε / 2 ≤ b + ε / 2 by linarith) hsub
  rwa [show b + ε / 2 - (a - ε / 2) = (b - a) + ε by ring,
    ENNReal.ofReal_add (sub_nonneg_of_le hab) hε'.le, ENNReal.ofReal_coe_nnreal] at h

private noncomputable def coordinateBoundaryWeight {A : Matrix ι ι ℂ} (hA : A.IsHermitian)
    (i : ι) (a b : ℝ) : ℝ :=
  ∑ j, Complex.normSq (hA.eigenvectorUnitary i j) *
    ((Real.sign (b - hA.eigenvalues j) - Real.sign (a - hA.eigenvalues j)) / 2)

section MeasurableParameters

variable {X : Type*} [MeasurableSpace X]

private theorem measurable_intervalIntegral_im_inv_imaginaryShift
    {M : X → Matrix ι ι ℂ} (hm : ∀ k l, Measurable (fun x => M x k l)) (i : ι) (y : ℝ)
    {a b : X → ℝ} (ha : Measurable a) (hb : Measurable b) (hab : ∀ x, a x ≤ b x) :
    Measurable (fun x => ∫ E in a x..b x, ((MatrixResolvent.imaginaryShift (M x) E y)⁻¹ i i).im) := by
  let D : Set (X × ℝ) := {p | p.2 ∈ Set.Ioc (a p.1) (b p.1)}
  let T (p : X × ℝ) : Matrix ι ι ℂ := MatrixResolvent.imaginaryShift (M p.1) p.2 y
  let R : X × ℝ → ℝ := fun p => ((T p)⁻¹ i i).im
  have hD : MeasurableSet D :=
    (measurableSet_lt (ha.comp measurable_fst) measurable_snd).inter
      (measurableSet_le measurable_snd (hb.comp measurable_fst))
  have hshift : Measurable (fun p : X × ℝ => fun k l => T p k l) := by
    refine measurable_pi_iff.mpr fun k => measurable_pi_iff.mpr fun l => ?_
    simp only [T, MatrixResolvent.imaginaryShift, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
    exact ((hm k l).comp measurable_fst).sub
      (((Complex.continuous_ofReal.measurable.comp measurable_snd).add measurable_const).mul
        measurable_const)
  have hMat : Continuous (Matrix.of : (ι → ι → ℂ) → Matrix ι ι ℂ) :=
    continuous_matrix fun k l => continuous_apply_apply k l
  have hdet : Measurable (fun p : X × ℝ => (T p).det) :=
    hMat.matrix_det.measurable.comp hshift
  have hadj : Measurable (fun p : X × ℝ => (T p).adjugate i i) :=
    (hMat.matrix_adjugate.matrix_elem i i).measurable.comp hshift
  have hR : Measurable R := by
    simp only [R, Matrix.inv_def, Ring.inverse_eq_inv, Matrix.smul_apply, smul_eq_mul]
    exact Complex.continuous_im.measurable.comp (hdet.inv.mul hadj)
  have h := ((hR.indicator hD).stronglyMeasurable.integral_prod_right'
    (ν := (volume : Measure ℝ))).measurable
  convert h using 1
  ext x
  rw [intervalIntegral.integral_of_le (hab x), ← integral_indicator measurableSet_Ioc]
  congr 1

private theorem measurable_coordinateBoundaryWeight_comp
    {M : X → Matrix ι ι ℂ} (hm : ∀ k l, Measurable (fun x => M x k l))
    (hM : ∀ x, (M x).IsHermitian) (i : ι)
    {a b : X → ℝ} (ha : Measurable a) (hb : Measurable b) (hab : ∀ x, a x ≤ b x) :
    Measurable (fun x => coordinateBoundaryWeight (hM x) i (a x) (b x)) := by
  let G (n : ℕ) (x : X) :=
    (∫ E in a x..b x, ((MatrixResolvent.imaginaryShift (M x) E (averagingHeight n))⁻¹ i i).im) /
      Real.pi
  apply measurable_of_tendsto_metrizable (f := G)
  · intro n
    exact (measurable_intervalIntegral_im_inv_imaginaryShift hm i (averagingHeight n)
      ha hb hab).div_const Real.pi
  · apply tendsto_pi_nhds.mpr
    intro x
    let hH := hM x
    have hlim := tendsto_intervalIntegral_sum_poissonKernel hH.eigenvalues
      (fun j => Complex.normSq (hH.eigenvectorUnitary i j)) (a x) (b x)
    have hnorm :
        (∑ j, Complex.normSq (hH.eigenvectorUnitary i j) *
          ((Real.sign (b x - hH.eigenvalues j) - Real.sign (a x - hH.eigenvalues j)) *
            (Real.pi / 2))) / Real.pi = coordinateBoundaryWeight hH i (a x) (b x) := by
      rw [coordinateBoundaryWeight, Finset.sum_div]
      refine Finset.sum_congr rfl fun j _ => ?_
      field_simp [Real.pi_ne_zero]
    rw [← hnorm]
    refine ((hlim.comp tendsto_averagingHeight).div_const Real.pi).congr fun n => ?_
    simp only [G, Function.comp_apply,
      im_inv_imaginaryShift_eq_sum_poissonKernel hH i (averagingHeight_pos n)]

end MeasurableParameters

private theorem eventually_interval_sign_eq_Icc_indicator {a b : ℝ} (hab : a ≤ b) (c : ℝ) :
    ∀ᶠ ε : ℝ in 𝓝[>] 0,
      (Real.sign (b + ε - c) - Real.sign (a - ε - c)) / 2 =
        (Set.Icc a b).indicator (fun _ => (1 : ℝ)) c := by
  by_cases hc : c ∈ Set.Icc a b
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    have hpos : 0 < ε := Set.mem_Ioi.mp hε
    have hb' : 0 < b + ε - c := by linarith [hc.2]
    have ha' : a - ε - c < 0 := by linarith [hc.1]
    norm_num [Set.indicator_of_mem hc, Real.sign_of_pos hb', Real.sign_of_neg ha']
  · have hout : c < a ∨ b < c := by simpa only [Set.mem_Icc, not_and_or, not_le] using hc
    rcases hout with ha | hb
    · filter_upwards [self_mem_nhdsWithin,
        (eventually_lt_nhds (sub_pos.mpr ha)).filter_mono nhdsWithin_le_nhds] with ε hε hεa
      have hpos : 0 < ε := Set.mem_Ioi.mp hε
      have hb' : 0 < b + ε - c := by linarith
      have ha' : 0 < a - ε - c := by linarith
      simp [Set.indicator_of_notMem hc, Real.sign_of_pos hb', Real.sign_of_pos ha']
    · filter_upwards [self_mem_nhdsWithin,
        (eventually_lt_nhds (sub_pos.mpr hb)).filter_mono nhdsWithin_le_nhds] with ε hε hεb
      have hpos : 0 < ε := Set.mem_Ioi.mp hε
      have hb' : b + ε - c < 0 := by linarith
      have ha' : a - ε - c < 0 := by linarith
      simp [Set.indicator_of_notMem hc, Real.sign_of_neg hb', Real.sign_of_neg ha']

/-- The closed-window coordinate spectral weight is measurable jointly in
the Hermitian matrix entries and the two interval endpoints. -/
theorem measurable_coordinateSpectralWeight_Icc_comp
    {X : Type*} [MeasurableSpace X] {M : X → Matrix ι ι ℂ}
    (hm : ∀ k l, Measurable (fun x => M x k l))
    (hM : ∀ x, (M x).IsHermitian) (i : ι)
    {a b : X → ℝ} (ha : Measurable a) (hb : Measurable b) (hab : ∀ x, a x ≤ b x) :
    Measurable (fun x => coordinateSpectralWeight (hM x) i (Set.Icc (a x) (b x))) := by
  apply measurable_of_tendsto_metrizable (f := fun n x => coordinateBoundaryWeight
    (hM x) i (a x - averagingHeight n) (b x + averagingHeight n))
  · intro n
    refine measurable_coordinateBoundaryWeight_comp hm hM i (ha.sub measurable_const)
      (hb.add measurable_const) fun x => ?_
    linarith [hab x, averagingHeight_pos n]
  · apply tendsto_pi_nhds.mpr
    intro x
    let hH := hM x
    unfold coordinateBoundaryWeight coordinateSpectralWeight
    refine tendsto_finset_sum Finset.univ (fun j _ => ?_)
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [tendsto_averagingHeight.eventually
      (eventually_interval_sign_eq_Icc_indicator (hab x) (hH.eigenvalues j))] with n hn
    change _ = Complex.normSq (hH.eigenvectorUnitary i j) * _
    rw [hn]
    by_cases hj : hH.eigenvalues j ∈ Set.Icc (a x) (b x)
    · simp only [Set.indicator_of_mem hj, mul_one]
    · simp only [Set.indicator_of_notMem hj, mul_zero]

/-- Spectral weights of closed intervals vary measurably with the rank-one perturbation. -/
theorem measurable_coordinateSpectralWeight_Icc
    {A : Matrix ι ι ℂ} (hA : A.IsHermitian) (i : ι) {a b : ℝ} (hab : a ≤ b) :
    Measurable (fun t : ℝ => coordinateSpectralWeight
      (isHermitian_add_diagonal_single hA i t) i (Set.Icc a b)) :=
  measurable_coordinateSpectralWeight_Icc_comp
    (fun k l => ((continuous_add_diagonal_single A i).matrix_elem k l).measurable)
    (fun t => isHermitian_add_diagonal_single hA i t) i measurable_const measurable_const
    (fun _ => hab)

theorem coordinateSpectralWeight_nonneg {A : Matrix ι ι ℂ} (hA : A.IsHermitian)
    (i : ι) (s : Set ℝ) : 0 ≤ coordinateSpectralWeight hA i s := by
  unfold coordinateSpectralWeight
  apply Finset.sum_nonneg
  intro j _
  by_cases hj : hA.eigenvalues j ∈ s
  · simpa only [Set.indicator_of_mem hj] using Complex.normSq_nonneg (hA.eigenvectorUnitary i j)
  · simp only [Set.indicator_of_notMem hj, le_rfl]

private theorem integral_le_of_lintegral_ofReal_le {μ : Measure ℝ} {f : ℝ → ℝ}
    (hm : Measurable f) (hnn : ∀ t, 0 ≤ f t) {r : ℝ} (hr : 0 ≤ r)
    (h : ∫⁻ t, ENNReal.ofReal (f t) ∂μ ≤ ENNReal.ofReal r) :
    ∫ t, f t ∂μ ≤ r := by
  have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top h
  rwa [← integral_eq_lintegral_of_nonneg_ae (ae_of_all _ hnn) hm.aestronglyMeasurable,
    ENNReal.toReal_ofReal hr] at hreal

/-- The integral of the coordinate spectral weight over all real perturbations
is at most the length of the closed interval. -/
theorem integral_coordinateSpectralWeight_Icc_le
    {A : Matrix ι ι ℂ} (hA : A.IsHermitian) (i : ι) {a b : ℝ} (hab : a ≤ b) :
    (∫ t : ℝ, coordinateSpectralWeight (isHermitian_add_diagonal_single hA i t)
      i (Set.Icc a b)) ≤ b - a :=
  integral_le_of_lintegral_ofReal_le (measurable_coordinateSpectralWeight_Icc hA i hab)
    (fun t => coordinateSpectralWeight_nonneg (isHermitian_add_diagonal_single hA i t) i _)
    (sub_nonneg.mpr hab) (lintegral_coordinateSpectralWeight_Icc_le hA i hab)

private theorem integral_withDensity_le_of_lintegral_ofReal_le
    {f : ℝ → ℝ} (hf : Measurable f) (hnn : ∀ t, 0 ≤ f t)
    {r : ℝ} (hr : 0 ≤ r) (hb : ∫⁻ t, ENNReal.ofReal (f t) ≤ ENNReal.ofReal r)
    {density : ℝ → ℝ≥0∞} (hd : Measurable density) (ρ : ℝ≥0)
    (hρ : ∀ᵐ t ∂volume, density t ≤ (ρ : ℝ≥0∞)) :
    (∫ t, f t ∂volume.withDensity density) ≤ (ρ : ℝ) * r := by
  refine integral_le_of_lintegral_ofReal_le hf hnn (mul_nonneg ρ.coe_nonneg hr) ?_
  rw [lintegral_withDensity_eq_lintegral_mul volume hd hf.ennreal_ofReal,
    ENNReal.ofReal_mul ρ.coe_nonneg, ENNReal.ofReal_coe_nnreal]
  calc
    _ ≤ ∫⁻ t, (ρ : ℝ≥0∞) * ENNReal.ofReal (f t) := by
      apply lintegral_mono_ae
      filter_upwards [hρ] with t ht
      exact mul_le_mul_left ht _
    _ = (ρ : ℝ≥0∞) * ∫⁻ t, ENNReal.ofReal (f t) :=
      lintegral_const_mul _ hf.ennreal_ofReal
    _ ≤ _ := mul_le_mul_right hb _

/-- A perturbation with a density bounded by `ρ` has expected spectral weight
at most `ρ` times the closed interval length. -/
theorem integral_coordinateSpectralWeight_Icc_withDensity_le
    {A : Matrix ι ι ℂ} (hA : A.IsHermitian) (i : ι) {a b : ℝ} (hab : a ≤ b)
    {density : ℝ → ℝ≥0∞} (hd : Measurable density) (ρ : ℝ≥0)
    (hρ : ∀ᵐ t ∂volume, density t ≤ (ρ : ℝ≥0∞)) :
    (∫ t : ℝ, coordinateSpectralWeight (isHermitian_add_diagonal_single hA i t)
      i (Set.Icc a b) ∂volume.withDensity density) ≤ (ρ : ℝ) * (b - a) :=
  integral_withDensity_le_of_lintegral_ofReal_le
    (measurable_coordinateSpectralWeight_Icc hA i hab)
    (fun t => coordinateSpectralWeight_nonneg (isHermitian_add_diagonal_single hA i t) i _)
    (sub_nonneg.mpr hab) (lintegral_coordinateSpectralWeight_Icc_le hA i hab) hd ρ hρ

theorem coordinateSpectralWeight_mono {A : Matrix ι ι ℂ} (hA : A.IsHermitian)
    (i : ι) {s u : Set ℝ} (hs : s ⊆ u) :
    coordinateSpectralWeight hA i s ≤ coordinateSpectralWeight hA i u := by
  unfold coordinateSpectralWeight
  apply Finset.sum_le_sum
  intro j _
  by_cases hj : hA.eigenvalues j ∈ s
  · rw [Set.indicator_of_mem hj, Set.indicator_of_mem (hs hj)]
  · rw [Set.indicator_of_notMem hj]
    by_cases hu : hA.eigenvalues j ∈ u
    · rw [Set.indicator_of_mem hu]
      exact Complex.normSq_nonneg _
    · rw [Set.indicator_of_notMem hu]

/-- Any interval between its open and closed endpoints has measurable spectral weight. -/
theorem measurable_coordinateSpectralWeight_of_Ioo_subset
    {A : Matrix ι ι ℂ} (hA : A.IsHermitian) (i : ι) {a b : ℝ} (hab : a ≤ b)
    {s : Set ℝ} (hs₁ : Set.Ioo a b ⊆ s) (hs₂ : s ⊆ Set.Icc a b) :
    Measurable (fun t : ℝ => coordinateSpectralWeight
      (isHermitian_add_diagonal_single hA i t) i s) := by
  classical
  rcases lt_or_eq_of_le hab with hlt | rfl
  · let l : ℝ := if a ∈ s then 0 else 1
    let r : ℝ := if b ∈ s then 0 else 1
    have heq (t : ℝ) :
        let hH := isHermitian_add_diagonal_single hA i t
        coordinateSpectralWeight hH i s = coordinateSpectralWeight hH i (Set.Icc a b) -
          l * coordinateSpectralWeight hH i (Set.Icc a a) -
          r * coordinateSpectralWeight hH i (Set.Icc b b) := by
      let hH := isHermitian_add_diagonal_single hA i t
      change coordinateSpectralWeight hH i s = _
      unfold coordinateSpectralWeight
      simp only [Finset.mul_sum, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro j _
      let x := hH.eigenvalues j
      change s.indicator _ x = (Set.Icc a b).indicator _ x -
        l * (Set.Icc a a).indicator _ x - r * (Set.Icc b b).indicator _ x
      by_cases hxa : x = a
      · rw [hxa]
        by_cases ha : a ∈ s <;>
          simp [l, ha, Set.indicator, Set.mem_Icc, hab, hlt.ne]
      · by_cases hxb : x = b
        · rw [hxb]
          by_cases hb : b ∈ s <;>
            simp [r, hb, Set.indicator, Set.mem_Icc, hab, hlt.ne']
        · have hx : x ∈ s ↔ x ∈ Set.Icc a b := by
            refine ⟨fun h => hs₂ h, fun h => hs₁ ?_⟩
            exact ⟨h.1.lt_of_ne (Ne.symm hxa), h.2.lt_of_ne hxb⟩
          simp [Set.indicator, hx, Set.Icc_self, hxa, hxb]
    simp_rw [heq]
    exact ((measurable_coordinateSpectralWeight_Icc hA i hab).sub
      ((measurable_coordinateSpectralWeight_Icc hA i (a := a) le_rfl).const_mul l)).sub
      ((measurable_coordinateSpectralWeight_Icc hA i (a := b) le_rfl).const_mul r)
  · rw [Set.Icc_self] at hs₂
    by_cases ha : a ∈ s
    · have hs : s = {a} := hs₂.antisymm (Set.singleton_subset_iff.mpr ha)
      rw [hs, ← Set.Icc_self]
      exact measurable_coordinateSpectralWeight_Icc hA i le_rfl
    · have hs : s = ∅ := Set.eq_empty_iff_forall_notMem.mpr fun x hx =>
        ha ((Set.mem_singleton_iff.mp (hs₂ hx)) ▸ hx)
      simp only [hs, coordinateSpectralWeight, Set.indicator_empty,
        Finset.sum_const_zero]
      exact measurable_const

private theorem volume_eq_of_Ioo_subset_of_subset_Icc {a b : ℝ} {s : Set ℝ}
    (hs₁ : Set.Ioo a b ⊆ s) (hs₂ : s ⊆ Set.Icc a b) :
    volume s = ENNReal.ofReal (b - a) := by
  apply le_antisymm
  · simpa only [Real.volume_Icc] using measure_mono (μ := volume) hs₂
  · simpa only [Real.volume_Ioo] using measure_mono (μ := volume) hs₁

/-- Rank-one spectral averaging for any bounded interval with endpoints `a`
and `b`, with any choice to include or exclude either endpoint. -/
theorem integral_coordinateSpectralWeight_interval_le
    {A : Matrix ι ι ℂ} (hA : A.IsHermitian) (i : ι) {a b : ℝ} (hab : a ≤ b)
    {s : Set ℝ} (hs₁ : Set.Ioo a b ⊆ s) (hs₂ : s ⊆ Set.Icc a b) :
    (∫ t : ℝ, coordinateSpectralWeight (isHermitian_add_diagonal_single hA i t) i s) ≤
      (volume s).toReal := by
  rw [volume_eq_of_Ioo_subset_of_subset_Icc hs₁ hs₂,
    ENNReal.toReal_ofReal (sub_nonneg.mpr hab)]
  refine integral_le_of_lintegral_ofReal_le
    (measurable_coordinateSpectralWeight_of_Ioo_subset hA i hab hs₁ hs₂)
    (fun t => coordinateSpectralWeight_nonneg (isHermitian_add_diagonal_single hA i t) i s)
    (sub_nonneg.mpr hab) ?_
  exact (lintegral_mono fun t => ENNReal.ofReal_le_ofReal
    (coordinateSpectralWeight_mono (isHermitian_add_diagonal_single hA i t) i hs₂)).trans
      (lintegral_coordinateSpectralWeight_Icc_le hA i hab)

/-- Bounded-density spectral averaging for any bounded interval. -/
theorem integral_coordinateSpectralWeight_interval_withDensity_le
    {A : Matrix ι ι ℂ} (hA : A.IsHermitian) (i : ι) {a b : ℝ} (hab : a ≤ b)
    {s : Set ℝ} (hs₁ : Set.Ioo a b ⊆ s) (hs₂ : s ⊆ Set.Icc a b)
    {density : ℝ → ℝ≥0∞} (hd : Measurable density) (ρ : ℝ≥0)
    (hρ : ∀ᵐ t ∂volume, density t ≤ (ρ : ℝ≥0∞)) :
    (∫ t : ℝ, coordinateSpectralWeight (isHermitian_add_diagonal_single hA i t) i s
      ∂volume.withDensity density) ≤ (ρ : ℝ) * (volume s).toReal := by
  rw [volume_eq_of_Ioo_subset_of_subset_Icc hs₁ hs₂, ENNReal.toReal_ofReal (sub_nonneg.mpr hab)]
  refine integral_withDensity_le_of_lintegral_ofReal_le
    (measurable_coordinateSpectralWeight_of_Ioo_subset hA i hab hs₁ hs₂)
    (fun t => coordinateSpectralWeight_nonneg (isHermitian_add_diagonal_single hA i t) i s)
    (sub_nonneg.mpr hab) ?_ hd ρ hρ
  exact (lintegral_mono fun t => ENNReal.ofReal_le_ofReal
    (coordinateSpectralWeight_mono (isHermitian_add_diagonal_single hA i t) i hs₂)).trans
      (lintegral_coordinateSpectralWeight_Icc_le hA i hab)

/-- Conditioning fixes the matrix and interval at each value of the
conditioning variable. A bounded density for the conditional law then gives
the spectral averaging bound at almost every such value. -/
theorem ae_integral_coordinateSpectralWeight_interval_le_of_conditional_density
    {X : Type*} [MeasurableSpace X] {ν : Measure X} {κ : X → Measure ℝ}
    {A : X → Matrix ι ι ℂ} (hA : ∀ x, (A x).IsHermitian) (i : ι)
    {a b : X → ℝ} {s : X → Set ℝ}
    (hab : ∀ x, a x ≤ b x) (hs₁ : ∀ x, Set.Ioo (a x) (b x) ⊆ s x)
    (hs₂ : ∀ x, s x ⊆ Set.Icc (a x) (b x)) (ρ : ℝ≥0)
    (hκ : ∀ᵐ x ∂ν, ∃ density : ℝ → ℝ≥0∞, Measurable density ∧
      (∀ᵐ t ∂volume, density t ≤ (ρ : ℝ≥0∞)) ∧ κ x = volume.withDensity density) :
    ∀ᵐ x ∂ν,
      (∫ t : ℝ, coordinateSpectralWeight (isHermitian_add_diagonal_single (hA x) i t) i (s x)
        ∂κ x) ≤ (ρ : ℝ) * (volume (s x)).toReal := by
  filter_upwards [hκ] with x hx
  obtain ⟨density, hd, hρ, hμ⟩ := hx
  rw [hμ]
  exact integral_coordinateSpectralWeight_interval_withDensity_le (hA x) i
    (hab x) (hs₁ x) (hs₂ x) hd ρ hρ

/-- The spectral projection obtained using the indicator of a set of eigenvalues. -/
noncomputable def matrixSpectralProjection {A : Matrix ι ι ℂ} (hA : A.IsHermitian)
    (s : Set ℝ) : Matrix ι ι ℂ :=
  Unitary.conjStarAlgAut ℂ _ hA.eigenvectorUnitary
    (Matrix.diagonal fun j => s.indicator (fun _ => (1 : ℂ)) (hA.eigenvalues j))

/-- The coordinate spectral weight is the diagonal entry of the spectral projection. -/
theorem matrixSpectralProjection_apply_diag {A : Matrix ι ι ℂ} (hA : A.IsHermitian)
    (s : Set ℝ) (i : ι) :
    matrixSpectralProjection hA s i i = (coordinateSpectralWeight hA i s : ℂ) := by
  rw [matrixSpectralProjection, coordinateSpectralWeight, Unitary.conjStarAlgAut_apply,
    Matrix.mul_apply, Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [Matrix.mul_diagonal, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply]
  by_cases hj : hA.eigenvalues j ∈ s
  · simp only [Set.indicator_of_mem hj, mul_one, Complex.star_def, Complex.mul_conj]
  · simp [Set.indicator_of_notMem hj]

end NumStability
