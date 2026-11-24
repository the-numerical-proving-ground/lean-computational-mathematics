import ComputationalMathematics.Source.CertifiedTridiagonalEigenpairs.SpecifiedAdjacentGap.Target
import ComputationalMathematics.Analysis.Eigenvalues.DiagonalPerturbation.Continuity
import ComputationalMathematics.Analysis.FunctionalCalculus.Resolvent.SpectralAveraging

/-! Interlacing and one-coordinate spectral averaging at a specified gap. -/

open MeasureTheory Filter
open scoped BigOperators ENNReal Topology

namespace NumStability.CertifiedTridiagonalEigenpairs

open Matrix.IsHermitian

private noncomputable def deletedEigenvalue {n : ℕ}
    {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} (hH : H.IsHermitian)
    (i : Fin (n + 1)) (j : Fin n) : ℝ :=
  (hH.submatrix i.succAbove).orderedEigenvaluesFin j.rev

private noncomputable def gapProjectionWeight {n : ℕ}
    {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} (hH : H.IsHermitian)
    (i : Fin (n + 1)) (j : Fin n) (g : ℝ) : ℝ :=
  coordinateSpectralWeight hH i (Set.Icc (deletedEigenvalue hH i j - g)
    (deletedEigenvalue hH i j + g))

private theorem submatrix_diagonalPerturbation {n : ℕ}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (v : Fin (n + 1) → ℝ) (i : Fin (n + 1)) :
    (A.diagonalPerturbation v).submatrix i.succAbove i.succAbove =
      (A.submatrix i.succAbove i.succAbove).diagonalPerturbation (fun k => v (i.succAbove k)) := by
  ext k l
  simp [Matrix.diagonalPerturbation, Matrix.diagonal_apply, Fin.succAbove_right_injective.eq_iff]

private theorem continuous_deletedEigenvalue {n : ℕ}
    {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} (hA : A.IsHermitian)
    (i : Fin (n + 1)) (j : Fin n) :
    Continuous (fun v => deletedEigenvalue (hA.diagonalPerturbation v) i j) := by
  have h := (continuous_orderedEigenvaluesFin_diagonalPerturbation
    (hA.submatrix i.succAbove) j.rev).comp
    (show Continuous (fun v : Fin (n + 1) → ℝ => fun k : Fin n => v (i.succAbove k)) from
      continuous_pi (fun k => continuous_apply (i.succAbove k)))
  convert h using 1
  funext v
  unfold deletedEigenvalue
  generalize_proofs h₁ h₂
  congr 1
  exact submatrix_diagonalPerturbation _ _ _

private theorem measurable_gapProjectionWeight {n : ℕ}
    {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} (hA : A.IsHermitian)
    (i : Fin (n + 1)) (j : Fin n) {g : ℝ} (hg : 0 ≤ g) :
    Measurable (fun v => gapProjectionWeight (hA.diagonalPerturbation v) i j g) := by
  have hm := (continuous_deletedEigenvalue hA i j).measurable
  have he (k l : Fin (n + 1)) : Measurable (fun v => A.diagonalPerturbation v k l) := by
    by_cases h : k = l
    · subst l
      simpa [Matrix.diagonalPerturbation] using
        (measurable_const (a := A k k)).add
          (Complex.continuous_ofReal.measurable.comp (measurable_pi_apply k))
    · simp [Matrix.diagonalPerturbation, Matrix.diagonal_apply_ne _ h]
  exact measurable_coordinateSpectralWeight_Icc_comp he hA.diagonalPerturbation i
    (hm.sub measurable_const) (hm.add measurable_const) (fun v => by linarith)

private theorem sum_normSq_eigenvectorUnitary {N : ℕ}
    {H : Matrix (Fin N) (Fin N) ℂ} (hH : H.IsHermitian) (j : Fin N) :
    ∑ i, Complex.normSq (hH.eigenvectorUnitary i j) = 1 := by
  simp only [eigenvectorUnitary_apply, Complex.normSq_eq_norm_sq]
  rw [← EuclideanSpace.norm_sq_eq, hH.eigenvectorBasis.norm_eq_one, one_pow]

private theorem two_le_sum_gapProjectionWeight {n : ℕ}
    {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} (hH : H.IsHermitian)
    (j : Fin n) (g : ℝ)
    (hgap : hH.orderedEigenvaluesFin j.rev.castSucc - hH.orderedEigenvaluesFin j.rev.succ ≤ g) :
    2 ≤ ∑ i, gapProjectionWeight hH i j g := by
  let low := eigenbasisIndexFin (n + 1) j.rev.succ
  let high := eigenbasisIndexFin (n + 1) j.rev.castSucc
  have hne : low ≠ high := by
    intro h
    have he := (eigenbasisIndexFin (n + 1)).injective h
    have hv := congrArg Fin.val he
    simp only [Fin.val_succ, Fin.val_castSucc] at hv
    omega
  have hbound (i : Fin (n + 1)) : Complex.normSq (hH.eigenvectorUnitary i low) +
      Complex.normSq (hH.eigenvectorUnitary i high) ≤ gapProjectionWeight hH i j g := by
    let μ := deletedEigenvalue hH i j
    let I := Set.Icc (μ - g) (μ + g)
    obtain ⟨hlo, hhi⟩ := hH.orderedEigenvaluesFin_submatrix_interlace i j.rev
    change hH.orderedEigenvaluesFin j.rev.succ ≤ μ at hlo
    change μ ≤ hH.orderedEigenvaluesFin j.rev.castSucc at hhi
    have hloI : hH.eigenvalues low ∈ I := by
      rw [show hH.eigenvalues low = hH.orderedEigenvaluesFin j.rev.succ from
        hH.eigenvalues_eigenbasisIndexFin _]
      exact ⟨by linarith, by linarith⟩
    have hhiI : hH.eigenvalues high ∈ I := by
      rw [show hH.eigenvalues high = hH.orderedEigenvaluesFin j.rev.castSucc from
        hH.eigenvalues_eigenbasisIndexFin _]
      exact ⟨by linarith, by linarith⟩
    let term (k : Fin (n + 1)) :=
      I.indicator (fun _ => Complex.normSq (hH.eigenvectorUnitary i k)) (hH.eigenvalues k)
    have hnonneg (k : Fin (n + 1)) : 0 ≤ term k :=
      Set.indicator_nonneg (fun _ _ => Complex.normSq_nonneg _) _
    calc
      _ = ∑ k ∈ ({low, high} : Finset (Fin (n + 1))), term k := by
        rw [Finset.sum_insert (by simpa using hne), Finset.sum_singleton]
        simp [term, hloI, hhiI]
      _ ≤ ∑ k, term k := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun k _ _ => hnonneg k)
      _ = _ := rfl
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hbound i)
  rwa [Finset.sum_add_distrib, sum_normSq_eigenvectorUnitary, sum_normSq_eigenvectorUnitary,
    one_add_one_eq_two] at hsum

private theorem diagonalPerturbation_insertNth {n : ℕ}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (i : Fin (n + 1)) (u : Fin n → ℝ) (t : ℝ) :
    A.diagonalPerturbation (i.insertNth t u) =
      A.diagonalPerturbation (i.insertNth 0 u) + Matrix.diagonal (Pi.single i (t : ℂ)) := by
  ext k l
  by_cases hkl : k = l
  · subst l
    cases k using Fin.succAboveCases i
    · simp [Matrix.diagonalPerturbation]
    · simp [Matrix.diagonalPerturbation]
  · simp [Matrix.diagonalPerturbation, Matrix.diagonal_apply_ne _ hkl]

private theorem lintegral_gapProjectionWeight_le {n : ℕ}
    {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} (hA : A.IsHermitian)
    (f : Fin (n + 1) → ℝ → ℝ≥0∞) (hf : ∀ i, Measurable (f i))
    (hnorm : ∀ i, IsProbabilityMeasure ((volume : Measure ℝ).withDensity (f i)))
    (ρ : ℝ) (hρ : ∀ i, ∀ᵐ t ∂(volume : Measure ℝ), f i t ≤ ENNReal.ofReal ρ)
    (i : Fin (n + 1)) (j : Fin n) {g : ℝ} (hg : 0 < g) :
    (∫⁻ v, ENNReal.ofReal (gapProjectionWeight (hA.diagonalPerturbation v) i j g)
      ∂Measure.pi (fun k => (volume : Measure ℝ).withDensity (f k))) ≤
      ENNReal.ofReal ρ * ENNReal.ofReal (2 * g) := by
  let law (k : Fin (n + 1)) := (volume : Measure ℝ).withDensity (f k)
  letI (k : Fin (n + 1)) : IsProbabilityMeasure (law k) := hnorm k
  let e := (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) i).symm
  let W (v : Fin (n + 1) → ℝ) := ENNReal.ofReal (gapProjectionWeight (hA.diagonalPerturbation v) i j g)
  have hm : Measurable W := (measurable_gapProjectionWeight hA i j hg.le).ennreal_ofReal
  have he := (measurePreserving_piFinSuccAbove law i).symm e.symm
  change (∫⁻ v, W v ∂Measure.pi law) ≤ _
  rw [he.lintegral_map_equiv W e]
  have hW : Measurable (fun p => W (e p)) := hm.comp e.measurable
  rw [lintegral_prod_symm _ hW.aemeasurable]
  calc
    _ ≤ ∫⁻ _ : Fin n → ℝ, ENNReal.ofReal ρ * ENNReal.ofReal (2 * g)
        ∂Measure.pi (fun k => law (i.succAbove k)) := by
      refine lintegral_mono (fun u => ?_)
      let hB := hA.diagonalPerturbation (i.insertNth 0 u)
      let m := (hA.submatrix i.succAbove).diagonalPerturbation u
      let μ := m.orderedEigenvaluesFin j.rev
      have hab : μ - g ≤ μ + g := by linarith
      have hw (t : ℝ) : W (e (t, u)) =
          ENNReal.ofReal (coordinateSpectralWeight (isHermitian_add_diagonal_single hB i t)
            i (Set.Icc (μ - g) (μ + g))) := by
        change ENNReal.ofReal (gapProjectionWeight (hA.diagonalPerturbation (i.insertNth t u)) i j g) = _
        have hμ : deletedEigenvalue (hA.diagonalPerturbation (i.insertNth t u)) i j = μ := by
          unfold deletedEigenvalue μ m
          generalize_proofs h₁ h₂
          congr 1
          rw [submatrix_diagonalPerturbation]
          simp only [Fin.insertNth_apply_succAbove]
        rw [gapProjectionWeight, hμ]
        congr 2
        exact diagonalPerturbation_insertNth A i u t
      simp_rw [hw]
      have hmeas := (measurable_coordinateSpectralWeight_Icc hB i hab).ennreal_ofReal
      change (∫⁻ _, _ ∂(volume : Measure ℝ).withDensity (f i)) ≤ _
      rw [lintegral_withDensity_eq_lintegral_mul volume (hf i) hmeas]
      calc
        _ ≤ ∫⁻ t, ENNReal.ofReal ρ *
            ENNReal.ofReal (coordinateSpectralWeight (isHermitian_add_diagonal_single hB i t)
              i (Set.Icc (μ - g) (μ + g))) := by
          apply lintegral_mono_ae
          filter_upwards [hρ i] with t ht
          exact mul_le_mul_left ht _
        _ = ENNReal.ofReal ρ * ∫⁻ t,
            ENNReal.ofReal (coordinateSpectralWeight (isHermitian_add_diagonal_single hB i t)
              i (Set.Icc (μ - g) (μ + g))) := lintegral_const_mul _ hmeas
        _ ≤ _ := by
          have havg := lintegral_coordinateSpectralWeight_Icc_le hB i hab
          rw [show μ + g - (μ - g) = 2 * g by ring] at havg
          exact mul_le_mul_right havg _
    _ = _ := by simp

private theorem density_bound_nonneg {ρ : ℝ} {f : ℝ → ℝ≥0∞}
    (hnorm : IsProbabilityMeasure ((volume : Measure ℝ).withDensity f))
    (hρ : ∀ᵐ t ∂(volume : Measure ℝ), f t ≤ ENNReal.ofReal ρ) : 0 ≤ ρ := by
  by_contra! h
  have hf : f =ᵐ[(volume : Measure ℝ)] 0 := by
    filter_upwards [hρ] with t ht
    simpa [ENNReal.ofReal_of_nonpos h.le] using ht
  have hlaw := hnorm.measure_univ
  rw [withDensity_congr_ae hf, withDensity_zero] at hlaw
  simp at hlaw

/-- Probability bound for one specified adjacent rank, with multiplicity. -/
theorem specifiedAdjacentGapProbability : SourceTargets.specifiedAdjacentGapProbability := by
  intro n _ A hA f hf hnorm ρ hρ j g hg
  classical
  let law (k : Fin (n + 1)) := (volume : Measure ℝ).withDensity (f k)
  let ν := Measure.pi law
  let E := hA.specifiedAdjacentGapEvent j g
  let W (i : Fin (n + 1)) (v : Fin (n + 1) → ℝ) :=
    ENNReal.ofReal (gapProjectionWeight (hA.diagonalPerturbation v) i j g)
  have hme : MeasurableSet E := hA.measurableSet_specifiedAdjacentGapEvent j g
  have hpoint (v : Fin (n + 1) → ℝ) :
      E.indicator (fun _ => (2 : ℝ≥0∞)) v ≤ ∑ i, W i v := by
    by_cases hv : v ∈ E
    · rw [Set.indicator_of_mem hv]
      change (2 : ℝ≥0∞) ≤ ∑ i, ENNReal.ofReal (gapProjectionWeight (hA.diagonalPerturbation v) i j g)
      have hnn (i : Fin (n + 1)) : 0 ≤ gapProjectionWeight (hA.diagonalPerturbation v) i j g :=
        coordinateSpectralWeight_nonneg _ _ _
      rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => hnn i)]
      have h := ENNReal.ofReal_le_ofReal (two_le_sum_gapProjectionWeight (hA.diagonalPerturbation v) j g hv)
      simpa using h
    · simp [Set.indicator_of_notMem hv]
  have hρ₀ := density_bound_nonneg (hnorm 0) (hρ 0)
  have htwo : 2 * ν E ≤ 2 * ENNReal.ofReal ((n + 1) * ρ * g) := calc
    _ = ∫⁻ v, E.indicator (fun _ => (2 : ℝ≥0∞)) v ∂ν :=
      (lintegral_indicator_const hme _).symm
    _ ≤ ∫⁻ v, ∑ i, W i v ∂ν := lintegral_mono hpoint
    _ = ∑ i, ∫⁻ v, W i v ∂ν := lintegral_finset_sum _ (fun i _ =>
      (measurable_gapProjectionWeight hA i j hg.le).ennreal_ofReal)
    _ ≤ ∑ _i : Fin (n + 1), ENNReal.ofReal ρ * ENNReal.ofReal (2 * g) :=
      Finset.sum_le_sum (fun i _ => lintegral_gapProjectionWeight_le hA f hf hnorm ρ hρ i j hg)
    _ = _ := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
        ← ENNReal.ofReal_mul hρ₀, ← ENNReal.ofReal_natCast,
        ← ENNReal.ofReal_mul (Nat.cast_nonneg _), ← (show ENNReal.ofReal (2 : ℝ) = 2 by norm_num),
        ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
      congr 1
      push_cast
      ring
  exact (ENNReal.mul_le_mul_iff_right (show (2 : ℝ≥0∞) ≠ 0 by norm_num) (by norm_num)).mp htwo

end NumStability.CertifiedTridiagonalEigenpairs
