import ComputationalMathematics.Source.CertifiedTridiagonalEigenpairs.FiniteTrial.CostReliabilityTarget
import ComputationalMathematics.Source.CertifiedTridiagonalEigenpairs.FiniteTrial.Proof
import ComputationalMathematics.Source.CertifiedTridiagonalEigenpairs.RequestedGapProbability.Proof
import ComputationalMathematics.Source.CertifiedTridiagonalEigenpairs.TrialSamplerBounds
import ComputationalMathematics.Analysis.FunctionalCalculus.Resolvent.ImaginaryShift

/-! Lift the actual finite rejection event to the coupling and apply the requested-gap bound. -/

namespace NumStability.CertifiedTridiagonalEigenpairs

open FloatingPointFormat.UnboundedBinary MeasureTheory NoisyRankCertificate
open scoped ENNReal

private theorem eigenvalues_cast_card {𝕜 : Type*} [RCLike 𝕜] {N : ℕ}
    {A : Matrix (Fin N) (Fin N) 𝕜} (hA : A.IsHermitian) (j : Fin N) :
    hA.eigenvalues₀ (Fin.cast (Fintype.card_fin N).symm j) =
      (Matrix.isHermitian_iff_isSymmetric.mp hA).eigenvalues finrank_euclideanSpace_fin j := by
  unfold Matrix.IsHermitian.eigenvalues₀
  have hcast {r s : ℕ} (hr : Module.finrank 𝕜 (EuclideanSpace 𝕜 (Fin N)) = r)
      (hs : Module.finrank 𝕜 (EuclideanSpace 𝕜 (Fin N)) = s) (h : r = s) (i : Fin s) :
      (Matrix.isHermitian_iff_isSymmetric.mp hA).eigenvalues hr (Fin.cast h.symm i) =
        (Matrix.isHermitian_iff_isSymmetric.mp hA).eigenvalues hs i := by
    cases h
    rfl
  exact hcast _ _ (Fintype.card_fin N) j

/-- Passing from a real symmetric matrix to its complexification preserves
each ordered eigenvalue, with its multiplicity. -/
theorem complexified_eigenvalue_eq {N : ℕ} {A : Matrix (Fin N) (Fin N) ℝ}
    (hA : A.IsHermitian) (hC : (A.map Complex.ofReal).IsHermitian) (j : Fin N) :
    (Matrix.isHermitian_iff_isSymmetric.mp hC).eigenvalues finrank_euclideanSpace_fin j =
      hermitianOrderedEigenvalue hA j := by
  have hroots : ((A.map Complex.ofReal).charpoly.roots.map (RCLike.re : ℂ → ℝ)) =
      A.charpoly.roots.map (RCLike.re : ℝ → ℝ) := by
    change ((A.map Complex.ofRealHom).charpoly.roots.map (RCLike.re : ℂ → ℝ)) = _
    rw [Matrix.charpoly_map, hA.splits_charpoly.roots_map_of_injective Complex.ofReal_injective,
      Multiset.map_map]
    congr 1
  have hsort := congrArg (fun roots : Multiset ℝ => roots.sort (· ≥ ·)) hroots
  dsimp only at hsort
  rw [hC.sort_roots_charpoly_eq_eigenvalues₀, hA.sort_roots_charpoly_eq_eigenvalues₀] at hsort
  have heigs := congrFun (List.ofFn_inj.mp hsort) (Fin.cast (Fintype.card_fin N).symm j)
  simpa only [eigenvalues_cast_card, hermitianOrderedEigenvalue] using heigs

private theorem complex_diagonalPerturbation_eq {N : ℕ}
    (S : Matrix (Fin N) (Fin N) ℝ) (v : Fin N → ℝ) :
    (S.map Complex.ofReal).diagonalPerturbation v = (S + Matrix.diagonal v).map Complex.ofReal := by
  ext i j
  by_cases h : i = j
  · subst j
    simp [Matrix.diagonalPerturbation]
  · simp [Matrix.diagonalPerturbation, Matrix.diagonal_apply_ne _ h]

private theorem coupledMatrix_tridiagonal {n k p : ℕ}
    (d : Fin (n + 1) → ℝ) (b : Fin n → ℝ)
    (batch : Fin (n + 1) → Fin (2 ^ rngBits (n + 1) k) × ℝ) :
    coupledMatrix (n + 1) k p (sturmTridiagonal d b) batch =
      sturmTridiagonal (fun i => d i + coupledCoordinate (perturbationScale p)
        (rngBits (n + 1) k) (batch i)) b := by
  unfold coupledMatrix
  let v := fun i => coupledCoordinate (perturbationScale p) (rngBits (n + 1) k) (batch i)
  change sturmTridiagonal d b + Matrix.diagonal v = sturmTridiagonal (d + v) b
  rw [← show sturmTridiagonal v 0 = Matrix.diagonal v by simp [sturmTridiagonal],
    ← sturmTridiagonal_add, add_zero]

private theorem spectrum_eq_of_matrix_eq {N : ℕ} {A B : Matrix (Fin N) (Fin N) ℂ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) (h : A = B) :
    (Matrix.isHermitian_iff_isSymmetric.mp hA).eigenvalues finrank_euclideanSpace_fin =
      (Matrix.isHermitian_iff_isSymmetric.mp hB).eigenvalues finrank_euclideanSpace_fin := by
  subst B
  rfl

private theorem coupledAdjacentGapEvent_iff {n k p : ℕ}
    (d : Fin (n + 1) → ℝ) (b : Fin n → ℝ)
    (batch : Fin (n + 1) → Fin (2 ^ rngBits (n + 1) k) × ℝ)
    (hC : ((sturmTridiagonal d b).map Complex.ofReal).IsHermitian) (e : Fin n) (g : ℝ) :
    let v := fun i => coupledCoordinate (perturbationScale p) (rngBits (n + 1) k) (batch i)
    v ∈ hC.specifiedAdjacentGapEvent e g ↔
      ascendingEigenvalue (sturmTridiagonal_isHermitian (d + v) b) e.succ -
      ascendingEigenvalue (sturmTridiagonal_isHermitian (d + v) b) e.castSucc ≤ g := by
  intro v
  have hP : ((sturmTridiagonal d b).map Complex.ofReal).diagonalPerturbation v =
      (sturmTridiagonal (d + v) b).map Complex.ofReal := by
    rw [complex_diagonalPerturbation_eq]
    exact congrArg (fun A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ => A.map Complex.ofReal)
      (coupledMatrix_tridiagonal (p := p) d b batch)
  have hshift := hC.diagonalPerturbation v
  have hP' := hP ▸ hshift
  have hfun := spectrum_eq_of_matrix_eq hshift hP' hP
  have hs := funext (complexified_eigenvalue_eq (sturmTridiagonal_isHermitian _ _) hP')
  unfold Matrix.IsHermitian.specifiedAdjacentGapEvent
  change _ - _ ≤ g ↔ _
  rw [hfun, hs, ascendingEigenvalue, ascendingEigenvalue, Fin.rev_succ, Fin.rev_castSucc]

private theorem trialScale_probability_le (n p : ℕ) (J : Finset ℕ) :
    (n + 1 : ℝ) * J.card * gapScale (n + 1) J.card p / perturbationScale p ≤
      rejectionBound (n + 1) := by
  let N : ℝ := nextPowerOfTwo (n + 1)
  let K : ℝ := nextPowerOfTwo J.card
  have hN : 0 < N := by unfold N nextPowerOfTwo; positivity
  have hK : 0 < K := by unfold K nextPowerOfTwo; positivity
  have hδ : 0 < perturbationScale p := div_pos (unitRoundoff_pos _) (by norm_num)
  have hnN : (n + 1 : ℝ) ≤ N := by
    unfold N
    exact_mod_cast le_nextPowerOfTwo (n + 1)
  have hkK : (J.card : ℝ) ≤ K := by
    unfold K
    exact_mod_cast le_nextPowerOfTwo J.card
  unfold gapScale rejectionBound
  change (n + 1 : ℝ) * J.card * (perturbationScale p / (1024 * N ^ 3 * K)) /
    perturbationScale p ≤ 3 / (2048 * N ^ 2)
  calc
    _ = (n + 1 : ℝ) * J.card / (1024 * N ^ 3 * K) := by
      field_simp [hN.ne', hK.ne', hδ.ne']
    _ ≤ N * K / (1024 * N ^ 3 * K) := by gcongr
    _ = 1 / (1024 * N ^ 2) := by field_simp [hN.ne', hK.ne']
    _ ≤ 3 / (2048 * N ^ 2) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [sq_nonneg N]

theorem finiteTrialUniformRejection : SourceTargets.finiteTrialUniformRejection := by
  intro n p J a b hn guard hJ hsubset ha hb
  let N := n + 1
  let k := J.card
  let δ := perturbationScale p
  let g := gapScale N k p
  let S := sturmTridiagonal (fun i => (a i).value) (fun j => (b j).value)
  let μ := vectorCoupling N δ (rngBits N k)
  let V := fun (batch : Fin N → Fin (2 ^ rngBits N k) × ℝ) i =>
    coupledCoordinate δ (rngBits N k) (batch i)
  have hS : (S.map Complex.ofReal).IsHermitian := by
    apply MatrixResolvent.isHermitian_map_ofReal
    have h := sturmTridiagonal_isHermitian (fun i => (a i).value) (fun j => (b j).value)
    simpa [Matrix.IsHermitian, Matrix.IsSymm] using h
  have hδ : 0 < δ := div_pos (unitRoundoff_pos _) (by norm_num)
  have hg : 0 < g := by
    change 0 < gapScale N k p
    rw [gapScale_eq_roundoff]
    exact unitRoundoff_pos _
  have hwords : Measurable (couplingWords N k) := by
    unfold couplingWords
    exact Measurable.of_discrete.comp (measurable_pi_lambda _
      (fun i => measurable_fst.comp (measurable_pi_apply i)))
  have hV : Measurable V :=
    measurable_pi_lambda _ (fun i => (measurable_coupledCoordinate δ (rngBits N k)).comp
      (measurable_pi_apply i))
  have hR : MeasurableSet (trialRejected n p J a b) := Set.Countable.measurableSet (Set.to_countable _)
  have hE := measurableSet_requestedSmallGapEvent hS J g
  have hsubsetAE :
      couplingWords N k ⁻¹' trialRejected n p J a b ≤ᵐ[μ]
        V ⁻¹' requestedSmallGapEvent hS J g := by
    filter_upwards [vectorCoupling_trial_close N k p] with batch hclose
    intro hrejected
    by_contra hbad
    have hgood (e : Fin n) (he : e.val + 1 ∈ requestedAdjacentGapIndices N J) :
        g < ascendingEigenvalue
          (sturmTridiagonal_isHermitian (fun i => (a i).value + V batch i) (fun j => (b j).value)) e.succ -
          ascendingEigenvalue
          (sturmTridiagonal_isHermitian (fun i => (a i).value + V batch i) (fun j => (b j).value)) e.castSucc := by
      apply lt_of_not_ge
      intro hsmall
      exact hbad ⟨e, he, (coupledAdjacentGapEvent_iff (k := k) (p := p) _ _ batch hS e g).mpr hsmall⟩
    have haccept := finiteTrialCoupledAcceptance n p J a b hn guard ha hb
      (couplingWords N k batch) (V batch) hclose hgood
    exact Bool.false_ne_true (hrejected.symm.trans haccept)
  have hgap := requestedGapProbability n hn (S.map Complex.ofReal) hS J hJ hsubset δ g hδ hg
  calc
    _ = μ (couplingWords N k ⁻¹' trialRejected n p J a b) := by
      rw [← vectorCoupling_words N k hδ, Measure.map_apply hwords hR]
    _ ≤ μ (V ⁻¹' requestedSmallGapEvent hS J g) := measure_mono_ae hsubsetAE
    _ = symmetricUniformProduct N δ (requestedSmallGapEvent hS J g) := by
      rw [← Measure.map_apply hV hE, vectorCoupling_values N hδ (rngBits N k)]
      rfl
    _ ≤ ENNReal.ofReal ((n + 1 : ℝ) * J.card * g / δ) := hgap.1.trans hgap.2
    _ ≤ ENNReal.ofReal (rejectionBound N) :=
      ENNReal.ofReal_le_ofReal (trialScale_probability_le n p J)

theorem finiteTrialCostReliability : SourceTargets.finiteTrialCostReliability :=
  ⟨finiteTrialCertificate, finiteTrialUniformRejection⟩

end NumStability.CertifiedTridiagonalEigenpairs
