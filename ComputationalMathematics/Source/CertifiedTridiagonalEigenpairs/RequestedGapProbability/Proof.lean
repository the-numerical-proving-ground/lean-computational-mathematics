import ComputationalMathematics.Analysis.Eigenvalues.DiagonalPerturbation.Continuity
import ComputationalMathematics.Source.CertifiedTridiagonalEigenpairs.RequestedAdjacentGaps.Proof
import ComputationalMathematics.Source.CertifiedTridiagonalEigenpairs.RequestedGapProbability.Target
import ComputationalMathematics.Source.CertifiedTridiagonalEigenpairs.SpecifiedAdjacentGap.Proof

/-! Union bound for the fixed requested gap set and specialization to uniform shifts. -/

namespace NumStability.CertifiedTridiagonalEigenpairs

open MeasureTheory
open scoped ENNReal

private def adjacentRank {n : ℕ} {J : Finset ℕ}
    (i : ↥(requestedAdjacentGapIndices (n + 1) J)) : Fin n :=
  ⟨i.val - 1, by
    have hi := Finset.mem_Icc.mp (Finset.mem_filter.mp i.property).1
    omega⟩

private theorem adjacentRank_val_add_one {n : ℕ} {J : Finset ℕ}
    (i : ↥(requestedAdjacentGapIndices (n + 1) J)) : (adjacentRank i).val + 1 = i.val := by
  have hi := (Finset.mem_Icc.mp (Finset.mem_filter.mp i.property).1).1
  change i.val - 1 + 1 = i.val
  omega

private theorem requestedSmallGapEvent_eq_iUnion {n : ℕ}
    {S : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} (hS : S.IsHermitian)
    (J : Finset ℕ) (g : ℝ) :
    requestedSmallGapEvent hS J g =
      ⋃ i : ↥(requestedAdjacentGapIndices (n + 1) J),
        hS.specifiedAdjacentGapEvent (adjacentRank i) g := by
  ext v
  rw [Set.mem_iUnion]
  change (∃ j : Fin n, j.val + 1 ∈ requestedAdjacentGapIndices (n + 1) J ∧
    v ∈ hS.specifiedAdjacentGapEvent j g) ↔ _
  constructor
  · rintro ⟨j, hj, hv⟩
    refine ⟨⟨j.val + 1, hj⟩, ?_⟩
    have heq : adjacentRank ⟨j.val + 1, hj⟩ = j := Fin.ext (Nat.add_sub_cancel _ _)
    rwa [heq]
  · rintro ⟨i, hv⟩
    exact ⟨adjacentRank i, adjacentRank_val_add_one i ▸ i.property, hv⟩

/-- A finite union of measurable specified-gap events is measurable. -/
theorem measurableSet_requestedSmallGapEvent {n : ℕ}
    {S : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} (hS : S.IsHermitian)
    (J : Finset ℕ) (g : ℝ) :
    MeasurableSet (requestedSmallGapEvent hS J g) := by
  rw [requestedSmallGapEvent_eq_iUnion]
  exact MeasurableSet.iUnion fun i => hS.measurableSet_specifiedAdjacentGapEvent (adjacentRank i) g

theorem measure_requestedSmallGapEvent_le {n : ℕ}
    {S : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} (hS : S.IsHermitian)
    (J : Finset ℕ) (g : ℝ) (μ : Measure (Fin (n + 1) → ℝ)) (c : ℝ≥0∞)
    (hgap : ∀ j, μ (hS.specifiedAdjacentGapEvent j g) ≤ c) :
    μ (requestedSmallGapEvent hS J g) ≤ (requestedAdjacentGapIndices (n + 1) J).card * c := by
  classical
  rw [requestedSmallGapEvent_eq_iUnion]
  calc
    _ ≤ ∑ i : ↥(requestedAdjacentGapIndices (n + 1) J),
        μ (hS.specifiedAdjacentGapEvent (adjacentRank i) g) :=
      measure_iUnion_fintype_le _ _
    _ ≤ ∑ _ : ↥(requestedAdjacentGapIndices (n + 1) J), c :=
      Finset.sum_le_sum fun i _ => hgap (adjacentRank i)
    _ = _ := by simp [nsmul_eq_mul]

theorem requestedGapProbability : SourceTargets.requestedGapProbability := by
  intro n hn S hS J _ _ δ g hδ hg
  have hprob :
      IsProbabilityMeasure ((volume : Measure ℝ).withDensity (symmetricUniformDensity δ)) := by
    rw [← symmetricUniform_eq_withDensity hδ]
    exact isProbabilityMeasure_symmetricUniform hδ
  have hsingle (j : Fin n) :
      symmetricUniformProduct (n + 1) δ (hS.specifiedAdjacentGapEvent j g) ≤
        ENNReal.ofReal ((n + 1 : ℝ) * (1 / (2 * δ)) * g) := by
    simpa only [symmetricUniformProduct, symmetricUniform_eq_withDensity hδ] using
      specifiedAdjacentGapProbability n hn S hS (fun _ => symmetricUniformDensity δ)
        (fun _ => measurable_symmetricUniformDensity δ) (fun _ => hprob)
        (1 / (2 * δ)) (fun _ => ae_of_all _ (symmetricUniformDensity_le δ)) j g hg
  constructor
  · have h := measure_requestedSmallGapEvent_le hS J g _ _ hsingle
    have heq :
        ((requestedAdjacentGapIndices (n + 1) J).card : ℝ) * ((n + 1 : ℝ) * (1 / (2 * δ)) * g) =
          (n + 1 : ℝ) * (requestedAdjacentGapIndices (n + 1) J).card * g / (2 * δ) := by ring
    rw [← heq, ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
    exact h
  · apply ENNReal.ofReal_le_ofReal
    have hcard : ((requestedAdjacentGapIndices (n + 1) J).card : ℝ) ≤ 2 * J.card := by
      exact_mod_cast requestedAdjacentGapIndices_card_le (n + 1) J
    have hδ' : 0 < 2 * δ := by positivity
    calc
      _ ≤ (n + 1 : ℝ) * (2 * J.card) * g / (2 * δ) := by gcongr
      _ = _ := by ring

end NumStability.CertifiedTridiagonalEigenpairs
