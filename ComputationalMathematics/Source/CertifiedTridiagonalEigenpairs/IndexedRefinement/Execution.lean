import ComputationalMathematics.Analysis.Eigenvalues.TridiagonalRefinementExecution
import ComputationalMathematics.Source.CertifiedTridiagonalEigenpairs.IndexedRefinement.Proof

/-! Enclosure, accuracy, and resource bounds for the constant-workspace run. -/

namespace NumStability.CertifiedTridiagonalEigenpairs

open FloatingPointFormat.UnboundedBinary
open FloatingPointFormat.UnboundedBinary.PaddedRefinement (midpoint)

noncomputable section

/-- The endpoint-only refinement has the source enclosures and accuracy.
The resource bounds follow from the separate interpreter of the same
instructions, whose first projection is the returned word. -/
theorem runIndexedRefinement {n r q : ℕ} {hq : 2 ≤ q} (j : Fin (n + 1))
    (a : Fin (n + 1) → Word q hq) (b : Fin n → Word q hq)
    (hr : 2 ≤ r) (hprec : r + 8 ≤ q)
    (hH : realMatrixOperatorNorm
      (sturmTridiagonal (fun i => (a i).value) (fun i => (b i).value)) ≤ 3 / 2)
    (hb : ∀ i, |(b i).value| ≤ 1) :
    let spectrum := NoisyRankCertificate.ascendingEigenvalue
      (sturmTridiagonal_isHermitian (fun i => (a i).value) (fun i => (b i).value))
    let ε := unitRoundoff r
    let measured := measuredTridiagonalRefinement r j a b
    measured.1 = runTridiagonalRefinement r j a b ∧
    (∀ m ≤ r + 4,
      let interval := runTridiagonalRefinementInterval r j a b m
      let x := midpoint interval
      interval.Contains (spectrum j) ∧
        interval.lower.value ≤ x.value ∧ x.value ≤ interval.upper.value) ∧
    |(runTridiagonalRefinement r j a b).value - spectrum j| ≤ (423 / 256) * ε ∧
    (423 / 256) * ε < 2 * ε ∧
    measured.2.work ≤ 68 * (n + 1) * r ∧
    measured.2.peakWords ≤ 26 * (n + 1) := by
  obtain ⟨henclosure, haccuracy, hstrict, _⟩ := indexedRefinement n r q hq j a b hr hprec hH hb
  obtain ⟨_, hwork, hspace⟩ := runTridiagonalRefinement_resources r j a b
  refine ⟨measuredTridiagonalRefinement_eq_run r j a b,
    ?_, ?_, hstrict, hwork.trans ?_, hspace⟩
  · simpa only [runTridiagonalRefinementInterval_eq] using henclosure
  · simpa only [runTridiagonalRefinement_eq] using haccuracy
  · have hsweep : 13 * (n + 1) + 8 ≤ 21 * (n + 1) := by omega
    have hiter : r + 4 ≤ 3 * r := by omega
    have hprod := Nat.mul_le_mul hsweep hiter
    have hnonzero : 2 ≤ (n + 1) * r :=
      hr.trans (by simpa using Nat.mul_le_mul_right r (show 1 ≤ n + 1 by omega))
    calc
      (13 * (n + 1) + 8) * (r + 4) + 10 ≤ (21 * (n + 1)) * (3 * r) + 10 :=
        Nat.add_le_add_right hprod 10
      _ = 63 * ((n + 1) * r) + 10 := by ring
      _ ≤ 68 * ((n + 1) * r) := by omega
      _ = 68 * (n + 1) * r := by ring

end

end NumStability.CertifiedTridiagonalEigenpairs
