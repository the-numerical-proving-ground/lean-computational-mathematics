import ComputationalMathematics.Source.CertifiedTridiagonalEigenpairs.IndexedRefinement.Target
import ComputationalMathematics.Source.CertifiedTridiagonalEigenpairs.CertifiedSturmCount

/-! The certified strict counts supply the brackets of the rounded refinement. -/

namespace NumStability.CertifiedTridiagonalEigenpairs

open FloatingPointFormat.UnboundedBinary ScalarWork

theorem indexedRefinement : SourceTargets.indexedRefinement := by
  unfold SourceTargets.indexedRefinement
  intro n r q hq j a b
  dsimp only
  intro hr hprec hH hb
  have ⟨henclosure, herr, hstrict⟩ :=
    tridiagonalRefinement_enclosures_and_accuracy_of_count_bracket r j a b hr hprec hH
      (fun x hxlo hxhi => by
        have h := certifiedSturmCount n r q hq a b x hr hprec hH hb ⟨hxlo, hxhi⟩
        exact ⟨h.2.2.1, h.2.2.2.1⟩)
  have ⟨hwork, hcap, hspace⟩ := tridiagonalRefinement_resources r j a b
  refine ⟨fun m _ => henclosure m, herr, hstrict, hwork.trans ?_, hcap, hspace⟩
  have hsweep : 13 * (n + 1) + 8 ≤ 21 * (n + 1) := by omega
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

end NumStability.CertifiedTridiagonalEigenpairs
