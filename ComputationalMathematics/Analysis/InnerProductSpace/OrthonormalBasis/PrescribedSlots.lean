import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Logic.Function.Basic
import Mathlib.Logic.Equiv.Set

/-!
# Orthonormal basis extension at prescribed finite slots

An orthonormal family can be extended to a full real Euclidean orthonormal basis
while retaining each vector at its specified injective final index.
-/

namespace NumStability

/-- Extend an orthonormal family at its exact injective final slots, including
empty families, empty ambient spaces and empty complements.
-/
theorem exists_orthonormalBasis_extending_fin_embedding {n k : ℕ}
    (I : Fin k ↪ Fin n) (Q : Fin k → EuclideanSpace ℝ (Fin n))
    (hQ : Orthonormal ℝ Q) :
    ∃ U : OrthonormalBasis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)),
      ∀ j, U (I j) = Q j := by
  classical
  let family : Fin n → EuclideanSpace ℝ (Fin n) :=
    Function.extend I Q (fun _ => 0)
  let e : Fin k ≃ Set.range I := Equiv.ofInjective I I.injective
  have hfamily : (Set.range I).restrict family = fun i => Q (e.symm i) := by
    funext i
    have hi : I (e.symm i) = i.val :=
      Equiv.apply_ofInjective_symm I.injective i
    change Function.extend I Q (fun _ => 0) i.val = Q (e.symm i)
    rw [← hi, I.injective.extend_apply]
  have horth : Orthonormal ℝ ((Set.range I).restrict family) := by
    rw [hfamily]
    exact hQ.comp e.symm e.symm.injective
  obtain ⟨U, hU⟩ :=
    horth.exists_orthonormalBasis_extension_of_card_eq (by simp)
  refine ⟨U, ?_⟩
  intro j
  have hj := hU (I j) ⟨j, rfl⟩
  simpa [family, I.injective.extend_apply] using hj

end NumStability
