import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.Finset.Card

/-! The adjacent gap indices tested for a fixed set of requested spectral ranks. -/

namespace NumStability.CertifiedTridiagonalEigenpairs

/-- The left endpoints of existing adjacent rank pairs touching a requested rank.
Ranks are numbered from one, as in the paper. -/
def requestedAdjacentGapIndices (n : ℕ) (J : Finset ℕ) : Finset ℕ :=
  (Finset.Icc 1 (n - 1)).filter fun i => i ∈ J ∨ i + 1 ∈ J

namespace SourceTargets

/-- The cardinality assertion accompanying the definition of the requested gap set. -/
def requestedAdjacentGapCardinality : Prop :=
  ∀ (n : ℕ) (J : Finset ℕ),
    J.Nonempty → J ⊆ Finset.Icc 1 n →
      (requestedAdjacentGapIndices n J).card ≤ 2 * J.card

end SourceTargets
end NumStability.CertifiedTridiagonalEigenpairs
