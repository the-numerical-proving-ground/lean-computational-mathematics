import ComputationalMathematics.Analysis.Eigenvalues.AscendingEigenvalueRoots
import ComputationalMathematics.Analysis.Eigenvalues.ComplexHermitianL1.Defs
import ComputationalMathematics.Analysis.Eigenvalues.CongruenceInertia
import ComputationalMathematics.Analysis.Eigenvalues.ScalarShift
import Mathlib.Analysis.CStarAlgebra.Matrix

/-!
# Strict spectral counts for certified refinement

The spectral-count definition and the spectral facts in Section 4 of the
selected paper, including Weyl's inequality (label `main:weyl`).
-/

namespace NumStability.CertifiedTridiagonalEigenpairs.SourceTargets

open Classical NoisyRankCertificate CongruenceInertia ComplexHermitianL1
open scoped Matrix.Norms.L2Operator

/-- The strict count includes eigenvalue multiplicities. It is the negative
count after a scalar shift. Weyl controls each ascending Hermitian rank, and
nonsingular real congruence preserves the negative inertia used in the count. -/
def sturmSpectralCount : Prop :=
  (∀ (n : ℕ) (H : Matrix (Fin n) (Fin n) ℝ) (hH : H.IsHermitian) (t : ℝ),
    let eigenvalue := ascendingEigenvalue hH
    let count := strictBelowCount eigenvalue t
    Monotone eigenvalue ∧
    count = (Finset.univ.filter fun j => eigenvalue j < t).card ∧
    count = (H.charpoly.roots.filter fun x => x < t).card ∧
    count = strictBelowCount (ascendingEigenvalue (ScalarShift.shifted_isHermitian H hH t)) 0) ∧
  (∀ (n : ℕ) (H E : Matrix (Fin n) (Fin n) ℂ)
    (hH : H.IsHermitian) (hE : E.IsHermitian) (j : Fin n),
    |complexOrderedEigenvalue (hH.add hE) j.rev - complexOrderedEigenvalue hH j.rev| ≤ ‖E‖) ∧
  (∀ (n : ℕ) (A B : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsHermitian) (hB : B.IsHermitian)
    (L : (Matrix (Fin n) (Fin n) ℝ)ˣ),
    A = L.val * B * L.val.transpose →
    negativeCount (hermitianOrderedEigenvalue hA) =
      negativeCount (hermitianOrderedEigenvalue hB))

end NumStability.CertifiedTridiagonalEigenpairs.SourceTargets
