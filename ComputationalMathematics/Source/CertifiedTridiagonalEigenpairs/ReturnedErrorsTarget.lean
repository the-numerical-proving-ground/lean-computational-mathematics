import ComputationalMathematics.Source.CertifiedTridiagonalEigenpairs.TridiagonalEigenpairRun

/-! Returned errors of the actual tridiagonal eigensolver, §7.2. -/

namespace NumStability.CertifiedTridiagonalEigenpairs

open Matrix WithLp NoisyRankCertificate FloatingPointFormat.UnboundedBinary
open scoped Matrix.Norms.L2Operator

/-- The returned array and separate per-column error bounds, at the original
input scale and original ordered ranks. -/
def TridiagonalReturnedBounds {n k : ℕ} (I : Fin k → Fin n)
    (T : Matrix (Fin n) (Fin n) ℝ) (hT : T.IsHermitian)
    (Q : Matrix (Fin n) (Fin k) ℝ) (labels : Fin k → ℝ) (u : ℝ) : Prop :=
  (∀ j, |labels j - ascendingEigenvalue hT (I j)| ≤ 16 * u * ‖T‖) ∧
  ‖T * Q - Q * diagonal labels‖ ≤ 128 * Real.sqrt k * u * ‖T‖ ∧
  ‖Qᵀ * Q - 1‖ ≤ 9 * Real.sqrt k * u ∧
  (∀ i j : Fin k, i ≠ j → |(Qᵀ * Q) i j| ≤ 9 * u) ∧
  (∀ j, ‖toLp 2 (T *ᵥ Q.col j) - labels j • toLp 2 (Q.col j)‖ ≤ 128 * u * ‖T‖)

/-- Intermediate bounds on the nontrivial branch, using its native label and
column array and the exact selected eigenvectors of its accepted matrix. -/
def TridiagonalAcceptedErrorBounds {n p : ℕ} {J : Finset ℕ} {hp : 2 ≤ p}
    (a : Fin (n + 1) → Word p hp) (b : Fin n → Word p hp)
    (valid : J ⊆ Finset.Icc 1 (n + 1)) (out : NativeAcceptedEigenpairs n p J hp) : Prop :=
  let r := out.scaleExponent
  let R := (2 : ℝ) ^ r
  let T := storedTridiagonal a b
  let S := normalizedTridiagonal a b r
  let bW := fun i => normalizeTrialWord (J := J) r (b i)
  let M := out.accepted.matrix bW
  let I := requestedRankOrder valid
  let θ := fun j => (runAcceptedRefinement out.accepted.trial bW ((requestedRankArray J valid).get j)).value
  let μ := fun j => roundToEven p hp (θ j)
  let D := diagonal μ
  let Q := out.columns
  let u := unitRoundoff p
  let η := vectorTolerance (n + 1) J.card p
  let rootk := Real.sqrt (J.card : ℝ)
  let ℓM := ascendingEigenvalue (out.accepted.matrix_isHermitian bW)
  let ℓS := ascendingEigenvalue (sturmTridiagonal_isHermitian _ _ :
    (normalizedTridiagonal a b r).IsHermitian)
  ∃ U : Matrix (Fin (n + 1)) (Fin J.card) ℝ,
    let E := Q - U
    Uᵀ * U = 1 ∧ M * U = U * diagonal (fun j => ℓM (I j)) ∧ Q = U + E ∧
    (∀ j, ‖toLp 2 (Q.col j) - toLp 2 (U.col j)‖ ≤ 4 * u) ∧
    ‖E‖ ≤ frobNormRect E ∧ frobNormRect E ≤ 4 * rootk * u ∧
    ‖Q‖ ≤ 1 + 4 * rootk * u ∧
    (∀ j, |μ j - ℓM (I j)| ≤ η + u * (1 + η) ∧
      |μ j - ℓM (I j)| < 2 * u ∧ |μ j| < 2) ∧
    ‖M * Q - Q * D‖ ≤ 12 * rootk * u + 2 * u ∧
    ‖S * Q - Q * D‖ < 15 * rootk * u ∧
    diagonal out.labels = R • D ∧
    ‖T * Q - Q * diagonal out.labels‖ < 120 * rootk * u * ‖T‖ ∧
    (∀ j, |μ j - ℓS (I j)| ≤ η + u * (1 + η) + u / 128 ∧ |μ j - ℓS (I j)| < 2 * u)

namespace SourceTargets

/-- Every returned execution has the original-scale bounds. On the nontrivial
branch its actual accepted matrix and stored final labels also satisfy the
intermediate estimates used to obtain them. -/
def tridiagonalReturnedErrors : Prop :=
  ∀ (n p : ℕ) (J : Finset ℕ) (hp : 2 ≤ p)
    (a : Fin (n + 1) → Word p hp) (b : Fin n → Word p hp)
    (bits : ℕ → GateBits n J) (guard : precisionGuard (n + 1) p)
    (hJ : J.Nonempty) (valid : J ⊆ Finset.Icc 1 (n + 1))
    (out : NativeTridiagonalOutput n p J hp),
    runTridiagonalEigenpairs a b bits guard hJ valid = some out →
    TridiagonalReturnedBounds (requestedRankOrder valid) (storedTridiagonal a b)
      (sturmTridiagonal_isHermitian _ _) out.columns out.labels (unitRoundoff p) ∧
    match out with
    | .exact _ _ => True
    | .refined accepted => TridiagonalAcceptedErrorBounds a b valid accepted

end SourceTargets

end NumStability.CertifiedTridiagonalEigenpairs
