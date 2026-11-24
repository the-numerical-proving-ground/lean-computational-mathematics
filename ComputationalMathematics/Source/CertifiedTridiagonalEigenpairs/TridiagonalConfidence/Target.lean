import ComputationalMathematics.Source.CertifiedTridiagonalEigenpairs.TridiagonalEigenpairWork

/-! Prescribed confidence for the actual tridiagonal eigenpair execution. -/

open MeasureTheory
open scoped ENNReal

namespace NumStability.CertifiedTridiagonalEigenpairs

open FloatingPointFormat.UnboundedBinary NoisyRankCertificate

/-- The manuscript's real work threshold, viewed in the extended nonnegative
reals so that the work of a run without a return can be infinite. -/
noncomputable def manuscriptWorkCutoff (C n k p : ℕ) (m : ℤ) : ℝ≥0∞ :=
  ENNReal.ofReal ((C : ℝ) * ((m : ℝ) + 1) * n * k * p)

namespace SourceTargets

/-- Corollary `main:high-probability`. One absolute constant controls the tail
and both confidence thresholds of the same complete work variable. The two
confidence parameters occur only in the work events. Every returned output on
this same stream law satisfies the tridiagonal stability guarantees. -/
def tridiagonalPrescribedConfidence : Prop :=
  ∃ C_hp : ℕ, 0 < C_hp ∧
    ∀ (n p : ℕ) (hp : 2 ≤ p) (J : Finset ℕ)
      (a : Fin (n + 1) → Word p hp) (b : Fin n → Word p hp)
      (hguard : precisionGuard (n + 1) p) (hJ : J.Nonempty)
      (hJvalid : J ⊆ Finset.Icc 1 (n + 1)),
      let d := n + 1
      let k := J.card
      let N := nextPowerOfTwo d
      let μ := retryBitMeasure n J
      let W := tridiagonalEigenpairWork a b hJvalid
      (∀ m : ℕ, 1 ≤ m →
        μ {bits | manuscriptWorkCutoff C_hp d k p m < W bits} ≤
          ENNReal.ofReal (3 / (2048 * (N : ℝ) ^ 2)) ^ m) ∧
      (∀ c : ℝ, 0 < c →
        1 - ENNReal.ofReal ((d : ℝ) ^ (-c)) ≤
          μ {bits | W bits ≤ manuscriptWorkCutoff C_hp d k p ⌈c / 2⌉}) ∧
      (∀ ε : ℝ, 0 < ε → ε < 1 →
        1 - ENNReal.ofReal ε ≤ μ {bits | W bits ≤
          manuscriptWorkCutoff C_hp d k p ⌈Real.log (1 / ε) / Real.log (2048 * (N : ℝ) ^ 2 / 3)⌉}) ∧
      (∀ (bits : ℕ → GateBits n J) (out : NativeTridiagonalOutput n p J hp),
        runTridiagonalEigenpairs a b bits hguard hJ hJvalid = some out →
        ReturnedAccuracy (requestedRankOrder hJvalid) (storedTridiagonal a b)
          (sturmTridiagonal_isHermitian _ _) out.columns out.labels (unitRoundoff p))

end SourceTargets
end NumStability.CertifiedTridiagonalEigenpairs
