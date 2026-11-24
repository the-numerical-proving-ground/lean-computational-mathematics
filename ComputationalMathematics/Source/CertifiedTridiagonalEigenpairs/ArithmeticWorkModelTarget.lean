import ComputationalMathematics.Algorithms.Arithmetic.ScalarWork
import ComputationalMathematics.Analysis.FloatingPointArithmetic.UnboundedBinary.ScalarOperations
import ComputationalMathematics.Source.CertifiedTridiagonalEigenpairs.Parameters

/-!
# Arithmetic and work in the selected-eigenpairs paper

The common arithmetic conventions are those of §1.1 (sec:model).
The input and final output use the same precision, with the guard from
equation (1) (main:guard). The real-rounding law is about exact inputs to
the rounding primitive. Operation charges and word counts require a separate
account of the steps taken and the simultaneous storage used by an execution.

The paper uses the Euclidean vector norm, the induced matrix operator norm,
and the Frobenius norm. Its other symbols retain their ordinary meaning:
identity, conjugate transpose, real transpose, matrix imaginary part,
base-two logarithm and natural logarithm.
-/

namespace NumStability.CertifiedTridiagonalEigenpairs

open FloatingPointFormat.UnboundedBinary
open ScalarWork

namespace SourceTargets

/-- The arithmetic conventions, roundoff bound and resource units of §1.1. -/
def arithmeticWorkModel : Prop :=
  (∀ n p : ℕ, 0 < n → precisionGuard n p → 7 ≤ p) ∧
  (∀ (t : ℕ) (ht : 2 ≤ t) (x : ℝ),
    ((∃ word : Word t ht, word.value = x) ↔ Native t ht x) ∧
    FloatingPointFormat.nearestRoundingIn (Native t ht) x (roundToEven t ht x) ∧
    (x ≠ 0 → (format t ht).sourceRoundToEvenEvidence x (roundToEven t ht x)) ∧
    |roundToEven t ht x - x| ≤ (2 : ℝ) ^ (-(t : ℤ)) * |x|) ∧
  (∀ (t : ℕ) (ht : 2 ≤ t) (operation : ScalarOperation t ht),
    operation.eval.value = roundToEven t ht operation.exactValue) ∧
  (∀ (s t : ℕ) (hs : 2 ≤ s) (ht : 2 ≤ t) (word : Word s hs),
    (word.convert t ht).value = roundToEven t ht word.value) ∧
  (∀ (t : ℕ) (ht : 2 ≤ t) (word : Word t ht) (k : ℤ),
    (word.scale k).value = (2 : ℝ) ^ k * word.value ∧
    (word.scale k).exponent = word.exponent.map (· + k)) ∧
  (∀ (cap : ℕ) (trace : List Step), TraceAllowed cap trace →
    (∀ bits, Step.arithmetic bits ∈ trace → 2 ≤ bits ∧ bits ≤ cap) ∧
    (∀ s t, Step.conversion s t ∈ trace → 2 ≤ s ∧ s ≤ cap ∧ 2 ≤ t ∧ t ≤ cap) ∧
    work trace = trace.length) ∧
  (∀ (liveWords : List ℕ) (limit : ℕ), storage liveWords ≤ limit ↔
    ∀ words ∈ liveWords, words ≤ limit)

end SourceTargets

end NumStability.CertifiedTridiagonalEigenpairs
