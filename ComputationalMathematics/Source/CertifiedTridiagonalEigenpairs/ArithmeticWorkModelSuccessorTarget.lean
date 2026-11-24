import ComputationalMathematics.Source.CertifiedTridiagonalEigenpairs.ArithmeticExecutionModel
import ComputationalMathematics.Source.CertifiedTridiagonalEigenpairs.ArithmeticNotation
import ComputationalMathematics.Source.CertifiedTridiagonalEigenpairs.BidiagonalSVDPrecision

/-!
# Arithmetic and work conventions for the selected singular-triplets paper

The source is §1.1, including the input guard, roundoff bound, execution
precision, resource units, and notation. The routine precision clauses refer
also to the paper's tridiagonal and bidiagonal working precision formulas.

The paper says ties to even for generic positive significand precision. In
the one-bit midpoint case both normalized candidates have odd significands.
The IEEE 754-2019 convention chooses the larger magnitude, as does comparing
at the input exponent before renormalization (GNU MPFR §4.4). Neither paper
algorithm uses the one-bit case under its operational precision guard.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace NumStability.CertifiedTridiagonalEigenpairs.SourceTargets

open FloatingPointFormat.UnboundedBinary
open ScalarWork
open ArithmeticNotation

/-- The arithmetic and roundoff clauses at every positive precision. -/
def positivePrecisionArithmetic : Prop :=
  (∀ (t : ℕ) (ht : 0 < t) (x : ℝ),
    FloatingPointFormat.nearestRoundingIn (NativeAt t ht) x (roundAt t ht x) ∧
    |roundAt t ht x - x| ≤ (2 : ℝ) ^ (-(t : ℤ)) * |x|) ∧
  (∀ (t : ℕ) (ht : 2 ≤ t) (x : ℝ), x ≠ 0 →
    (format t ht).sourceRoundToEvenEvidence x (roundAt t (by omega) x)) ∧
  (∀ x : ℝ, x ≠ 0 →
    (positiveFormat 1 (by decide)).sourceRoundAwayEvidence x (roundAt 1 (by decide) x)) ∧
  (∀ m : ℕ, (positiveFormat 1 (by decide)).normalizedMantissa m → m = 1) ∧
  (∀ (t : ℕ) (ht : 0 < t) (operation : ArithmeticOperationAt t ht),
    operation.eval.val = roundAt t ht operation.exactValue) ∧
  (∀ (t : ℕ) (ht : 0 < t) (x : WordAt t ht) (hx : 0 ≤ x.val),
    0 ≤ (ArithmeticOperationAt.sqrt x hx).exactValue ∧
    (ArithmeticOperationAt.sqrt x hx).exactValue ^ 2 = x.val) ∧
  (∀ (s t : ℕ) (hs : 0 < s) (ht : 0 < t) (word : WordAt s hs),
    (convertWordAt t ht word).val = roundAt t ht word.val) ∧
  (∀ (t : ℕ) (ht : 2 ≤ t) (operation : ScalarOperation t ht),
    (ArithmeticOperationAt.ofStoredOperation operation).eval.val = operation.eval.value) ∧
  (∀ (t : ℕ) (ht : 2 ≤ t) (word : Word t ht) (k : ℤ),
    (word.scale k).value = (2 : ℝ) ^ k * word.value ∧
    (word.scale k).exponent = word.exponent.map (· + k))

/-- The precision guard and its instantiations for the paper's routines.
The type of an execution shares its I/O precision and indexes its arithmetic
steps by its working precision. Its conversions retain both precisions. -/
def executionResources : Prop :=
  (∀ n p : ℕ, 0 < n → precisionGuard n p → 7 ≤ p) ∧
  (∀ n k p : ℕ, 0 < n → precisionGuard n p →
    RoutinePrecision n p p p ∧
    RoutinePrecision n p (workingPrecision n k p) (workingPrecision n k p) ∧
    RoutinePrecision n p (svdAuxiliaryPrecision k p) (svdWorkingPrecision n k p)) ∧
  (∀ {n p q cap : ℕ} (prec : RoutinePrecision n p q cap) (stream : ℕ → Bool)
    (run : ArithmeticExecution prec stream),
    (∀ step ∈ run.trace, chargeAllowed cap step) ∧
    work run.trace = run.steps.length ∧
    (∀ limit : ℕ, storage run.liveWords ≤ limit ↔ ∀ words ∈ run.liveWords, words ≤ limit) ∧
    run.steps.filterMap ExecutedStep.bitValue =
      (List.range (run.steps.filterMap ExecutedStep.bitValue).length).map stream) ∧
  (∀ cap : ℕ, ∀ step : Step, chargeAtLeastTwo step →
    (step.Allowed cap ↔ chargeAllowed cap step)) ∧
  (∀ j : ℕ, ∀ b : Bool, fairBitStreamMeasure {stream | stream j = b} = (1 / 2 : ℝ≥0∞)) ∧
  iIndepFun (fun j (stream : ℕ → Bool) => stream j) fairBitStreamMeasure

/-- The Euclidean, matrix, and logarithmic notation of §1.1. -/
def notationConventions : Prop :=
  (∀ {n : ℕ} {𝕜 : Type} [RCLike 𝕜] (x : EuclideanSpace 𝕜 (Fin n)),
    vectorNorm x = Real.sqrt (∑ i, ‖x i‖ ^ 2)) ∧
  (∀ {m n : ℕ} {𝕜 : Type} [RCLike 𝕜] (a : Matrix (Fin m) (Fin n) 𝕜),
    matrixNorm a = ‖LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin a)‖ ∧
    frobeniusNorm a = Real.sqrt (∑ i, ∑ j, ‖a i j‖ ^ 2)) ∧
  (∀ {n : ℕ} {𝕜 : Type} [RCLike 𝕜] (i j : Fin n),
    identity n (𝕜 := 𝕜) i j = if i = j then 1 else 0) ∧
  (∀ {m n : ℕ} (a : Matrix (Fin m) (Fin n) ℝ) (i : Fin n) (j : Fin m),
    transpose a i j = a j i) ∧
  (∀ {m n : ℕ} (a : Matrix (Fin m) (Fin n) ℂ) (i : Fin n) (j : Fin m),
    adjoint a i j = star (a j i)) ∧
  (∀ {n : ℕ} (a : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n),
    imaginaryPart a i j = (a i j - star (a j i)) / (2 * Complex.I)) ∧
  (∀ x : ℝ, 0 < x →
    binaryLog x = naturalLog x / naturalLog 2 ∧ Real.exp (naturalLog x) = x)

/-- Proof-free contract for the common arithmetic and work model in §1.1. -/
def arithmeticWorkModelSuccessor : Prop :=
  positivePrecisionArithmetic ∧ executionResources ∧ notationConventions

end NumStability.CertifiedTridiagonalEigenpairs.SourceTargets
