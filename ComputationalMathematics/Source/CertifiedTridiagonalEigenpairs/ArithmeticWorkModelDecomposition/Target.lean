import ComputationalMathematics.Source.CertifiedTridiagonalEigenpairs.ArithmeticExecutionModel
import ComputationalMathematics.Source.CertifiedTridiagonalEigenpairs.ArithmeticNotation
import ComputationalMathematics.Source.CertifiedTridiagonalEigenpairs.BidiagonalSVDPrecision

/-! Proof-free obligations for the arithmetic and work model in §1.1. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace NumStability.CertifiedTridiagonalEigenpairs.SourceTargets

open FloatingPointFormat.UnboundedBinary
open ScalarWork
open ArithmeticNotation

/-- Unbounded binary representability, nearest rounding and its error,
including the standard nearest-even convention at a one-bit midpoint. -/
def binaryRoundingModel : Prop :=
  (∀ (t : ℕ) (ht : 0 < t) (x : ℝ),
    FloatingPointFormat.nearestRoundingIn (NativeAt t ht) x (roundAt t ht x) ∧
    |roundAt t ht x - x| ≤ (2 : ℝ) ^ (-(t : ℤ)) * |x|) ∧
  (∀ (t : ℕ) (ht : 2 ≤ t) (x : ℝ), x ≠ 0 →
    (format t ht).sourceRoundToEvenEvidence x (roundAt t (by omega) x)) ∧
  (∀ x : ℝ, x ≠ 0 →
    (positiveFormat 1 (by decide)).sourceRoundAwayEvidence x (roundAt 1 (by decide) x)) ∧
  (∀ m : ℕ, (positiveFormat 1 (by decide)).normalizedMantissa m → m = 1)

/-- Rounded operations and explicit conversions. Binary-power scaling
preserves the represented value up to that exact factor. -/
def roundedScalarOperations : Prop :=
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

/-- The guard and admissible precisions for the exact branches, the
tridiagonal computation, and the bidiagonal auxiliary phase. -/
def arithmeticRoutinePrecisions : Prop :=
  (∀ n p : ℕ, 0 < n → precisionGuard n p → 7 ≤ p) ∧
  (∀ n k p : ℕ, 0 < n → precisionGuard n p →
    RoutinePrecision n p p p ∧
    RoutinePrecision n p (workingPrecision n k p) (workingPrecision n k p) ∧
    RoutinePrecision n p (svdAuxiliaryPrecision k p) (svdWorkingPrecision n k p))

/-- A routine's charged operations and peak scalar-word storage.
Each bit draw consumes the next coordinate of the supplied stream. -/
def arithmeticExecutionCharges : Prop :=
  (∀ {n p q cap : ℕ} (prec : RoutinePrecision n p q cap) (stream : ℕ → Bool)
    (run : ArithmeticExecution prec stream),
    (∀ step ∈ run.trace, chargeAllowed cap step) ∧
    work run.trace = run.steps.length ∧
    (∀ limit : ℕ, storage run.liveWords ≤ limit ↔ ∀ words ∈ run.liveWords, words ≤ limit) ∧
    run.steps.filterMap ExecutedStep.bitValue =
      (List.range (run.steps.filterMap ExecutedStep.bitValue).length).map stream) ∧
  (∀ cap : ℕ, ∀ step : Step, chargeAtLeastTwo step →
    (step.Allowed cap ↔ chargeAllowed cap step))

/-- The law of the exact stream used for fair-bit generation. -/
def arithmeticFairBitLaw : Prop :=
  (∀ j : ℕ, ∀ b : Bool, fairBitStreamMeasure {stream | stream j = b} = (1 / 2 : ℝ≥0∞)) ∧
  iIndepFun (fun j (stream : ℕ → Bool) => stream j) fairBitStreamMeasure

/-- The vector Euclidean norm, induced matrix norm, and Frobenius norm. -/
def arithmeticNormNotation : Prop :=
  (∀ {n : ℕ} {𝕜 : Type} [RCLike 𝕜] (x : EuclideanSpace 𝕜 (Fin n)),
    vectorNorm x = Real.sqrt (∑ i, ‖x i‖ ^ 2)) ∧
  (∀ {m n : ℕ} {𝕜 : Type} [RCLike 𝕜] (a : Matrix (Fin m) (Fin n) 𝕜),
    matrixNorm a = ‖LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin a)‖ ∧
    frobeniusNorm a = Real.sqrt (∑ i, ∑ j, ‖a i j‖ ^ 2))

/-- Identity, real transpose, conjugate transpose, and matrix imaginary part. -/
def arithmeticMatrixNotation : Prop :=
  (∀ {n : ℕ} {𝕜 : Type} [RCLike 𝕜] (i j : Fin n),
    identity n (𝕜 := 𝕜) i j = if i = j then 1 else 0) ∧
  (∀ {m n : ℕ} (a : Matrix (Fin m) (Fin n) ℝ) (i : Fin n) (j : Fin m),
    transpose a i j = a j i) ∧
  (∀ {m n : ℕ} (a : Matrix (Fin m) (Fin n) ℂ) (i : Fin n) (j : Fin m),
    adjoint a i j = star (a j i)) ∧
  (∀ {n : ℕ} (a : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n),
    imaginaryPart a i j = (a i j - star (a j i)) / (2 * Complex.I))

/-- The binary and natural logarithms on their positive domain. -/
def arithmeticLogNotation : Prop :=
  ∀ x : ℝ, 0 < x →
    binaryLog x = naturalLog x / naturalLog 2 ∧ Real.exp (naturalLog x) = x

/-- All obligations together, without altering the original target. -/
def arithmeticWorkModelParts : Prop :=
  binaryRoundingModel ∧ roundedScalarOperations ∧
    arithmeticRoutinePrecisions ∧ arithmeticExecutionCharges ∧ arithmeticFairBitLaw ∧
    arithmeticNormNotation ∧ arithmeticMatrixNotation ∧ arithmeticLogNotation

end NumStability.CertifiedTridiagonalEigenpairs.SourceTargets
