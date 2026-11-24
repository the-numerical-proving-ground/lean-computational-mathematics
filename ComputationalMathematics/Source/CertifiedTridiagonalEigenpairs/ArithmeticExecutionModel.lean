import ComputationalMathematics.Algorithms.Arithmetic.ScalarWork
import ComputationalMathematics.Analysis.FloatingPointArithmetic.UnboundedBinary.PositivePrecision
import ComputationalMathematics.Source.CertifiedTridiagonalEigenpairs.Parameters
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.Distributions.Uniform

/-!
# Arithmetic executions and their charges

A routine has a common input and final output precision, a specified working
precision, and a precision cap supplied by the theorem that invokes it. Each
arithmetic step rounds at the working precision. Conversions carry both
precisions explicitly and are the steps that can change precision. A random
stream supplies the bit values used by the bit-draw steps in order.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace NumStability.CertifiedTridiagonalEigenpairs

open FloatingPointFormat.UnboundedBinary

/-- A scalar at positive precision, with its exact represented real value. -/
abbrev WordAt (p : ℕ) (hp : 0 < p) := {x : ℝ // NativeAt p hp x}

/-- Round the real input to a stored word at the specified precision. -/
noncomputable def roundWordAt (p : ℕ) (hp : 0 < p) (x : ℝ) : WordAt p hp :=
  ⟨roundAt p hp x, (roundAt_nearest p hp x).1⟩

/-- A conversion rounds the represented value at its destination precision. -/
noncomputable def convertWordAt {s : ℕ} {hs : 0 < s} (t : ℕ) (ht : 0 < t)
    (word : WordAt s hs) : WordAt t ht :=
  roundWordAt t ht word.val

/-- The five real scalar primitives with stored operands and their real
division and square-root domains. -/
inductive ArithmeticOperationAt (p : ℕ) (hp : 0 < p) where
  | add (x y : WordAt p hp)
  | sub (x y : WordAt p hp)
  | mul (x y : WordAt p hp)
  | div (x y : WordAt p hp) (hy : y.val ≠ 0)
  | sqrt (x : WordAt p hp) (hx : 0 ≤ x.val)

namespace ArithmeticOperationAt

/-- Exact real result used to specify the rounded result. -/
noncomputable def exactValue {p : ℕ} {hp : 0 < p} : ArithmeticOperationAt p hp → ℝ
  | .add x y => x.val + y.val
  | .sub x y => x.val - y.val
  | .mul x y => x.val * y.val
  | .div x y _ => x.val / y.val
  | .sqrt x _ => Real.sqrt x.val

noncomputable def eval {p : ℕ} {hp : 0 < p}
    (operation : ArithmeticOperationAt p hp) : WordAt p hp :=
  roundWordAt p hp operation.exactValue

private noncomputable def ofStoredWord {p : ℕ} {hp : 2 ≤ p} (word : Word p hp) :
    WordAt p (by omega) :=
  ⟨word.value, (nativeAt_iff_native p hp word.value).mpr word.native_value⟩

/-- Read a scalar operation from the concrete stored-word implementation
used by the existing Sturm and refinement routines. -/
noncomputable def ofStoredOperation {p : ℕ} {hp : 2 ≤ p} :
    ScalarOperation p hp → ArithmeticOperationAt p (by omega)
  | .add x y => .add (ofStoredWord x) (ofStoredWord y)
  | .sub x y => .sub (ofStoredWord x) (ofStoredWord y)
  | .mul x y => .mul (ofStoredWord x) (ofStoredWord y)
  | .div x y hy => .div (ofStoredWord x) (ofStoredWord y) hy
  | .sqrt x hx => .sqrt (ofStoredWord x) hx

end ArithmeticOperationAt

/-- Admissible I/O and working precisions for a routine under its applicable
theorem's cap. The natural number p is shared by inputs and final output. -/
structure RoutinePrecision (n p q cap : ℕ) : Prop where
  dimension_pos : 0 < n
  guard : precisionGuard n p
  input_pos : 0 < p
  working_pos : 0 < q
  input_le_cap : p ≤ cap
  working_le_cap : q ≤ cap

/-- Executed steps whose precision-bearing operands retain their values. The
arithmetic constructor uses the specified routine precision q. -/
inductive ExecutedStep (q : ℕ) (hq : 0 < q) (cap : ℕ) where
  | arithmetic (operation : ArithmeticOperationAt q hq)
  | conversion (s t : ℕ) (hs : 0 < s) (ht : 0 < t)
      (hsCap : s ≤ cap) (htCap : t ≤ cap) (word : WordAt s hs)
  | comparison
  | index
  | fairBit (value : Bool)
  | readExponent
  | scaleByPowerOfTwo

namespace ExecutedStep

/-- Project an executed step to the scalar-work charge. -/
def charge {q cap : ℕ} {hq : 0 < q} : ExecutedStep q hq cap → ScalarWork.Step
  | .arithmetic _ => .arithmetic q
  | .conversion s t _ _ _ _ _ => .conversion s t
  | .comparison => .comparison
  | .index => .index
  | .fairBit _ => .fairBit
  | .readExponent => .readExponent
  | .scaleByPowerOfTwo => .scaleByPowerOfTwo

def bitValue {q cap : ℕ} {hq : 0 < q} : ExecutedStep q hq cap → Option Bool
  | .fairBit bit => some bit
  | _ => none

end ExecutedStep

/-- Precision admissibility for the generic source model, including one bit. -/
def chargeAllowed (cap : ℕ) : ScalarWork.Step → Prop
  | .arithmetic bits => 0 < bits ∧ bits ≤ cap
  | .conversion s t => 0 < s ∧ s ≤ cap ∧ 0 < t ∧ t ≤ cap
  | _ => True

/-- The precision floor that holds for arithmetic and conversions in the
existing concrete two-or-more-bit executions. -/
def chargeAtLeastTwo : ScalarWork.Step → Prop
  | .arithmetic p => 2 ≤ p
  | .conversion s t => 2 ≤ s ∧ 2 ≤ t
  | _ => True

/-- The bit source supplies a fresh independent fair value whenever queried
at the next coordinate. -/
noncomputable def fairBitStreamMeasure : Measure (ℕ → Bool) :=
  Measure.infinitePi fun _ : ℕ => (PMF.uniformOfFintype Bool).toMeasure

/-- One finite execution. Each recorded draw consumes the next coordinate of
the same stream. The storage list records simultaneous live-word counts at
the execution points. -/
structure ArithmeticExecution {n p q cap : ℕ}
    (precision : RoutinePrecision n p q cap) (stream : ℕ → Bool) where
  input : List (WordAt p precision.input_pos)
  output : List (WordAt p precision.input_pos)
  steps : List (ExecutedStep q precision.working_pos cap)
  drawsFromStream :
    steps.filterMap ExecutedStep.bitValue =
      (List.range (steps.filterMap ExecutedStep.bitValue).length).map stream
  liveWords : List ℕ

namespace ArithmeticExecution

def trace {n p q cap : ℕ} {precision : RoutinePrecision n p q cap}
    {stream : ℕ → Bool} (run : ArithmeticExecution precision stream) : List ScalarWork.Step :=
  run.steps.map ExecutedStep.charge

end ArithmeticExecution

end NumStability.CertifiedTridiagonalEigenpairs
