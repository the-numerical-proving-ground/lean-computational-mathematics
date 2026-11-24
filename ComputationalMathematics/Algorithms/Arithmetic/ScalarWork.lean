import Mathlib.Data.Nat.Basic

/-!
# Scalar-operation work and storage accounting

A trace records charged operations in an arithmetic model with a precision cap.
Its length measures arithmetic work. Space is the peak number of simultaneous
scalar words. An execution proof supplies the charged operations and live-word
counts for its algorithm.
-/

namespace NumStability.ScalarWork

/-- Chargeable primitive steps. A fair-bit event charges for the generation of
one bit; an execution's probability model specifies the law of the draws. -/
inductive Step where
  | arithmetic (bits : ℕ)
  | conversion (source destination : ℕ)
  | comparison
  | index
  | fairBit
  | readExponent
  | scaleByPowerOfTwo

/-- Arithmetic is allowed at up to the cap. Both precisions of a conversion
must be within the cap. Comparisons, index operations, single fair-bit draws
and the representation operations have constant cost. -/
def Step.Allowed (cap : ℕ) : Step → Prop
  | .arithmetic bits => 2 ≤ bits ∧ bits ≤ cap
  | .conversion source destination =>
    2 ≤ source ∧ source ≤ cap ∧ 2 ≤ destination ∧ destination ≤ cap
  | _ => True

/-- All charged operations in an execution respect its precision cap. -/
def TraceAllowed (cap : ℕ) (trace : List Step) : Prop :=
  ∀ step ∈ trace, step.Allowed cap

/-- Each recorded step consumes one unit of work. -/
def work (trace : List Step) : ℕ :=
  trace.length

/-- Maximum number of simultaneous scalar words, given the live-word count at
each point of the execution. -/
def storage (liveWords : List ℕ) : ℕ :=
  liveWords.foldr max 0

theorem storage_le_iff {liveWords : List ℕ} {limit : ℕ} :
    storage liveWords ≤ limit ↔ ∀ words ∈ liveWords, words ≤ limit := by
  induction liveWords with
  | nil => simp [storage]
  | cons words liveWords ih =>
    change max words (storage liveWords) ≤ limit ↔ _
    rw [Nat.max_le, List.forall_mem_cons, ih]

end NumStability.ScalarWork
