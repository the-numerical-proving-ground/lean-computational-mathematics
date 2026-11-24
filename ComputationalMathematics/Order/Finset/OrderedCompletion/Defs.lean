import Mathlib.Data.Finset.Fold
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Fin
import Mathlib.Order.Fin.Basic

/-!
# Completing an ordered list at prescribed positions

Exact finite order constructions for nonnegative lists. No numerical algorithm
or operation-count bound is asserted by these mathematical definitions.
-/

namespace NumStability.OrderStatistics

noncomputable section

/-- Maximum of zero and the selected values at or before `i`. -/
def selectedLowerEnvelope {n k : ℕ} (I : Fin k → Fin n)
    (s : Fin k → ℝ) (i : Fin n) : ℝ :=
  (Finset.univ.filter fun j : Fin k => I j ≤ i).fold max 0 s

/-- Raise a reference entry to its selected lower bound. -/
def raiseToSelectedLower {n k : ℕ} (I : Fin k → Fin n)
    (truth : Fin n → ℝ) (s : Fin k → ℝ) (i : Fin n) : ℝ :=
  max (truth i) (selectedLowerEnvelope I s i)

/-- Clip the raised reference entry by all selected values at or after it.
An absent upper bound leaves the real-valued seed unchanged, without an infinity
sentinel. Inclusive comparisons retain selected positions on both sides.
-/
def completeSelectedValues {n k : ℕ} (I : Fin k → Fin n)
    (truth : Fin n → ℝ) (s : Fin k → ℝ) (i : Fin n) : ℝ :=
  (Finset.univ.filter fun j : Fin k => i ≤ I j).fold min
    (raiseToSelectedLower I truth s i) s

end

end NumStability.OrderStatistics
