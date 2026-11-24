import ComputationalMathematics.Source.CertifiedTridiagonalEigenpairs.Section06.InverseRecurrence

namespace NumStability.CertifiedTridiagonalEigenpairs.SourceTargets

open scoped Matrix
open FloatingPointFormat.UnboundedBinary

/-- Section 6's rounded reciprocal and outward assignments, using the stored
twist, directional pivots and original edges. -/
def vectorInverseRecurrence : Prop :=
  ∀ (q : ℕ) (hq : 2 ≤ q) (n : ℕ) (a b : ℕ → ℝ) (η : ℝ) (r : Fin n),
    let γ := vectorSweepTwist q hq n a b η r
    let wHat := vectorRoundedInverseColumn q hq n a b η r
    wHat r = roundedTwistReciprocal q hq γ.1 γ.2 ∧
    (wHat r).im = vectorScore q hq γ ∧
    (∀ i ≠ r, wHat i = roundedInverseStep q hq (vectorOutwardEdge q hq n a b η r i 0)
      (wHat (vectorParent r i))) ∧
    ∀ i j : Fin n, j ∈ inversePathIndices r (vectorParent r) n i →
      (vectorOutwardEdge q hq n a b η r j 0).original = 0 → wHat i = 0

/-- Section 6's normwise path errors and nonzero filtered output, for the
perturbed matrix of the structured backward error proof. -/
def vectorRoundedPath : Prop :=
  ∀ (q : ℕ) (hq : 2 ≤ q) (n : ℕ) (_hn : 2 ≤ n) (a b : ℕ → ℝ) (η : ℝ) (r : Fin n)
    (_hη : 0 < η) (u : ℝ),
    u ≤ 1 / 128 →
    (n : ℝ) * unitRoundoff q ≤ 1 / 128 →
    (n : ℝ) * unitRoundoff q ≤ u / 65536 →
    (∀ i : Fin n, η ≤ (vectorLeftSweep q hq a b η i.val).2 ∧
      η ≤ (vectorRightSweep q hq n a b η i.val).2) →
    η ≤ (vectorSweepTwist q hq n a b η r).2 →
    ∀ (E : Matrix (Fin n) (Fin n) ℂ) (β : Fin n → ℂ),
    Eᵀ = E →
    (let d := vectorAssemblyPivot q hq n a b η r
     let L := 1 + rootedEliminationPart r (vectorParent r) β d
     vectorShiftedMatrix n a b η + E = L * Matrix.diagonal d * Lᵀ) →
    (∀ j : Fin n, j ≠ r → (vectorShiftedMatrix n a b η + E) (vectorParent r j) j = β j) →
    (∀ i j : Fin n, i.val + 1 = j.val →
      let e := (vectorShiftedMatrix n a b η + E) i j
      (b i.val = 0 → e = 0) ∧
      (b i.val ≠ 0 → ‖e / (b i.val : ℂ) - 1‖ ≤ 11 * unitRoundoff q)) →
    let w : PiLp 2 (fun _ : Fin n => ℂ) :=
      WithLp.toLp 2 (fun i => (vectorShiftedMatrix n a b η + E)⁻¹ i r)
    let wHat : PiLp 2 (fun _ : Fin n => ℂ) :=
      WithLp.toLp 2 (vectorRoundedInverseColumn q hq n a b η r)
    let y : PiLp 2 (fun _ : Fin n => ℝ) := WithLp.toLp 2 (fun i => (w i).im)
    let yHat : PiLp 2 (fun _ : Fin n => ℝ) := WithLp.toLp 2 (fun i => (wHat i).im)
    ‖wHat - w‖ ≤ 64 * (n : ℝ) * unitRoundoff q * ‖w‖ ∧
    ‖wHat - w‖ ≤ u / 1024 * ‖w‖ ∧
    (‖w‖ ≤ 3 * ‖y‖ → ‖yHat - y‖ ≤ (3 * u / 1024) * ‖y‖ ∧ yHat ≠ 0)

end NumStability.CertifiedTridiagonalEigenpairs.SourceTargets
