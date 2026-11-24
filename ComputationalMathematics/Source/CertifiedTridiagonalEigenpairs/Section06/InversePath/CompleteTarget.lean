import ComputationalMathematics.Source.CertifiedTridiagonalEigenpairs.Section06.InversePath.Target
import ComputationalMathematics.Source.CertifiedTridiagonalEigenpairs.Section06.VectorExecution

namespace NumStability.CertifiedTridiagonalEigenpairs.SourceTargets

open scoped Matrix
open FloatingPointFormat.UnboundedBinary

/-- The rounded selected-column recurrence, its actual real-arithmetic
assignments and positive divisors, and the imaginary vector supplied to normalization. -/
def vectorInverseRecurrenceComplete : Prop :=
  (∀ (q : ℕ) (hq : 2 ≤ q) (n : ℕ) (a b : ℕ → ℝ) (η : ℝ) (r : Fin n),
    let R := roundToEven q hq
    let modulus := fun x y : ℝ => R (R (x ^ 2) + R (y ^ 2))
    let quotient := fun b x y : ℝ =>
      (⟨R (R (b * x) / modulus x y), R (R (b * y) / modulus x y)⟩ : ℂ)
    let product := fun z v : ℂ =>
      (⟨R (R (z.re * v.re) - R (z.im * v.im)),
        R (R (z.re * v.im) + R (z.im * v.re))⟩ : ℂ)
    let γ := vectorSweepTwist q hq n a b η r
    let wHat := vectorRoundedInverseColumn q hq n a b η r
    wHat r = ⟨R (γ.1 / modulus γ.1 γ.2), R (γ.2 / modulus γ.1 γ.2)⟩ ∧
    (wHat r).im = vectorScore q hq γ ∧
    (∀ i j : Fin n, i.val + 1 = j.val → i.val < r.val →
      let d := vectorLeftSweep q hq a b η i.val
      wHat i = if b i.val = 0 then 0 else product (-quotient (b i.val) d.1 d.2) (wHat j)) ∧
    (∀ i j : Fin n, i.val + 1 = j.val → r.val < j.val →
      let d := vectorRightSweep q hq n a b η j.val
      wHat j = if b i.val = 0 then 0 else product (-quotient (b i.val) d.1 d.2) (wHat i)) ∧
    (∀ i j : Fin n, j ∈ inversePathIndices r (vectorParent r) n i →
      (vectorOutwardEdge q hq n a b η r j 0).original = 0 → wHat i = 0) ∧
    (0 < η →
      (∀ i : Fin n, η ≤ (vectorLeftSweep q hq a b η i.val).2 ∧
        η ≤ (vectorRightSweep q hq n a b η i.val).2) →
      η ≤ γ.2 →
      0 < modulus γ.1 γ.2 ∧
      ∀ i : Fin n, i ≠ r →
        let edge := vectorOutwardEdge q hq n a b η r i 0
        0 < modulus edge.pivotRe edge.pivotNegIm)) ∧
  (∀ (q : ℕ) (hq : 2 ≤ q) (n : ℕ) (hn : 0 < n)
      (A : Matrix (Fin n) (Fin n) ℝ) (shift η : ℝ) (i : Fin n),
    let a := vectorInputDiagonal A shift
    let b := vectorInputEdge A
    let r := vectorSelectedIndex q hq n hn a b η
    (vectorComputedImaginary hq hn A shift η i).value =
      (vectorRoundedInverseColumn q hq n a b η r i).im)

/-- Local reciprocal, substituted-edge, quotient, complex-product and propagation
errors, the full product on every outward path, and the selected vector bounds. -/
def vectorRoundedPathComplete : Prop :=
  (∀ (q : ℕ) (hq : 2 ≤ q),
    let ω := unitRoundoff q
    ω ≤ 1 / 128 →
    (∀ x y : ℝ, 0 < y →
      let s := vectorSquaredModulus q hq x y
      let γ := (⟨x, -y⟩ : ℂ)
      0 < s ∧ (1 - ω) ^ 2 * ‖γ‖ ^ 2 ≤ s ∧ s ≤ (1 + ω) ^ 2 * ‖γ‖ ^ 2 ∧
      ‖roundedTwistReciprocal q hq x y - γ⁻¹‖ ≤ 4 * ω * ‖γ⁻¹‖) ∧
    (∀ x y t : ℝ, 0 < y →
      let R := roundToEven q hq
      let s := vectorSquaredModulus q hq x y
      let S := x ^ 2 + y ^ 2
      (∃ c : ℝ, (1 - ω) / (1 + ω) ^ 2 ≤ c ∧ c ≤ (1 + ω) / (1 - ω) ^ 2 ∧
        R (t / s) = c * (t / S)) ∧
      (∃ c : ℝ, (1 - ω) ^ 2 / (1 + ω) ^ 2 ≤ c ∧
        c ≤ (1 + ω) ^ 2 / (1 - ω) ^ 2 ∧ R (R t / s) = c * (t / S))) ∧
    (∀ (b : ℝ) (β : ℂ), b ≠ 0 → ‖β / (b : ℂ) - 1‖ ≤ 11 * ω →
      β ≠ 0 ∧ ‖(b : ℂ) / β - 1‖ ≤ 11 * ω / (1 - 11 * ω) ∧
      11 * ω / (1 - 11 * ω) ≤ 13 * ω) ∧
    (∀ b x y : ℝ, 0 < y →
      let d := (⟨x, -y⟩ : ℂ)
      ‖roundedEdgeQuotient q hq b x y - (b : ℂ) / d‖ ≤ 6 * ω * ‖(b : ℂ) / d‖) ∧
    (∀ z v : ℂ, ‖roundedComplexProduct q hq z v - z * v‖ ≤ 3 * ω * (‖z‖ * ‖v‖)) ∧
    (∀ (edge : InversePathEdge) (v : ℂ), 0 < edge.pivotNegIm →
      let exactProduct := -((edge.original : ℂ) / edge.pivot) * v
      ‖roundedInverseStep q hq edge v - exactProduct‖ ≤
        (6 * ω + 3 * ω * (1 + 6 * ω)) * ‖exactProduct‖ ∧
      6 * ω + 3 * ω * (1 + 6 * ω) ≤ 10 * ω)) ∧
  (∀ (q : ℕ) (hq : 2 ≤ q) (n : ℕ) (_hn : 2 ≤ n),
    let ω := unitRoundoff q
    (n : ℝ) * ω ≤ 1 / 128 →
    ∀ (x y : ℝ), 0 < y → ∀ path : List InversePathEdge, path.length ≤ n →
      (∀ edge ∈ path, 0 < edge.pivotNegIm) →
      (∀ edge ∈ path, ‖edge.absorbed - (edge.original : ℂ)‖ ≤ 11 * ω * ‖(edge.original : ℂ)‖) →
      let w := exactInversePath x y path
      let wHat := roundedInversePath q hq x y path
      let B := (1 + 4 * ω) * (1 + 13 * ω) ^ n * (1 + 10 * ω) ^ n - 1
      (∃ (center : ℂ) (edges ops : List ℂ),
        edges.length = path.length ∧ ops.length = path.length ∧
        ‖center - 1‖ ≤ 4 * ω ∧
        (∀ z ∈ edges, ‖z - 1‖ ≤ 13 * ω) ∧
        (∀ z ∈ ops, ‖z - 1‖ ≤ 10 * ω) ∧
        wHat = w * (center * edges.prod * ops.prod)) ∧
      ‖wHat - w‖ ≤ B * ‖w‖ ∧
      B ≤ Real.exp (25 * (n : ℝ) * ω) - 1 ∧
      Real.exp (25 * (n : ℝ) * ω) - 1 ≤ 64 * (n : ℝ) * ω ∧
      (∀ edge ∈ path, edge.original = 0 → w = 0 ∧ wHat = 0)) ∧
  vectorRoundedPath

end NumStability.CertifiedTridiagonalEigenpairs.SourceTargets
