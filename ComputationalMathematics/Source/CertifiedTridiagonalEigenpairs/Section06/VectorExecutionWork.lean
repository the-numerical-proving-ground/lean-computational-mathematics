import ComputationalMathematics.Source.CertifiedTridiagonalEigenpairs.Section06.CachedExecutionWork
import ComputationalMathematics.Source.CertifiedTridiagonalEigenpairs.Section06.VectorExecution

/-! # Work and accuracy of the Section 6 vector computation -/

open Matrix WithLp
open scoped Matrix.Norms.L2Operator

namespace NumStability.CertifiedTridiagonalEigenpairs

open FloatingPointFormat.UnboundedBinary ScalarWork

private def imaginaryProjectionStep : List Step :=
  [.comparison, .index, .index, .index, .index]

private def firstSquareStep (q : ℕ) : List Step :=
  [.comparison, .index, .index, .arithmetic q]

private def remainingSquareStep (q : ℕ) : List Step :=
  [.comparison, .index, .index, .index, .arithmetic q, .arithmetic q]

private def normalizationOutputStep (q p : ℕ) : List Step :=
  [.comparison, .index, .index, .index, .arithmetic q, .conversion q p, .index]

/-- The cache schedule followed by the imaginary projection and the two
indexed normalization passes. The projection reads a stored real component.
The normalization uses one rounded square per component, one rounded sum per
component after the first, one rounded square root, and one rounded quotient
and output-precision conversion per component. Includes the comparisons and
index operations of the array loops. -/
def vectorExecutionTrace (q p : ℕ) {n : ℕ} (r : Fin n) : List Step :=
  vectorCachedExecutionTrace q r ++
    (List.range n).flatMap (fun _ => imaginaryProjectionStep) ++ [.comparison] ++
    firstSquareStep q ++
    (List.range (n - 1)).flatMap (fun _ => remainingSquareStep q) ++
    [.comparison, .arithmetic q] ++
    (List.range n).flatMap (fun _ => normalizationOutputStep q p) ++ [.comparison]

/-- During projection retain the source entries, complex column, real input,
and scalar loop state. The cached complex column is released before the
normalization passes, which keep the input, denominator and output array. -/
def vectorExecutionLiveWords {n : ℕ} (r : Fin n) : List ℕ :=
  vectorCachedExecutionLiveWords r ++ [5 * n + 5, 4 * n + 5, n]

private theorem length_flatMap_const {α β : Type*} (xs : List α) (ys : List β) :
    (xs.flatMap (fun _ => ys)).length = xs.length * ys.length := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [ih, Nat.add_mul, Nat.add_comm]

private theorem traceAllowed_flatMap_const {cap : ℕ} {α : Type*}
    (xs : List α) (ys : List Step) (h : TraceAllowed cap ys) :
    TraceAllowed cap (xs.flatMap (fun _ => ys)) := by
  intro step hstep
  obtain ⟨_, _, hi⟩ := List.mem_flatMap.mp hstep
  exact h step hi

/-- Absolute linear work and storage bounds for the executed schedule. The
working precision is also the cap for the final conversion when p ≤ q. -/
theorem vectorExecution_resources (q p : ℕ) {n : ℕ} (r : Fin n) (hn : 2 ≤ n)
    (hq : 2 ≤ q) (hp : 2 ≤ p) (hpq : p ≤ q) :
    work (vectorExecutionTrace q p r) ≤ 166 * n ∧
      TraceAllowed q (vectorExecutionTrace q p r) ∧
      storage (vectorExecutionLiveWords r) ≤ 31 * n := by
  constructor
  · have h := vectorCachedExecutionTrace_work q r
    simp only [work] at h
    simp only [vectorExecutionTrace, work, List.length_append, length_flatMap_const,
      List.length_range, imaginaryProjectionStep, firstSquareStep, remainingSquareStep,
      normalizationOutputStep, List.length_cons, List.length_nil, h]
    omega
  constructor
  · have hProj : TraceAllowed q imaginaryProjectionStep := by
      simp [TraceAllowed, imaginaryProjectionStep, Step.Allowed]
    have hFirst : TraceAllowed q (firstSquareStep q) := by
      simp [TraceAllowed, firstSquareStep, Step.Allowed, hq]
    have hSquare : TraceAllowed q (remainingSquareStep q) := by
      simp [TraceAllowed, remainingSquareStep, Step.Allowed, hq]
    have hOutput : TraceAllowed q (normalizationOutputStep q p) := by
      simp [TraceAllowed, normalizationOutputStep, Step.Allowed, hq, hp, hpq]
    have hCache := vectorCachedExecutionTrace_allowed q q r hq le_rfl
    intro step hstep
    simp only [vectorExecutionTrace, List.mem_append] at hstep
    rcases hstep with ((((((hcache | hproj) | hprojEnd) | hfirst) | hsquare) | hsqrt) |
      hout) | hOutEnd
    · exact hCache step hcache
    · exact traceAllowed_flatMap_const (List.range n) _ hProj _ hproj
    · simp [Step.Allowed, List.mem_singleton.mp hprojEnd]
    · exact hFirst step hfirst
    · exact traceAllowed_flatMap_const (List.range (n - 1)) _ hSquare _ hsquare
    · have h : TraceAllowed q [.comparison, .arithmetic q] := by
        simp [TraceAllowed, Step.Allowed, hq]
      exact h step hsqrt
    · exact traceAllowed_flatMap_const (List.range n) _ hOutput _ hout
    · simp [Step.Allowed, List.mem_singleton.mp hOutEnd]
  · rw [storage_le_iff]
    intro words hwords
    rw [vectorExecutionLiveWords, List.mem_append] at hwords
    rcases hwords with hcache | hrest
    · have h := (storage_le_iff.mp (vectorCachedExecutionLiveWords_storage r)) _ hcache
      omega
    · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hrest
      rcases hrest with rfl | rfl | rfl <;> omega

/-- Section 6's deterministic accuracy and work theorem. Both the resource
bounds and the output refer to the shared cached sweeps and least maximizing score
execution. The result is stored at precision p, the divisors are positive,
and the signed error is bounded by 4u. -/
theorem roundedTridiagonalVectorAccuracyAndWork
    {n p q : ℕ} (hn : 2 ≤ n) (hp : 2 ≤ p) (hq : 2 ≤ q)
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsSymm) (hAnorm : ‖A‖ ≤ 2)
    (hband : ∀ i j : Fin n, i.val + 1 < j.val ∨ j.val + 1 < i.val → A i j = 0)
    (hb : ∀ i j : Fin n, i.val + 1 = j.val → |A i j| ≤ 1)
    (hNativeA : ∀ i j : Fin n, Native q hq (A i j))
    (j : Fin n) (v : EuclideanSpace ℝ (Fin n)) (hv : ‖v‖ = 1)
    (heig : A *ᵥ v.ofLp = (MatrixResolvent.isHermitian_map_ofReal hA).eigenvalues j • v.ofLp)
    {shift η Δ : ℝ} (hNativeShift : Native q hq shift)
    (hηpow : ∃ m : ℤ, η = (2 : ℝ) ^ m) (hηmax : η ≤ 1 / 2)
    (hΔ : 0 < Δ) (hguard : (n : ℝ) * unitRoundoff p ≤ 1 / 128)
    (hηprec : η ≤ Δ * Real.sqrt (unitRoundoff p) / (16 * (n : ℝ) ^ (1 / 4 : ℝ)))
    (hnear : |shift - (MatrixResolvent.isHermitian_map_ofReal hA).eigenvalues j| ≤ η)
    (hgap : ∀ i ≠ j, Δ ≤ |(MatrixResolvent.isHermitian_map_ofReal hA).eigenvalues i -
      (MatrixResolvent.isHermitian_map_ofReal hA).eigenvalues j|)
    (hωη : unitRoundoff q ≤ η / 4096)
    (hωΔ : unitRoundoff q ≤ unitRoundoff p * Δ / 8192)
    (hωn : unitRoundoff q ≤ unitRoundoff p / (65536 * (n : ℝ))) :
    let run := vectorCachedExecution q hq n (by omega)
      (vectorInputDiagonal A shift) (vectorInputEdge A) η
    let trace := vectorExecutionTrace q p run.root
    let liveWords := vectorExecutionLiveWords run.root
    work trace ≤ 166 * n ∧ TraceAllowed q trace ∧ storage liveWords ≤ 31 * n ∧
    vectorPivotDivisorsPositive n q hq (vectorInputDiagonal A shift) (vectorInputEdge A) η ∧
      ∃ hx : Word.euclidean (vectorComputedImaginary hq (by omega) A shift η) ≠ 0,
        0 < (Word.roundedNormScan (vectorComputedImaginaryArray hq (by omega) A shift η)).value ∧
          ∃ σ : ℝ, (σ = -1 ∨ σ = 1) ∧
            ‖Word.euclidean (vectorComputedOutput hp hq (by omega) A shift η hx) - σ • v‖ <
              9 * unitRoundoff p / 4 ∧
            ‖Word.euclidean (vectorComputedOutput hp hq (by omega) A shift η hx) - σ • v‖ ≤
              4 * unitRoundoff p := by
  intro run trace liveWords
  have hpq := vectorOutputPrecision_le_workingPrecision hn hωn
  obtain ⟨hwork, htrace, hstorage⟩ := vectorExecution_resources q p run.root hn hq hp hpq
  exact ⟨hwork, htrace, hstorage, roundedTridiagonalVectorAccuracy hn hp hq A hA hAnorm
    hband hb hNativeA j v hv heig hNativeShift hηpow hηmax hΔ hguard hηprec hnear hgap
    hωη hωΔ hωn⟩

end NumStability.CertifiedTridiagonalEigenpairs
