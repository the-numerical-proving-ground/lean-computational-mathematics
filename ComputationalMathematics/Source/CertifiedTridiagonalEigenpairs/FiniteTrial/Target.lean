import ComputationalMathematics.Analysis.Eigenvalues.TridiagonalRefinementExecution
import ComputationalMathematics.Source.CertifiedTridiagonalEigenpairs.FiniteSampler
import ComputationalMathematics.Source.CertifiedTridiagonalEigenpairs.IndexedRefinement.Target
import ComputationalMathematics.Source.CertifiedTridiagonalEigenpairs.RequestedAdjacentGaps.Target

/-! The rounded one-trial gate and its deterministic contract for §3 and §5. -/

namespace NumStability.CertifiedTridiagonalEigenpairs

open FloatingPointFormat.UnboundedBinary NoisyRankCertificate ScalarWork

/-- The requested ranks and their existing neighbors, in one-based numbering. -/
def requestedNeighborRanks (N : ℕ) (J : Finset ℕ) : Finset ℕ :=
  (J ∪ J.image (· - 1) ∪ J.image (· + 1)) ∩ Finset.Icc 1 N

/-- Mark one existing one-based rank in a flag array. -/
def markTrialRank {N : ℕ} (flags : Vector Bool N) (rank : ℕ) : Vector Bool N :=
  if h : 1 ≤ rank ∧ rank ≤ N then flags.set (rank - 1) true (by omega) else flags

/-- A flag vector recording which ranks are requested. -/
noncomputable def trialRequestedFlags (N : ℕ) (J : Finset ℕ) : Vector Bool N :=
  J.toList.foldl markTrialRank (Vector.replicate N false)

/-- A flag vector recording which ranks are requested or are existing neighbors. -/
noncomputable def trialNeighborFlags (N : ℕ) (J : Finset ℕ) : Vector Bool N :=
  (J.toList.flatMap fun j => [j, j - 1, j + 1]).foldl markTrialRank (Vector.replicate N false)

/-- The ranks `J⁺`, represented in ascending scan order. -/
noncomputable def trialRanks (n : ℕ) (J : Finset ℕ) : List (Fin (n + 1)) :=
  let flags := trialNeighborFlags (n + 1) J
  (List.finRange (n + 1)).filter fun j => flags[j.val]

/-- The tested edges, in ascending scan order. An edge has one-based ranks
`e.val + 1` and `e.val + 2`. -/
noncomputable def trialEdges (n : ℕ) (J : Finset ℕ) : List (Fin n) :=
  let flags := trialRequestedFlags (n + 1) J
  (List.finRange n).filter fun e => flags[e.castSucc.val] || flags[e.succ.val]

/-- Working words at the precision determined by dimension, requested count and input precision. -/
abbrev TrialWord (n : ℕ) (J : Finset ℕ) (p : ℕ) :=
  Word (workingPrecision (n + 1) J.card p) (workingPrecision_ge_two (n + 1) J.card p)

/-- The original normalized diagonal is sampled afresh on every trial. -/
noncomputable def trialDiagonalWords {n p : ℕ} {J : Finset ℕ}
    (a : Fin (n + 1) → TrialWord n J p)
    (words : Fin (n + 1) → FairBitWord (rngBits (n + 1) J.card)) :
    Vector (TrialWord n J p) (n + 1) :=
  let q := workingPrecision (n + 1) J.card p
  let hq := workingPrecision_ge_two (n + 1) J.card p
  let b := rngBits (n + 1) J.card
  Vector.ofFn fun i => Word.round q hq
    ((a i).value + formCenter q hq p b (accumulate q hq b (words i)))

/-- Indexed read from the stored diagonal. -/
noncomputable def trialDiagonal {n p : ℕ} {J : Finset ℕ}
    (a : Fin (n + 1) → TrialWord n J p)
    (words : Fin (n + 1) → FairBitWord (rngBits (n + 1) J.card))
    (i : Fin (n + 1)) : TrialWord n J p :=
  (trialDiagonalWords a words)[i.val]

/-- The matrix stored by this trial, with the original subdiagonal. -/
noncomputable def trialMatrix {n p : ℕ} {J : Finset ℕ}
    (a : Fin (n + 1) → TrialWord n J p) (b : Fin n → TrialWord n J p)
    (words : Fin (n + 1) → FairBitWord (rngBits (n + 1) J.card)) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  sturmTridiagonal (fun i => (trialDiagonal a words i).value) (fun j => (b j).value)

/-- The instrumented refinement used to specify the label and charge its trace. -/
noncomputable def trialRefinement {n p : ℕ} {J : Finset ℕ}
    (a : Fin (n + 1) → TrialWord n J p) (b : Fin n → TrialWord n J p)
    (words : Fin (n + 1) → FairBitWord (rngBits (n + 1) J.card)) (i : Fin (n + 1)) :=
  tridiagonalRefinement (gapToleranceExponent (n + 1) J.card p) i (trialDiagonal a words) b

/-- The stored comparison threshold. Its value is exactly `3*g/4`. -/
noncomputable def trialThreshold (n : ℕ) (J : Finset ℕ) (p : ℕ) : TrialWord n J p :=
  let m := p + 3 * Nat.clog 2 (n + 1) + Nat.clog 2 J.card + 18
  (Word.round _ _ 3).scale (-(m : ℤ) - 2)

/-- Each tested difference is computed with one rounded subtraction. -/
noncomputable def trialDifference {n p : ℕ} {J : Finset ℕ}
    (a : Fin (n + 1) → TrialWord n J p) (b : Fin n → TrialWord n J p)
    (words : Fin (n + 1) → FairBitWord (rngBits (n + 1) J.card)) (e : Fin n) :
    TrialWord n J p :=
  (ScalarOperation.sub (trialRefinement a b words e.succ).label
    (trialRefinement a b words e.castSucc).label).eval

/-- Scan the marked ranks and store each resulting label once. The two gate
operands are subsequently read from this fixed-size array. -/
noncomputable def trialCachedLabels {n p : ℕ} {J : Finset ℕ}
    (diag : Vector (TrialWord n J p) (n + 1)) (b : Fin n → TrialWord n J p) :
    Vector (TrialWord n J p) (n + 1) :=
  let flags := trialNeighborFlags (n + 1) J
  Vector.ofFn fun i =>
    if flags[i.val] then
      runTridiagonalRefinement (gapToleranceExponent (n + 1) J.card p) i
        (fun j => diag[j.val]) b
    else .zero

/-- The trial retains the stored diagonal alongside its acceptance decision. -/
structure FiniteTrialResult (n : ℕ) (J : Finset ℕ) (p : ℕ) where
  diagonal : Vector (TrialWord n J p) (n + 1)
  accepted : Bool

/-- Sample the input diagonal once, refine the marked ranks, and test the
rounded adjacent differences touching a requested rank. -/
noncomputable def trialRun (n p : ℕ) (J : Finset ℕ)
    (a : Fin (n + 1) → TrialWord n J p) (b : Fin n → TrialWord n J p)
    (words : Fin (n + 1) → FairBitWord (rngBits (n + 1) J.card)) : FiniteTrialResult n J p :=
  letI := Classical.propDecidable
  let diagonal := trialDiagonalWords a words
  let labels := trialCachedLabels diagonal b
  let threshold := trialThreshold n J p
  let checks := (trialEdges n J).map fun e =>
    let diff := (ScalarOperation.sub labels[e.succ.val] labels[e.castSucc.val]).eval
    decide (threshold.value ≤ diff.value)
  ⟨diagonal, checks.all id⟩

/-- The gate accepts precisely when all the rounded adjacent differences
touching a requested rank meet the stored threshold. -/
noncomputable def trialAccepts (n p : ℕ) (J : Finset ℕ)
    (a : Fin (n + 1) → TrialWord n J p) (b : Fin n → TrialWord n J p)
    (words : Fin (n + 1) → FairBitWord (rngBits (n + 1) J.card)) : Bool :=
  (trialRun n p J a b words).accepted

/-- Trace for setting and scanning the two index flags, sampling the new
diagonal, refining the visited ranks once, and comparing each tested edge. -/
noncomputable def trialTrace {n p : ℕ} {J : Finset ℕ}
    (a : Fin (n + 1) → TrialWord n J p) (b : Fin n → TrialWord n J p)
    (words : Fin (n + 1) → FairBitWord (rngBits (n + 1) J.card)) : List Step :=
  let q := workingPrecision (n + 1) J.card p
  List.replicate (12 * (n + 1 + J.card)) .index ++
    samplerTrace (n + 1) J.card p ++
    (trialRanks n J).flatMap (fun i => trialRefinement a b words i |>.trace) ++
    [.scaleByPowerOfTwo] ++
    (trialEdges n J).flatMap (fun _ => [.index, .index, .arithmetic q, .comparison])

namespace SourceTargets

/-- Deterministic part of the cost and reliability theorem for one finite trial.
The separately stated probability bound uses the same gate on the same bit words. -/
def finiteTrialCertificate : Prop :=
  ∀ (n p : ℕ) (J : Finset ℕ) (a : Fin (n + 1) → TrialWord n J p)
    (b : Fin n → TrialWord n J p),
    2 ≤ n + 1 → precisionGuard (n + 1) p → J.Nonempty → J ⊆ Finset.Icc 1 (n + 1) →
    (∀ i, |(a i).value| ≤ 1 / 4) → (∀ i, |(b i).value| ≤ 1 / 4) →
    ∀ words : Fin (n + 1) → FairBitWord (rngBits (n + 1) J.card),
    let S := sturmTridiagonal (fun i => (a i).value) (fun i => (b i).value)
    let M := trialMatrix a b words
    let spectrum := ascendingEigenvalue
      (sturmTridiagonal_isHermitian (fun i => (trialDiagonal a words i).value) (fun i => (b i).value))
    let g := gapScale (n + 1) J.card p
    let trace := trialTrace a b words
    (trialThreshold n J p).value = 3 * g / 4 ∧
    realMatrixOperatorNorm (M - S) ≤ perturbationScale p + 2 * workingRoundoff (n + 1) J.card p ∧
    perturbationScale p + 2 * workingRoundoff (n + 1) J.card p ≤ unitRoundoff p / 128 ∧
    realMatrixOperatorNorm M < 1 ∧
    (∀ i j, i ≠ j → M i j = S i j) ∧
    (trialAccepts n p J a b words = true →
      ∀ j : Fin (n + 1), j.val + 1 ∈ J → ∀ i : Fin (n + 1), i ≠ j →
        certifiedGap (n + 1) J.card p < |spectrum i - spectrum j|) ∧
    trace.countP isFairBit = (n + 1) * rngBits (n + 1) J.card ∧
    work trace ≤ 2000 * (n + 1) * J.card * (p + Nat.clog 2 (n + 1)) ∧
    TraceAllowed (workingPrecision (n + 1) J.card p) trace

/-- The good continuous event implies that this exact finite gate accepts,
whenever the coupled diagonal shifts lie in their decoding cells. -/
def finiteTrialCoupledAcceptance : Prop :=
  ∀ (n p : ℕ) (J : Finset ℕ) (a : Fin (n + 1) → TrialWord n J p)
    (b : Fin n → TrialWord n J p),
    2 ≤ n + 1 → precisionGuard (n + 1) p →
    (∀ i, |(a i).value| ≤ 1 / 4) → (∀ i, |(b i).value| ≤ 1 / 4) →
    ∀ (words : Fin (n + 1) → FairBitWord (rngBits (n + 1) J.card)) (V : Fin (n + 1) → ℝ),
    let A := fun i => (a i).value + V i
    let spectrum := ascendingEigenvalue (sturmTridiagonal_isHermitian A (fun i => (b i).value))
    let g := gapScale (n + 1) J.card p
    (∀ i, |V i - cellCenter (perturbationScale p) (rngBits (n + 1) J.card)
      (trialDraws (n + 1) J.card words i)| ≤ g / 64) →
    (∀ e : Fin n, e.val + 1 ∈ requestedAdjacentGapIndices (n + 1) J →
      g < spectrum e.succ - spectrum e.castSucc) →
    trialAccepts n p J a b words = true

end SourceTargets
end NumStability.CertifiedTridiagonalEigenpairs
