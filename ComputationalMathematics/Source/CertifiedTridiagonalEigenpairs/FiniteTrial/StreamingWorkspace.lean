import ComputationalMathematics.Source.CertifiedTridiagonalEigenpairs.FiniteTrial.Proof

/-! Read-only bit blocks can be supplied one bit at a time to the finite gate. -/

namespace NumStability.CertifiedTridiagonalEigenpairs

open FloatingPointFormat.UnboundedBinary ScalarWork

/-- Sequentially read the fair-bit word using a single rounded accumulator. -/
noncomputable def accumulateStreamingBits (q : ℕ) (hq : 2 ≤ q) (m : ℕ)
    (bits : FairBitWord m) : ℝ :=
  Fin.foldl m (fun r i => roundToEven q hq (2 * r + (bits i).toNat)) 0

theorem accumulateStreamingBits_eq (q : ℕ) (hq : 2 ≤ q) (m : ℕ)
    (bits : FairBitWord m) : accumulateStreamingBits q hq m bits = accumulate q hq m bits := by
  induction m with
  | zero => simp [accumulateStreamingBits, accumulate]
  | succ m ih =>
    unfold accumulateStreamingBits
    rw [Fin.foldl_succ_last]
    change roundToEven q hq (2 * accumulateStreamingBits q hq m (Fin.init bits) +
      (bits (Fin.last m)).toNat) = _
    rw [ih]
    rfl

variable {n p : ℕ} {J : Finset ℕ}

/-- Fill the diagonal array from a fresh read-only bit block. -/
noncomputable def streamingTrialDiagonal
    (a : Fin (n + 1) → TrialWord n J p)
    (bits : Fin (n + 1) → FairBitWord (rngBits (n + 1) J.card)) :
    Vector (TrialWord n J p) (n + 1) :=
  let q := workingPrecision (n + 1) J.card p
  let hq := workingPrecision_ge_two (n + 1) J.card p
  let m := rngBits (n + 1) J.card
  Vector.ofFn fun i => Word.round q hq
    ((a i).value + formCenter q hq p m (accumulateStreamingBits q hq m (bits i)))

theorem streamingTrialDiagonal_eq
    (a : Fin (n + 1) → TrialWord n J p)
    (bits : Fin (n + 1) → FairBitWord (rngBits (n + 1) J.card)) :
    streamingTrialDiagonal a bits = trialDiagonalWords a bits := by
  simp [streamingTrialDiagonal, trialDiagonalWords, accumulateStreamingBits_eq]

/-- The same rounded gate with sequential bit reads, one cached label
per visited rank and the sampled diagonal returned on success. -/
noncomputable def runStreamingTrial (n p : ℕ) (J : Finset ℕ)
    (a : Fin (n + 1) → TrialWord n J p) (b : Fin n → TrialWord n J p)
    (bits : Fin (n + 1) → FairBitWord (rngBits (n + 1) J.card)) : FiniteTrialResult n J p :=
  letI := Classical.propDecidable
  let diagonal := streamingTrialDiagonal a bits
  let labels := trialCachedLabels diagonal b
  let threshold := trialThreshold n J p
  let checks := (trialEdges n J).map fun e =>
    let diff := (ScalarOperation.sub (labels.get e.succ) (labels.get e.castSucc)).eval
    decide (threshold.value ≤ diff.value)
  ⟨diagonal, checks.all id⟩

theorem runStreamingTrial_eq (n p : ℕ) (J : Finset ℕ)
    (a : Fin (n + 1) → TrialWord n J p) (b : Fin n → TrialWord n J p)
    (bits : Fin (n + 1) → FairBitWord (rngBits (n + 1) J.card)) :
    runStreamingTrial n p J a b bits = trialRun n p J a b bits := by
  unfold runStreamingTrial
  rw [streamingTrialDiagonal_eq]
  rfl

/-- Peak scalar-word accounting for the sequential gate. For sampling, the
two input bands, one new band, and constant sampler state suffice. Marking
retains up to three neighbor indices per request, two flag arrays, and the
rank scan. The cache pass adds the fixed requested ranks to its own meter.
Comparison retains the bands, flags, label cache, edges and their Booleans.
The bit stream is an input oracle; only the currently read bit is resident. -/
noncomputable def streamingTrialWorkspace
    (a : Fin (n + 1) → TrialWord n J p) (b : Fin n → TrialWord n J p)
    (bits : Fin (n + 1) → FairBitWord (rngBits (n + 1) J.card)) : ℕ :=
  let N := n + 1
  let k := J.card
  storage
    [3 * N + k + 10, 6 * N + 4 * k + 12,
      storage (trialCacheLiveWords a b bits) + k + 8,
      8 * N + k + 12]

theorem streamingTrialWorkspace_le
    (a : Fin (n + 1) → TrialWord n J p) (b : Fin n → TrialWord n J p)
    (bits : Fin (n + 1) → FairBitWord (rngBits (n + 1) J.card))
    (hkn : J.card ≤ n + 1) :
    streamingTrialWorkspace a b bits ≤ 44 * (n + 1) := by
  have hcache := trialCachedLabels_storage a b bits
  change max _ (max _ (max _ (max _ 0))) ≤ _
  simp only [Nat.max_le]
  omega

end NumStability.CertifiedTridiagonalEigenpairs
