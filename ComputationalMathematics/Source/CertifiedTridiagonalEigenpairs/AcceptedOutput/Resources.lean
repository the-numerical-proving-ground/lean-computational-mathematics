import ComputationalMathematics.Source.CertifiedTridiagonalEigenpairs.AcceptedOutput.NormalizedExecution
import ComputationalMathematics.Source.CertifiedTridiagonalEigenpairs.IndexedRefinement.Execution
import ComputationalMathematics.Source.CertifiedTridiagonalEigenpairs.Section06.VectorExecutionWork

/-!
# Work and peak storage of the accepted output loop

The meter visits the same rank array and uses the meters of the two numerical
kernels. The numerical loop computes neither the charge lists nor the space
observations.
-/

namespace NumStability.CertifiedTridiagonalEigenpairs

open FloatingPointFormat.UnboundedBinary ScalarWork
open scoped Matrix.Norms.L2Operator

noncomputable section

variable {n p : ℕ} {J : Finset ℕ}

private def outputSetupTrace (N k q : ℕ) : List Step :=
  -- Flag initialization, rank marks, increasing scan and packed rank writes.
  List.replicate N .index ++ List.replicate (9 * k) .index ++
    List.replicate (8 * N) .index ++ List.replicate (3 * k) .index ++
    -- Setup scalars, the dyadic shift, and the output array and return fields.
    List.replicate 14 .index ++ [.arithmetic q, .scaleByPowerOfTwo]

private def outputRankWriteTrace (q p : ℕ) : List Step :=
  -- Loop test, cursor, rank read, label conversion, exact scaling and pair write.
  [.comparison, .index, .index, .conversion q p, .scaleByPowerOfTwo, .index, .index, .index]

/-- Work by phase and the peak number of simultaneously resident scalar words. -/
structure AcceptedOutputUsage where
  setupWork : ℕ
  refinementWork : ℕ
  vectorWork : ℕ
  writeWork : ℕ
  peakWords : ℕ

/-- Sum the costs of the sequential phases. -/
def AcceptedOutputUsage.work (u : AcceptedOutputUsage) : ℕ :=
  u.setupWork + u.refinementWork + u.vectorWork + u.writeWork

/-- The endpoint-only refinement meter at the actual post-accept tolerance. -/
def acceptedRankRefinementMeter (trial : RetryResult n J p) (b : Fin n → TrialWord n J p)
    (j : RequestedTrialRank n J) :=
  measuredTridiagonalRefinement (vectorToleranceExponent (n + 1) J.card p + 1)
    j.val (fun i => trial.trial.val.diagonal[i.val]) b

/-- The cached solve metered at the root selected for this accepted rank. -/
def acceptedRankVectorMeter (trial : RetryResult n J p) (b : Fin n → TrialWord n J p)
    (j : RequestedTrialRank n J) :=
  let label := (acceptedRankRefinementMeter trial b j).1
  let A := trial.readMatrix b
  vectorCachedExecution (workingPrecision (n + 1) J.card p)
    (workingPrecision_ge_two (n + 1) J.card p) (n + 1) (Nat.succ_pos n)
    (vectorInputDiagonal A label.value) (vectorInputEdge A) (acceptedShiftWord n p J).value

/-- The scalar meter returns the loop's actual label, and the metered cached
solve has the same stored imaginary components as the numerical loop. -/
theorem acceptedRankMeters_match (trial : RetryResult n J p) (b : Fin n → TrialWord n J p)
    (j : RequestedTrialRank n J) :
    (acceptedRankRefinementMeter trial b j).1 = runAcceptedRefinement trial.trial b j ∧
    ∀ i : Fin (n + 1),
      ((vectorComputedImaginaryArray (workingPrecision_ge_two (n + 1) J.card p)
        (Nat.succ_pos n) (trial.readMatrix b) (runAcceptedRefinement trial.trial b j).value
        (acceptedShiftWord n p J).value).get i).value =
      ((acceptedRankVectorMeter trial b j).column.get i).im := by
  have h : (acceptedRankRefinementMeter trial b j).1 =
      runAcceptedRefinement trial.trial b j := measuredTridiagonalRefinement_eq_run _ _ _ _
  refine ⟨h, fun i => ?_⟩
  unfold acceptedRankVectorMeter
  dsimp only
  rw [h]
  change ((vectorComputedImaginaryArray _ _ _ _ _)[i.val]).value = _
  rw [vectorComputedImaginaryArray, Vector.getElem_ofFn, vectorImaginaryWords_value]

/-- Allow for both original input bands, the normalized bands, the accepted
diagonal, scan flags and rank buffers, and scalar control state. The band arrays
are referenced by the kernels. Charging their resident words here as well is
a conservative bound. -/
private def acceptedOutputResident (N k : ℕ) : ℕ := 8 * N + 2 * k + 32

/-- Meter the exact increasing rank array consumed by `acceptedOutputLoop`.
Each finished pair leaves one label and one full column resident. Workspace for
refinement and vector computation contributes a maximum because they run in
sequence. The current pair's words are allowed during the output write. -/
def acceptedOutputUsage (trial : RetryResult n J p) (b : Fin n → TrialWord n J p)
    (hJvalid : J ⊆ Finset.Icc 1 (n + 1)) : AcceptedOutputUsage :=
  let N := n + 1
  let k := J.card
  let q := workingPrecision N k p
  let ranks := requestedRankArray J hJvalid
  let scalar := fun i => (acceptedRankRefinementMeter trial b (ranks.get i)).2
  let root := fun i => (acceptedRankVectorMeter trial b (ranks.get i)).root
  let resident := acceptedOutputResident N k
  let live := fun i : Fin k =>
    resident + i.val * (N + 1) +
      max (scalar i).peakWords (storage (vectorExecutionLiveWords (root i)) + 1) + (N + 1)
  ⟨work (outputSetupTrace N k q),
    ∑ i : Fin k, (scalar i).work,
    ∑ i : Fin k, work (vectorExecutionTrace q p (root i)),
    k * work (outputRankWriteTrace q p),
    storage (resident :: (resident + k * (N + 1)) :: (List.finRange k).map live)⟩

/-- Precision of the post-accept meter, using its exact setup, output writes,
and vector schedule. The refinement trace observes the same endpoint loop;
each nested count is also checked using the recorded sweep of that loop. -/
def acceptedOutputRespectsPrecision (trial : RetryResult n J p)
    (b : Fin n → TrialWord n J p) (hJvalid : J ⊆ Finset.Icc 1 (n + 1)) : Prop :=
  let N := n + 1
  let q := workingPrecision N J.card p
  let r := vectorToleranceExponent N J.card p + 1
  let a : Fin N → TrialWord n J p := fun i => trial.trial.val.diagonal[i.val]
  let ranks := requestedRankArray J hJvalid
  TraceAllowed q (outputSetupTrace N J.card q) ∧
  TraceAllowed q (outputRankWriteTrace q p) ∧
  ∀ i : Fin J.card,
    let j := ranks.get i
    TraceAllowed q (tridiagonalRefinement r j.val a b).trace ∧
    (∀ m < r + 4,
      let x := PaddedRefinement.midpoint (runTridiagonalRefinementInterval r j.val a b m)
      TraceAllowed q (recordedClippedSturmExecution q (workingPrecision_ge_two N J.card p)
        r a b x).2.trace) ∧
    TraceAllowed q (vectorExecutionTrace q p (acceptedRankVectorMeter trial b j).root)

theorem acceptedOutput_respectsPrecision (trial : RetryResult n J p)
    (b : Fin n → TrialWord n J p) (hJvalid : J ⊆ Finset.Icc 1 (n + 1))
    (hp : 2 ≤ p) (hn : 2 ≤ n + 1) :
    acceptedOutputRespectsPrecision trial b hJvalid := by
  unfold acceptedOutputRespectsPrecision
  dsimp only
  let q := workingPrecision (n + 1) J.card p
  have hq : 2 ≤ q := workingPrecision_ge_two _ _ _
  have hpq : p ≤ q := by dsimp [q, workingPrecision]; omega
  refine ⟨?_, ?_, fun i => ⟨?_, ?_, ?_⟩⟩
  · intro step hstep
    simp only [outputSetupTrace, List.mem_append, List.mem_replicate, List.mem_cons,
      List.not_mem_nil, or_false] at hstep
    aesop (add simp [Step.Allowed])
  · change TraceAllowed q (outputRankWriteTrace q p)
    simp [outputRankWriteTrace, TraceAllowed, Step.Allowed, hq, hp, hpq]
  · exact (tridiagonalRefinement_resources _ _ _ _).2.1
  · intro m _
    exact (runClippedSturmSweep_resources _ _ _ _ _ _).2.1
  · exact (vectorExecution_resources q p _ hn hq hp hpq).2.1

private theorem refining_exponent_bound {N k p : ℕ} (hn : 2 ≤ N)
    (hkn : k ≤ N) (hguard : precisionGuard N p) :
    vectorToleranceExponent N k p + 1 ≤ 6 * (p + Nat.clog 2 N) := by
  have hp := clog_add_le_of_precisionGuard (by omega : 0 < N) hguard
  have hlog := Nat.clog_mono_right 2 hkn
  unfold vectorToleranceExponent
  omega

private theorem acceptedOutputRank_scalar_bounds
    (a : Fin (n + 1) → TrialWord n J p) (b : Fin n → TrialWord n J p)
    (bits : ℕ → GateBits n J) (trial : RetryResult n J p) (hp : 2 ≤ p)
    (hn : 2 ≤ n + 1) (hguard : precisionGuard (n + 1) p)
    (hJ : J.Nonempty) (hJvalid : J ⊆ Finset.Icc 1 (n + 1))
    (ha : ∀ i, |(a i).value| ≤ 1 / 4) (hb : ∀ i, |(b i).value| ≤ 1 / 4)
    (htrial : retryRun a b bits = some trial) (j : RequestedTrialRank n J) :
    let measured := acceptedRankRefinementMeter trial b j
    measured.2.work ≤ 68 * (n + 1) * (vectorToleranceExponent (n + 1) J.card p + 1) ∧
      measured.2.peakWords ≤ 26 * (n + 1) := by
  have hnorm := (runAcceptedRefinement_facts a b bits trial hp hn hguard hJ hJvalid
    ha hb htrial j).2.1
  have hM : realMatrixOperatorNorm (trial.matrix b) ≤ 3 / 2 :=
    hnorm.le.trans (by norm_num)
  have hprec := vectorToleranceExponent_add_nine_le (k := J.card) hn hguard
  have hr : 2 ≤ vectorToleranceExponent (n + 1) J.card p + 1 := by
    unfold vectorToleranceExponent
    omega
  have h := runIndexedRefinement j.val (fun i => trial.trial.val.diagonal[i.val]) b hr
    (by simpa only [Nat.add_assoc] using hprec) hM (fun i => (hb i).trans (by norm_num))
  exact h.2.2.2.2

/-- Actual post-accept work of §7.4, separated into setup, final refinements,
vectors, and explicit label and pair writes. Peak space includes the retained
outputs and charges for one active rank at a time. -/
theorem acceptedOutputUsage_resources
    (a : Fin (n + 1) → TrialWord n J p) (b : Fin n → TrialWord n J p)
    (bits : ℕ → GateBits n J) (trial : RetryResult n J p) (hp : 2 ≤ p)
    (hn : 2 ≤ n + 1) (hguard : precisionGuard (n + 1) p)
    (hJ : J.Nonempty) (hJvalid : J ⊆ Finset.Icc 1 (n + 1))
    (ha : ∀ i, |(a i).value| ≤ 1 / 4) (hb : ∀ i, |(b i).value| ≤ 1 / 4)
    (htrial : retryRun a b bits = some trial) :
    let N := n + 1
    let k := J.card
    let u := acceptedOutputUsage trial b hJvalid
    u.setupWork = 9 * N + 12 * k + 16 ∧
    u.refinementWork ≤ 408 * N * k * (p + Nat.clog 2 N) ∧
    u.vectorWork ≤ 166 * N * k ∧ u.writeWork = 8 * k ∧
    u.refinementWork + u.vectorWork + u.writeWork ≤ 600 * N * k * (p + Nat.clog 2 N) ∧
    u.work ≤ 1300 * N * k * p ∧
    k * (N + 1) ≤ u.peakWords ∧ u.peakWords ≤ 64 * (N + N * k) := by
  intro N k u
  let q := workingPrecision N k p
  let ranks := requestedRankArray J hJvalid
  have hkn : k ≤ N := by
    have h := Finset.card_le_card hJvalid
    simpa [k, N, Nat.card_Icc] using h
  have hN : 2 ≤ N := hn
  have hk : 1 ≤ k := Finset.card_pos.mpr hJ
  have hpq : p ≤ q := by dsimp [q, workingPrecision]; omega
  have hq := workingPrecision_ge_two N k p
  have hscalar (i : Fin k) :=
    acceptedOutputRank_scalar_bounds a b bits trial hp hn hguard hJ hJvalid ha hb htrial (ranks.get i)
  have hvector (i : Fin k) :=
    vectorExecution_resources q p (acceptedRankVectorMeter trial b (ranks.get i)).root hn hq hp hpq
  have hExp := refining_exponent_bound hn hkn hguard
  have hSetup : u.setupWork = 9 * N + 12 * k + 16 := by
    change work (outputSetupTrace N k q) = _
    simp [work, outputSetupTrace]
    omega
  have hRefine : u.refinementWork ≤ 408 * N * k * (p + Nat.clog 2 N) := by
    change (∑ i : Fin k, (acceptedRankRefinementMeter trial b (ranks.get i)).2.work) ≤ _
    calc
      _ ≤ ∑ _ : Fin k, 68 * N * (6 * (p + Nat.clog 2 N)) :=
        Finset.sum_le_sum fun i _ => (hscalar i).1.trans (Nat.mul_le_mul_left _ hExp)
      _ = _ := by simp; ring
  have hVec : u.vectorWork ≤ 166 * N * k := by
    change (∑ i : Fin k, work (vectorExecutionTrace q p
      (acceptedRankVectorMeter trial b (ranks.get i)).root)) ≤ _
    calc
      _ ≤ ∑ _ : Fin k, 166 * N := Finset.sum_le_sum fun i _ => (hvector i).1
      _ = _ := by simp [mul_comm]
  have hWrite : u.writeWork = 8 * k := by
    change k * work (outputRankWriteTrace q p) = _
    simp [work, outputRankWriteTrace, mul_comm]
  have hs : 1 ≤ p + Nat.clog 2 N := by omega
  have hxN : k ≤ N * k := by
    simpa using Nat.mul_le_mul_right k (show 1 ≤ N by omega)
  have hxS : N * k ≤ N * k * (p + Nat.clog 2 N) := by
    simpa using Nat.mul_le_mul_left (N * k) hs
  have hPost : u.refinementWork + u.vectorWork + u.writeWork ≤
      600 * N * k * (p + Nat.clog 2 N) := by
    have hwrite := Nat.mul_le_mul_left 8 (hxN.trans hxS)
    have hvec := Nat.mul_le_mul_left 166 hxS
    rw [hWrite]
    calc
      _ ≤ 408 * N * k * (p + Nat.clog 2 N) + 166 * (N * k) + 8 * k := by
        exact Nat.add_le_add (Nat.add_le_add hRefine (by simpa [Nat.mul_assoc] using hVec)) le_rfl
      _ = 408 * (N * k * (p + Nat.clog 2 N)) + 166 * (N * k) + 8 * k := by ring
      _ ≤ 600 * (N * k * (p + Nat.clog 2 N)) := by omega
      _ = _ := by ring
  have hLog : Nat.clog 2 N ≤ p := by
    have := clog_add_le_of_precisionGuard (by omega : 0 < N) hguard
    omega
  have hNprod : N ≤ N * k := by
    simpa using Nat.mul_le_mul_left N hk
  have hProd : N * k ≤ N * k * p := by
    simpa using Nat.mul_le_mul_left (N * k) (show 1 ≤ p by omega)
  have hWork : u.work ≤ 1300 * N * k * p := by
    have hPostP : u.refinementWork + u.vectorWork + u.writeWork ≤ 1200 * (N * k * p) :=
      hPost.trans (by calc
        _ ≤ 600 * N * k * (2 * p) := Nat.mul_le_mul_left _ (by omega)
        _ = _ := by ring)
    unfold AcceptedOutputUsage.work
    rw [hSetup]
    calc
      _ = (9 * N + 12 * k + 16) + (u.refinementWork + u.vectorWork + u.writeWork) := by ring
      _ ≤ 1300 * (N * k * p) := by omega
      _ = _ := by ring
  have hExplicit : k * (N + 1) ≤ u.peakWords := by
    change _ ≤ max (acceptedOutputResident N k) (max (acceptedOutputResident N k + k * (N + 1)) _)
    exact (Nat.le_add_left _ _).trans ((le_max_left _ _).trans (le_max_right _ _))
  refine ⟨hSetup, hRefine, hVec, hWrite, hPost, hWork, hExplicit, ?_⟩
  have hkout : k * (N + 1) = N * k + k := by ring
  change storage (_ :: _ :: _) ≤ _
  rw [storage_le_iff]
  intro words hwords
  simp only [List.mem_cons, List.mem_map] at hwords
  rcases hwords with rfl | rfl | ⟨i, _, rfl⟩
  · unfold acceptedOutputResident
    omega
  · change acceptedOutputResident N k + k * (N + 1) ≤ _
    rw [hkout]
    unfold acceptedOutputResident
    omega
  · have hScratch : max (acceptedRankRefinementMeter trial b (ranks.get i)).2.peakWords
        (storage (vectorExecutionLiveWords (acceptedRankVectorMeter trial b (ranks.get i)).root) + 1)
        ≤ 31 * N + 1 :=
      max_le ((hscalar i).2.trans (by omega)) (Nat.add_le_add_right (hvector i).2.2 1)
    have hPrefix : i.val * (N + 1) + (N + 1) ≤ k * (N + 1) := by
      rw [← Nat.succ_mul]
      exact Nat.mul_le_mul_right _ i.isLt
    change acceptedOutputResident N k + i.val * (N + 1) +
      max (acceptedRankRefinementMeter trial b (ranks.get i)).2.peakWords
        (storage (vectorExecutionLiveWords (acceptedRankVectorMeter trial b (ranks.get i)).root) + 1)
      + (N + 1) ≤ _
    unfold acceptedOutputResident
    omega

/-- The post-accept meter for a returned native run, using its retained scale,
trial identity and normalized subdiagonal. -/
def normalizedAcceptedOutputUsage {hp : 2 ≤ p}
    (b : Fin n → Word p hp) (hJvalid : J ⊆ Finset.Icc 1 (n + 1))
    (out : NativeAcceptedEigenpairs n p J hp) : AcceptedOutputUsage :=
  acceptedOutputUsage out.accepted (fun i => normalizeTrialWord out.scaleExponent (b i)) hJvalid

/-- The actual normalized eigensolver's post-accept work and peak scalar-word
space have absolute bounds, including its explicit returned columns and labels. -/
theorem normalizedEigenpairRun_resources {hp : 2 ≤ p}
    (a : Fin (n + 1) → Word p hp) (b : Fin n → Word p hp)
    (bits : ℕ → GateBits n J) (hn : 2 ≤ n + 1) (hguard : precisionGuard (n + 1) p)
    (hJ : J.Nonempty) (hJvalid : J ⊆ Finset.Icc 1 (n + 1))
    (out : NativeAcceptedEigenpairs n p J hp)
    (h : normalizedEigenpairRun a b bits hn hguard hJ hJvalid = some out) :
    let u := normalizedAcceptedOutputUsage b hJvalid out
    u.work ≤ 1300 * (n + 1) * J.card * p ∧
    J.card * (n + 2) ≤ u.peakWords ∧ u.peakWords ≤ 64 * ((n + 1) + (n + 1) * J.card) := by
  have hRetry := normalizedEigenpairRun_acceptance a b bits hn hguard hJ hJvalid
  rw [h, Option.map_some] at hRetry
  obtain ⟨hr, htrial⟩ := normalizedRetryRun_some hRetry.symm
  obtain ⟨ha, hb⟩ := normalizedTrialInput_bounds (J := J) a b hr
  exact (acceptedOutputUsage_resources _ _ bits out.accepted hp hn hguard hJ hJvalid
    ha hb htrial).2.2.2.2.2

end

end NumStability.CertifiedTridiagonalEigenpairs
