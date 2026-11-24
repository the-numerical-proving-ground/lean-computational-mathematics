import ComputationalMathematics.Source.CertifiedTridiagonalEigenpairs.BidiagonalSVDExactBranches
import ComputationalMathematics.Source.CertifiedTridiagonalEigenpairs.BidiagonalSVDOracleOutput
import ComputationalMathematics.Source.CertifiedTridiagonalEigenpairs.BidiagonalSVDNativeRanks

/-!
# Execute the selected bidiagonal SVD

The exact dispatch returns before requesting any bits. For a nonzero matrix of
order at least two, deterministic preprocessing fixes the one tridiagonal
request whose fair-bit stream drives the retries.
-/

namespace NumStability.CertifiedTridiagonalEigenpairs.BidiagonalSVDRequest

open FloatingPointFormat.UnboundedBinary MeasureTheory

variable {n k p : ℕ} {hp : 2 ≤ p}

/-- Both branches produce the same native triplet type and retain their trial count. -/
structure RunOutput (n k p : ℕ) (hp : 2 ≤ p) where
  triplets : NativeSVDTriplets (n + 1) k p hp
  trials : ℕ

/-- View the existing exact branch in the common native output format. -/
def exactOutput (out : BidiagonalExactOutput p hp n k) : RunOutput n k p hp :=
  ⟨⟨fun j i => out.left i j, fun j i => out.right i j, out.labels⟩, out.trials⟩

/-- Materialize both families and the labels even on the zero and scalar branches. -/
def exactPackedOutput (out : BidiagonalExactOutput p hp n k) : RunOutput n k p hp :=
  let labels := Vector.ofFn out.labels
  let left := Vector.ofFn fun j : Fin k => Vector.ofFn fun i : Fin (n + 1) => out.left i j
  let right := Vector.ofFn fun j : Fin k => Vector.ofFn fun i : Fin (n + 1) => out.right i j
  ⟨⟨fun j i => (left.get j).get i, fun j i => (right.get j).get i, labels.get⟩, out.trials⟩

@[simp] theorem exactPackedOutput_eq (out : BidiagonalExactOutput p hp n k) :
    exactPackedOutput out = exactOutput out := by
  have hget {m : ℕ} {β : Type} (f : Fin m → β) (i : Fin m) :
      (Vector.ofFn f).get i = f i := Vector.getElem_ofFn i.isLt
  have hfn {m : ℕ} {β : Type} (f : Fin m → β) : (Vector.ofFn f).get = f := funext (hget f)
  simp only [exactPackedOutput, exactOutput, hfn]

/-- The deterministic dispatch determines the subsequent bit-stream type. -/
inductive RunPlan (upper : Bool) (a : Fin (n + 1) → Word p hp) (b : Fin n → Word p hp)
    (I : Fin k ↪o Fin (n + 1))
    (cmp : EmptyBinScan.Comparison (svdLabelPrecision k p) (svdLabelPrecision_ge_two k p))
    (hk : 1 ≤ k) (hguard : precisionGuard (n + 1) p) where
  | exact (out : BidiagonalExactOutput p hp n k) (he : bidiagonalExactBranch a b I = some out)
  | nontrivial (hn : 2 ≤ n + 1) (call : TridiagonalCall n k p)
      (hprep : prepareTridiagonalCall upper a b I cmp hn hk hguard I.strictMono = some call)
      (hscale : ∃ r, normalizationExponent a b = some r)

variable {upper : Bool} {a : Fin (n + 1) → Word p hp} {b : Fin n → Word p hp}
  {I : Fin k ↪o Fin (n + 1)}
  {cmp : EmptyBinScan.Comparison (svdLabelPrecision k p) (svdLabelPrecision_ge_two k p)}
  {hk : 1 ≤ k} {hguard : precisionGuard (n + 1) p}

private theorem nontrivial_of_exact_none (he : bidiagonalExactBranch a b I = none) :
    storedBidiagonal upper a b ≠ 0 ∧ 2 ≤ n + 1 := by
  have h := (bidiagonalExactBranch_isSome_iff upper a b I).not
  have h' : ¬ (storedBidiagonal upper a b = 0 ∨ n = 0) := by simpa [he] using h
  exact ⟨fun hz => h' (.inl hz), by by_contra! hn; exact h' (.inr (by omega))⟩

/-- Check the exact branches, then prepare the one tridiagonal call. -/
noncomputable def prepareRun (upper : Bool) (a : Fin (n + 1) → Word p hp)
    (b : Fin n → Word p hp) (I : Fin k ↪o Fin (n + 1))
    (cmp : EmptyBinScan.Comparison (svdLabelPrecision k p) (svdLabelPrecision_ge_two k p))
    (hk : 1 ≤ k) (hguard : precisionGuard (n + 1) p) :
    RunPlan upper a b I cmp hk hguard :=
  match he : bidiagonalExactBranch a b I with
  | some out => .exact out he
  | none =>
    let h := nontrivial_of_exact_none (upper := upper) he
    let hscale := (bidiagonal_normalizationExponent_exists upper a b).mpr h.1
    match hprep : prepareTridiagonalCall upper a b I cmp h.2 hk hguard I.strictMono with
    | some call => .nontrivial h.2 call hprep hscale
    | none => False.elim (by
        obtain ⟨r, hr⟩ := hscale
        obtain ⟨call, hc, _⟩ :=
          prepareTridiagonalCall_spec upper a b I cmp h.2 hk hguard I.strictMono hr
        rw [hprep] at hc
        contradiction)

/-- An exact branch draws no random bits. The other branch uses the bit words
of its actual packed request, in the order of successive trials. -/
def RunPlan.Bits : RunPlan upper a b I cmp hk hguard → Type
  | .exact .. => Unit
  | .nontrivial _ call .. => ℕ → GateBits (edgeCount n) call.oneBasedRanks

instance (plan : RunPlan upper a b I cmp hk hguard) : MeasurableSpace plan.Bits := by
  cases plan
  · change MeasurableSpace Unit
    infer_instance
  · change MeasurableSpace (ℕ → GateBits (edgeCount n) _)
    infer_instance

/-- Fair bits on the packed request, or the point mass on the exact branch. -/
noncomputable def RunPlan.bitMeasure (plan : RunPlan upper a b I cmp hk hguard) :
    Measure plan.Bits :=
  match plan with
  | .exact .. => Measure.dirac ()
  | .nontrivial _ call .. => retryBitMeasure (edgeCount n) call.oneBasedRanks

/-- Successful actual oracle returns have nonzero columns for final normalization. -/
theorem TridiagonalCall.returnedParities_nonzero (hn : 2 ≤ n + 1) (call : TridiagonalCall n k p)
    (hprep : prepareTridiagonalCall upper a b I cmp hn hk hguard I.strictMono = some call)
    (hscale : ∃ r, normalizationExponent a b = some r)
    (bits : ℕ → GateBits (edgeCount n) call.oneBasedRanks) (out : call.NativeParities)
    (hrun : call.solveParities upper hk hguard bits = some out) :
    (∀ j, Word.euclidean (out.left.get j).get ≠ 0) ∧
    (∀ j, Word.euclidean (out.right.get j).get ≠ 0) := by
  obtain ⟨r, hr⟩ := hscale
  obtain ⟨hL, hR, _⟩ :=
    TridiagonalCall.prepared_solve_finish_accuracy hp upper a b I cmp hn hk hguard
      I.strictMono hr call hprep bits out hrun
  exact ⟨hL, hR⟩

private theorem preparedSlots_strictMono (hn : 2 ≤ n + 1) (call : TridiagonalCall n k p)
    (hprep : prepareTridiagonalCall upper a b I cmp hn hk hguard I.strictMono = some call) :
    StrictMono call.slots := by
  simp only [prepareTridiagonalCall] at hprep
  obtain ⟨_, _, _, rfl⟩ := Option.pmap_eq_some_iff.mp hprep
  exact I.strictMono

/-- Compute the native flags from the stored cache and use the native slot
tables to extract the single call's two parity arrays. -/
noncomputable def TridiagonalCall.solvePreparedParities (hn : 2 ≤ n + 1)
    (call : TridiagonalCall n k p)
    (hprep : prepareTridiagonalCall upper a b I cmp hn hk hguard I.strictMono = some call)
    (bits : ℕ → GateBits (edgeCount n) call.oneBasedRanks) : Option call.NativeParities :=
  let flags := assembleLowFlags cmp call.preprocessing call.labelCount
  let hf := prepareLowFlags_spec upper a b I cmp hn hk hguard I.strictMono call hprep
  call.solveParitiesWithRankPlan upper flags hf (preparedSlots_strictMono hn call hprep)
    hk hguard bits

theorem TridiagonalCall.solvePreparedParities_eq (hn : 2 ≤ n + 1)
    (call : TridiagonalCall n k p)
    (hprep : prepareTridiagonalCall upper a b I cmp hn hk hguard I.strictMono = some call)
    (bits : ℕ → GateBits (edgeCount n) call.oneBasedRanks) :
    call.solvePreparedParities hn hprep bits = call.solveParities upper hk hguard bits :=
  call.solveParitiesWithRankPlan_eq upper _ _ _ hk hguard bits

/-- Normalize each packed column with a shared rounded denominator and
materialize the two output arrays and all final labels. -/
noncomputable def TridiagonalCall.finishPacked (call : TridiagonalCall n k p)
    (out : call.NativeParities) (hL : ∀ j, Word.euclidean (out.left.get j).get ≠ 0)
    (hR : ∀ j, Word.euclidean (out.right.get j).get ≠ 0) : NativeSVDTriplets (n + 1) k p hp :=
  let left := Vector.ofFn fun j => Word.normalizeToScan p hp (out.left.get j) (hL j)
  let right := Vector.ofFn fun j => Word.normalizeToScan p hp (out.right.get j) (hR j)
  let labels := Vector.ofFn fun j =>
    (Word.round p hp (call.label j)).scale call.preprocessing.scaleExponent
  ⟨fun j i => (left.get j).get i, fun j i => (right.get j).get i, labels.get⟩

@[simp] theorem TridiagonalCall.finishPacked_eq (call : TridiagonalCall n k p)
    (out : call.NativeParities) (hL : ∀ j, Word.euclidean (out.left.get j).get ≠ 0)
    (hR : ∀ j, Word.euclidean (out.right.get j).get ≠ 0) :
    call.finishPacked (hp := hp) out hL hR = call.finish out hL hR := by
  have hget {m : ℕ} {β : Type} (f : Fin m → β) (i : Fin m) :
      (Vector.ofFn f).get i = f i := Vector.getElem_ofFn i.isLt
  have hfn {m : ℕ} {β : Type} (f : Fin m → β) : (Vector.ofFn f).get = f := funext (hget f)
  simp only [finishPacked, finish, finishNative, hfn, Word.normalizeToScan_get]

/-- Return exact triplets, or finish the successful return of the one packed call.
A stream that never accepts yields `none`. -/
noncomputable def RunPlan.run :
    (plan : RunPlan upper a b I cmp hk hguard) → plan.Bits → Option (RunOutput n k p hp)
  | .exact out _ => fun _ => some (exactPackedOutput out)
  | .nontrivial hn call hprep hscale => fun bits =>
    match hrun : call.solvePreparedParities hn hprep bits with
    | none => none
    | some out =>
      let hrun' := (call.solvePreparedParities_eq hn hprep bits).symm.trans hrun
      let nz := call.returnedParities_nonzero hn hprep hscale bits out hrun'
      some ⟨call.finishPacked out nz.1 nz.2, out.oracle.accepted.index + 1⟩

/-- The top-level nontrivial branch retains the same finalized words and count
as the successful solve on its own packed request. -/
theorem RunPlan.nontrivial_run_eq_some (hn : 2 ≤ n + 1) (call : TridiagonalCall n k p)
    (hprep : prepareTridiagonalCall upper a b I cmp hn hk hguard I.strictMono = some call)
    (hscale : ∃ r, normalizationExponent a b = some r)
    (bits : ℕ → GateBits (edgeCount n) call.oneBasedRanks) (out : call.NativeParities)
    (hrun : call.solveParities upper hk hguard bits = some out)
    (hL : ∀ j, Word.euclidean (out.left.get j).get ≠ 0)
    (hR : ∀ j, Word.euclidean (out.right.get j).get ≠ 0) :
    (RunPlan.nontrivial hn call hprep hscale).run bits =
      some ⟨call.finish out hL hR, out.oracle.accepted.index + 1⟩ := by
  simp only [RunPlan.run]
  split
  · rename_i hnone
    rw [call.solvePreparedParities_eq, hrun] at hnone
    contradiction
  · rename_i solved hs
    rw [call.solvePreparedParities_eq, hrun] at hs
    cases Option.some.inj hs
    rw [TridiagonalCall.finishPacked_eq]

theorem RunPlan.nontrivial_run_eq_none (hn : 2 ≤ n + 1) (call : TridiagonalCall n k p)
    (hprep : prepareTridiagonalCall upper a b I cmp hn hk hguard I.strictMono = some call)
    (hscale : ∃ r, normalizationExponent a b = some r)
    (bits : ℕ → GateBits (edgeCount n) call.oneBasedRanks) :
    (RunPlan.nontrivial hn call hprep hscale).run bits = none ↔ call.solve hk hguard bits = none := by
  simp only [RunPlan.run]
  split
  · rename_i hnone
    rw [call.solvePreparedParities_eq, TridiagonalCall.solveParities] at hnone
    exact ⟨fun _ => Option.map_eq_none_iff.mp hnone, fun _ => rfl⟩
  · rename_i out hout
    rw [call.solvePreparedParities_eq, TridiagonalCall.solveParities] at hout
    exact ⟨fun h => by contradiction, fun h => by simp [h] at hout⟩

/-- The exact branches return immediately and the nontrivial branch returns
almost surely under the fair-bit law of the single prepared request. -/
theorem RunPlan.ae_returns (plan : RunPlan upper a b I cmp hk hguard) :
    ∀ᵐ bits ∂plan.bitMeasure, ∃ out, plan.run bits = some out := by
  cases plan with
  | exact out he =>
    exact ae_of_all _ (fun _ => ⟨exactPackedOutput out, rfl⟩)
  | nontrivial hn call hprep hscale =>
    have hnonzero := prepareTridiagonalCall_nonzero upper a b I cmp hn hk hguard I.strictMono hprep
    change ∀ᵐ bits ∂retryBitMeasure (edgeCount n) call.oneBasedRanks, _
    filter_upwards [call.ae_solve_returns hk hguard hnonzero] with bits hbits
    obtain ⟨out, hout⟩ := hbits
    have hp : call.solveParities upper hk hguard bits = some (call.extractParities upper out) := by
      simp only [TridiagonalCall.solveParities, hout, Option.map_some]
    obtain ⟨hL, hR⟩ := call.returnedParities_nonzero hn hprep hscale bits _ hp
    exact ⟨_, nontrivial_run_eq_some hn call hprep hscale bits _ hp hL hR⟩

end NumStability.CertifiedTridiagonalEigenpairs.BidiagonalSVDRequest
