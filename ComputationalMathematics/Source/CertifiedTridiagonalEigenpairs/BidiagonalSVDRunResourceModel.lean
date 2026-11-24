import ComputationalMathematics.Source.CertifiedTridiagonalEigenpairs.AcceptedOutput.WholeRunStorage
import ComputationalMathematics.Source.CertifiedTridiagonalEigenpairs.AcceptedOutput.WholeRunWork
import ComputationalMathematics.Source.CertifiedTridiagonalEigenpairs.BidiagonalSVDPhaseResources
import ComputationalMathematics.Source.CertifiedTridiagonalEigenpairs.BidiagonalSVDRun

/-! Work and peak scalar words on the selected SVD execution. -/

open MeasureTheory
open scoped ENNReal

namespace NumStability.CertifiedTridiagonalEigenpairs.BidiagonalSVDRequest

open FloatingPointFormat.UnboundedBinary ScalarWork

noncomputable section

variable {n k p : ℕ} {hp : 2 ≤ p}
variable {upper : Bool} {a : Fin (n + 1) → Word p hp} {b : Fin n → Word p hp}
  {I : Fin k ↪o Fin (n + 1)}
  {cmp : EmptyBinScan.Comparison (svdLabelPrecision k p) (svdLabelPrecision_ge_two k p)}
  {hk : 1 ≤ k} {hguard : precisionGuard (n + 1) p}

/-- Upper charge for the shared exact-dispatch scan. The scan inspects the
stored bands and has no real arithmetic besides stored-word comparisons. -/
def dispatchTrace (d : ℕ) : List Step :=
  (List.replicate (2 * d - 1)
    [.index, .comparison, .comparison, .readExponent, .readExponent, .comparison,
      .comparison, .comparison, .index]).flatten ++
  [.comparison, .comparison, .index, .index, .index, .index, .index, .index]

/-- Exact dispatch copies the requested coordinate columns and their labels. -/
def exactWriteTrace (d k : ℕ) : List Step :=
  (List.replicate (2 * (d * k)) [.index, .comparison, .index, .index]).flatten ++
    (List.replicate k [.index, .index, .index]).flatten

/-- The exact path keeps the input, request, and the two materialized
coordinate families and labels. -/
def exactPeakWords (d k : ℕ) : ℕ := 24 * d + 2 * (d * k) + 2 * k + 8

/-- The deterministic phases surrounding the one oracle call, using the
flags and native rank plan taken from the prepared cache. -/
def TridiagonalCall.outerWork (call : TridiagonalCall n k p) (upper : Bool)
    (a : Fin (n + 1) → Word p hp) (b : Fin n → Word p hp) (I : Fin k ↪o Fin (n + 1))
    (cmp : EmptyBinScan.Comparison (svdLabelPrecision k p) (svdLabelPrecision_ge_two k p)) : ℕ :=
  let flags := assembleLowFlags cmp call.preprocessing call.labelCount
  ScalarWork.work (dispatchTrace (n + 1)) +
    ScalarWork.work (call.preparationTrace upper a b I) +
    ScalarWork.work (lowFlagsTrace k) +
    ScalarWork.work (call.nativeRankPlanTrace flags) +
    ScalarWork.work (finishTrace (n + 1) k p)

/-- Use the oracle work meter for exactly the packed call that runs on this
stream. On a never-accepting stream the charge is infinite, so the finite
schedule for postprocessing does not change its cost. -/
def RunPlan.work : (plan : RunPlan upper a b I cmp hk hguard) → plan.Bits → ℝ≥0∞
  | .exact .. => fun _ =>
      (ScalarWork.work (dispatchTrace (n + 1)) + ScalarWork.work (exactWriteTrace (n + 1) k) : ℕ)
  | .nontrivial _ call .. => fun bits =>
      (call.outerWork upper a b I cmp : ℝ≥0∞) +
        normalizedEigenpairWork call.diagonal.get call.edges.get call.oneBasedRanks_subset bits

/-- Resident preparation and rank words remain charged while the oracle uses
its retry/accepted-output workspace. The oracle retains its returned pairs
while the native finish writes both parity families. Addition permits all these
regions to be live simultaneously and bounds the peak of the actual run. -/
def RunPlan.workspaceBound : (plan : RunPlan upper a b I cmp hk hguard) → plan.Bits → ℕ
  | .exact .. => fun _ => exactPeakWords (n + 1) k
  | .nontrivial _ call .. => fun bits =>
      let flags := assembleLowFlags cmp call.preprocessing call.labelCount
      let legal := call.admissible hk hguard
      storage (call.preparationLiveWords upper a b I) + k +
        storage (call.nativeRankPlanLiveWords flags) +
        normalizedEigenpairWorkspace call.diagonal.get call.edges.get bits
          legal.1 legal.2.2.2.2.2.1 legal.2.1 call.oneBasedRanks_subset +
        (if (call.solve hk hguard bits).isSome then storage (finishLiveWords (n + 1) k) else 0)

/-- The complete precision cap uses only the input precision on exact branches. -/
def RunPlan.precision (plan : RunPlan upper a b I cmp hk hguard) : ℕ :=
  match plan with
  | .exact .. => p
  | .nontrivial .. => svdWorkingPrecision (n + 1) k p

/-- The number of attempted perturbations, including the accepted one, is
zero on the exact branches and infinite on a never-accepting stream. -/
def RunPlan.attemptCount : (plan : RunPlan upper a b I cmp hk hguard) → plan.Bits → ℝ≥0∞
  | .exact .. => fun _ => 0
  | .nontrivial _ call .. => fun bits =>
      normalizedEigenpairAttemptCount call.diagonal.get call.edges.get bits


/-- Deterministic phase traces and every auxiliary trial prefix fit the same
precision as the actual branch. The working precision of the packed auxiliary
solver also bounds its post-accept operations. -/
def RunPlan.RespectsPrecision (plan : RunPlan upper a b I cmp hk hguard) : Prop :=
  match plan with
  | .exact .. => TraceAllowed plan.precision (dispatchTrace (n + 1) ++ exactWriteTrace (n + 1) k)
  | .nontrivial _ call .. =>
    let flags := assembleLowFlags cmp call.preprocessing call.labelCount
    TraceAllowed plan.precision (dispatchTrace (n + 1)) ∧
    TraceAllowed plan.precision (call.preparationTrace upper a b I) ∧
    TraceAllowed plan.precision (lowFlagsTrace k) ∧
    TraceAllowed plan.precision (call.nativeRankPlanTrace flags) ∧
    TraceAllowed plan.precision (finishTrace (n + 1) k p) ∧
    workingPrecision (edgeCount n + 1) call.oneBasedRanks.card
      (svdAuxiliaryPrecision k p) ≤ plan.precision ∧
    ∀ (e : ℤ) (_ : normalizationExponent call.diagonal.get call.edges.get = some e)
      (bits : ℕ → GateBits (edgeCount n) call.oneBasedRanks) (m : ℕ),
      TraceAllowed plan.precision (trialTracePrefix
        (fun i => normalizeTrialWord e (call.diagonal.get i))
        (fun i => normalizeTrialWord e (call.edges.get i)) bits m)

end

end NumStability.CertifiedTridiagonalEigenpairs.BidiagonalSVDRequest
