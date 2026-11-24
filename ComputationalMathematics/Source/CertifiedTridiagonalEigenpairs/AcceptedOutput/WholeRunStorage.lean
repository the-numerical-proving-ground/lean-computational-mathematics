import ComputationalMathematics.Source.CertifiedTridiagonalEigenpairs.AcceptedOutput.Resources
import ComputationalMathematics.Source.CertifiedTridiagonalEigenpairs.Retry.PrefixExecution
import ComputationalMathematics.Source.CertifiedTridiagonalEigenpairs.ExactBranchExecution

/-! Peak scalar words for normalization, all retry prefixes and accepted output. -/

namespace NumStability.CertifiedTridiagonalEigenpairs

open FloatingPointFormat.UnboundedBinary ScalarWork

variable {n p : ℕ} {J : Finset ℕ} {hp : 2 ≤ p}

/-- Measure the packed scale scan with the requested ranks still resident.
Once that scan has released its scratch, the original and normalized bands,
ranks, and fixed control slots remain during the band writes. -/
def normalizationWorkspace (a : Fin (n + 1) → Word p hp) (b : Fin n → Word p hp)
    (k : ℕ) : ℕ :=
  let scan := runNormalizationScan a b
  let fill := if scan.exponent.isSome then 4 * (n + 1) + k + 8 else 0
  max (storage scan.liveWords + k) fill

theorem normalizationWorkspace_le (a : Fin (n + 1) → Word p hp) (b : Fin n → Word p hp)
    (k : ℕ) (hkn : k ≤ n + 1) : normalizationWorkspace a b k ≤ 25 * (n + 1) := by
  have hscan := (runNormalizationScan_resources a b).2.2
  unfold normalizationWorkspace
  apply max_le
  · omega
  · split <;> omega

/-- Peak up through normalization and the first `m` trial opportunities.
The finite retry loop stops measuring trials once it has accepted. -/
noncomputable def normalizedEigenpairPrefixWorkspace
    (a : Fin (n + 1) → Word p hp) (b : Fin n → Word p hp)
    (bits : ℕ → GateBits n J) (m : ℕ) : ℕ :=
  max (normalizationWorkspace a b J.card) <|
    match normalizationExponent a b with
    | none => 0
    | some r =>
      let diagonal : Vector (TrialWord n J p) (n + 1) :=
        Vector.ofFn fun i => normalizeTrialWord r (a i)
      let subdiagonal : Vector (TrialWord n J p) n :=
        Vector.ofFn fun i => normalizeTrialWord r (b i)
      (measuredRetryPrefix (fun i => diagonal[i.val]) (fun i => subdiagonal[i.val]) bits m).2

theorem normalizedEigenpairPrefixWorkspace_le
    (a : Fin (n + 1) → Word p hp) (b : Fin n → Word p hp)
    (bits : ℕ → GateBits n J) (m : ℕ) (hJvalid : J ⊆ Finset.Icc 1 (n + 1)) :
    normalizedEigenpairPrefixWorkspace a b bits m ≤ 55 * (n + 1) := by
  have hkn : J.card ≤ n + 1 := by
    simpa [Nat.card_Icc] using Finset.card_le_card hJvalid
  unfold normalizedEigenpairPrefixWorkspace
  apply max_le
  · exact (normalizationWorkspace_le a b J.card hkn).trans (by omega)
  · split
    · omega
    · exact measuredRetryPrefix_workspace _ _ bits m hkn

/-- At a successful normalized run's actual attempt count, the bounded
sequential loop returns the accepted diagonal used by the output loop. -/
theorem normalizedEigenpairRun_prefix_returns
    (a : Fin (n + 1) → Word p hp) (b : Fin n → Word p hp)
    (bits : ℕ → GateBits n J) (hn : 2 ≤ n + 1) (hguard : precisionGuard (n + 1) p)
    (hJ : J.Nonempty) (hJvalid : J ⊆ Finset.Icc 1 (n + 1))
    (out : NativeAcceptedEigenpairs n p J hp)
    (hrun : normalizedEigenpairRun a b bits hn hguard hJ hJvalid = some out) :
    (measuredRetryPrefix (fun i => normalizeTrialWord out.scaleExponent (a i))
      (fun i => normalizeTrialWord out.scaleExponent (b i)) bits (out.accepted.index + 1)).1 =
        some out.accepted := by
  have hr := normalizedEigenpairRun_acceptance a b bits hn hguard hJ hJvalid
  rw [hrun, Option.map_some] at hr
  obtain ⟨_, ht⟩ := normalizedRetryRun_some hr.symm
  rw [measuredRetryPrefix_run, retryRunPrefix_eq_filter, ht]
  simp

/-- Complete normalized run workspace. The supremum includes every attempted
prefix even for an indefinitely rejecting stream. The output phase is entered
only when that same normalized run returns. -/
noncomputable def normalizedEigenpairWorkspace
    (a : Fin (n + 1) → Word p hp) (b : Fin n → Word p hp)
    (bits : ℕ → GateBits n J) (hn : 2 ≤ n + 1) (hguard : precisionGuard (n + 1) p)
    (hJ : J.Nonempty) (hJvalid : J ⊆ Finset.Icc 1 (n + 1)) : ℕ :=
  max (sSup (Set.range (normalizedEigenpairPrefixWorkspace a b bits))) <|
    match normalizedEigenpairRun a b bits hn hguard hJ hJvalid with
    | none => 0
    | some out => (normalizedAcceptedOutputUsage b hJvalid out).peakWords

theorem normalizedEigenpairPrefixWorkspace_le_workspace
    (a : Fin (n + 1) → Word p hp) (b : Fin n → Word p hp)
    (bits : ℕ → GateBits n J) (hn : 2 ≤ n + 1) (hguard : precisionGuard (n + 1) p)
    (hJ : J.Nonempty) (hJvalid : J ⊆ Finset.Icc 1 (n + 1)) (m : ℕ) :
    normalizedEigenpairPrefixWorkspace a b bits m ≤
      normalizedEigenpairWorkspace a b bits hn hguard hJ hJvalid := by
  have hbounded : BddAbove (Set.range (normalizedEigenpairPrefixWorkspace a b bits)) :=
    ⟨55 * (n + 1), by
      rintro _ ⟨j, rfl⟩
      exact normalizedEigenpairPrefixWorkspace_le a b bits j hJvalid⟩
  exact (le_csSup hbounded ⟨m, rfl⟩).trans (le_max_left _ _)

/-- For a returning run, the complete peak is the peak up to its actual
first-accept count, combined with that run's output phase. -/
theorem normalizedEigenpairWorkspace_eq_of_return
    (a : Fin (n + 1) → Word p hp) (b : Fin n → Word p hp)
    (bits : ℕ → GateBits n J) (hn : 2 ≤ n + 1) (hguard : precisionGuard (n + 1) p)
    (hJ : J.Nonempty) (hJvalid : J ⊆ Finset.Icc 1 (n + 1))
    (out : NativeAcceptedEigenpairs n p J hp)
    (hrun : normalizedEigenpairRun a b bits hn hguard hJ hJvalid = some out) :
    normalizedEigenpairWorkspace a b bits hn hguard hJ hJvalid =
      max (normalizedEigenpairPrefixWorkspace a b bits (out.accepted.index + 1))
          (normalizedAcceptedOutputUsage b hJvalid out).peakWords := by
  let m := out.accepted.index + 1
  have hr := normalizedEigenpairRun_acceptance a b bits hn hguard hJ hJvalid
  rw [hrun, Option.map_some] at hr
  have hscale := (normalizedRetryRun_some hr.symm).1
  have hreturn := normalizedEigenpairRun_prefix_returns a b bits hn hguard hJ hJvalid out hrun
  let P := normalizedEigenpairPrefixWorkspace a b bits
  have hP (j : ℕ) : P j ≤ P m := by
    unfold P normalizedEigenpairPrefixWorkspace
    rw [hscale]
    simp only [Vector.getElem_ofFn]
    rcases le_or_gt j m with hj | hj
    · exact max_le_max le_rfl (measuredRetryPrefix_peak_monotone _ _ bits hj)
    · have hstable := measuredRetryPrefix_stable _ _ bits m (j - m) out.accepted hreturn
      have hindex : m + (j - m) = j := by omega
      rw [hindex] at hstable
      rw [hstable]
  have hrange : BddAbove (Set.range P) :=
    ⟨P m, by rintro _ ⟨j, rfl⟩; exact hP j⟩
  have hsup : sSup (Set.range P) = P m :=
    le_antisymm (csSup_le (Set.range_nonempty _) (by rintro _ ⟨j, rfl⟩; exact hP j))
      (le_csSup hrange ⟨m, rfl⟩)
  unfold normalizedEigenpairWorkspace
  rw [hrun, show sSup (Set.range (normalizedEigenpairPrefixWorkspace a b bits)) = P m from hsup]

/-- Peak storage includes the native output as well as all active phases. -/
theorem normalizedEigenpairWorkspace_le
    (a : Fin (n + 1) → Word p hp) (b : Fin n → Word p hp)
    (bits : ℕ → GateBits n J) (hn : 2 ≤ n + 1) (hguard : precisionGuard (n + 1) p)
    (hJ : J.Nonempty) (hJvalid : J ⊆ Finset.Icc 1 (n + 1)) :
    normalizedEigenpairWorkspace a b bits hn hguard hJ hJvalid ≤
      64 * ((n + 1) + (n + 1) * J.card) := by
  unfold normalizedEigenpairWorkspace
  apply max_le
  · apply csSup_le (Set.range_nonempty _)
    rintro _ ⟨m, rfl⟩
    exact (normalizedEigenpairPrefixWorkspace_le a b bits m hJvalid).trans (by omega)
  · split
    · omega
    · rename_i out hout
      exact (normalizedEigenpairRun_resources a b bits hn hguard hJ hJvalid out hout).2.2

theorem normalizedEigenpairWorkspace_output_le
    (a : Fin (n + 1) → Word p hp) (b : Fin n → Word p hp)
    (bits : ℕ → GateBits n J) (hn : 2 ≤ n + 1) (hguard : precisionGuard (n + 1) p)
    (hJ : J.Nonempty) (hJvalid : J ⊆ Finset.Icc 1 (n + 1))
    (out : NativeAcceptedEigenpairs n p J hp)
    (hrun : normalizedEigenpairRun a b bits hn hguard hJ hJvalid = some out) :
    J.card * (n + 2) ≤ normalizedEigenpairWorkspace a b bits hn hguard hJ hJvalid := by
  have hlower := (normalizedEigenpairRun_resources a b bits hn hguard hJ hJvalid out hrun).2.1
  unfold normalizedEigenpairWorkspace
  rw [hrun]
  exact hlower.trans (le_max_right _ _)

end NumStability.CertifiedTridiagonalEigenpairs
