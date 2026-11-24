import ComputationalMathematics.Source.CertifiedTridiagonalEigenpairs.AcceptedOutput.Execution

/-! End-to-end execution of the normalized, nontrivial branch. -/

namespace NumStability.CertifiedTridiagonalEigenpairs

open FloatingPointFormat.UnboundedBinary

noncomputable section

variable {n p : ℕ} {J : Finset ℕ} {hp : 2 ≤ p}

/-- Compute the scale, retain the normalized bands across retries, then run the
output loop on the first accepted diagonal and the same normalized subdiagonal. -/
def normalizedEigenpairRun
    (a : Fin (n + 1) → Word p hp) (b : Fin n → Word p hp)
    (bits : ℕ → GateBits n J) (hn : 2 ≤ n + 1) (hguard : precisionGuard (n + 1) p)
    (hJ : J.Nonempty) (hJvalid : J ⊆ Finset.Icc 1 (n + 1)) :
    Option (NativeAcceptedEigenpairs n p J hp) :=
  match hr : normalizationExponent a b with
  | none => none
  | some r =>
    let aW : Vector (TrialWord n J p) (n + 1) := Vector.ofFn fun i => normalizeTrialWord r (a i)
    let bW : Vector (TrialWord n J p) n := Vector.ofFn fun i => normalizeTrialWord r (b i)
    let av := fun i : Fin (n + 1) => aW[i.val]
    let bv := fun i : Fin n => bW[i.val]
    match htrial : retryRun av bv bits with
    | none => none
    | some trial =>
      let bounds := normalizedTrialInput_bounds (J := J) a b hr
      some (acceptedOutputLoop (hp := hp) av bv bits trial hn hguard hJ hJvalid
        (by simpa only [av, aW, Vector.getElem_ofFn] using bounds.1)
        (by simpa only [bv, bW, Vector.getElem_ofFn] using bounds.2) htrial r)

/-- The scale and gate result retained with the outputs coincide with the
first-accept normalized retry execution. -/
theorem normalizedEigenpairRun_acceptance
    (a : Fin (n + 1) → Word p hp) (b : Fin n → Word p hp)
    (bits : ℕ → GateBits n J) (hn : 2 ≤ n + 1) (hguard : precisionGuard (n + 1) p)
    (hJ : J.Nonempty) (hJvalid : J ⊆ Finset.Icc 1 (n + 1)) :
    (normalizedEigenpairRun a b bits hn hguard hJ hJvalid).map
      (fun out => (out.scaleExponent, out.accepted)) = normalizedRetryRun a b bits := by
  unfold normalizedEigenpairRun normalizedRetryRun
  split
  · rename_i h
    conv => rhs; rw [h]
    rfl
  · rename_i r h
    conv => rhs; rw [h]
    dsimp only [Option.bind_some]
    split
    · rename_i hs
      conv => rhs; rw [hs]
      rfl
    · rename_i trial hs
      conv => rhs; rw [hs]
      rfl

/-- Every returned native output of the normalized branch has the complete
deterministic residual, orthogonality, eigenvalue, and common-witness bounds. -/
theorem normalizedEigenpairRun_accuracy
    (a : Fin (n + 1) → Word p hp) (b : Fin n → Word p hp)
    (bits : ℕ → GateBits n J) (hn : 2 ≤ n + 1) (hguard : precisionGuard (n + 1) p)
    (hJ : J.Nonempty) (hJvalid : J ⊆ Finset.Icc 1 (n + 1))
    (out : NativeAcceptedEigenpairs n p J hp)
    (h : normalizedEigenpairRun a b bits hn hguard hJ hJvalid = some out) :
    ReturnedAccuracy (requestedRankOrder hJvalid) (storedTridiagonal a b)
      (sturmTridiagonal_isHermitian _ _) out.columns out.labels (unitRoundoff p) := by
  unfold normalizedEigenpairRun at h
  split at h
  · contradiction
  · rename_i r hr
    dsimp only at h
    split at h
    · contradiction
    · rename_i trial htrial
      obtain rfl := Option.some.inj h
      apply acceptedOutputLoop_accuracy _ _ _ _ _ _ _ _ _ _ _ _ _ _ hr
      · intro i
        simp only [Vector.getElem_ofFn]
      · intro i
        simp only [Vector.getElem_ofFn]

open MeasureTheory in
/-- For a nonzero input, the almost-sure return of the gate yields an actual
native eigensolver return. The numerical output loop requires no new trials. -/
theorem normalizedEigenpairRun_returns
    (a : Fin (n + 1) → Word p hp) (b : Fin n → Word p hp)
    (hn : 2 ≤ n + 1) (hguard : precisionGuard (n + 1) p)
    (hJ : J.Nonempty) (hJvalid : J ⊆ Finset.Icc 1 (n + 1))
    (hnonzero : storedTridiagonal a b ≠ 0) :
    ∀ᵐ bits ∂retryBitMeasure n J, ∃ out,
      normalizedEigenpairRun a b bits hn hguard hJ hJvalid = some out := by
  filter_upwards [normalizedRetryRun_returns a b hn hguard hJ hJvalid hnonzero]
    with bits hbits
  obtain ⟨r, trial, _, htrial⟩ := hbits
  have heq := normalizedEigenpairRun_acceptance a b bits hn hguard hJ hJvalid
  rw [htrial] at heq
  cases h : normalizedEigenpairRun a b bits hn hguard hJ hJvalid with
  | none => simp [h] at heq
  | some out => exact ⟨out, rfl⟩

end

end NumStability.CertifiedTridiagonalEigenpairs
