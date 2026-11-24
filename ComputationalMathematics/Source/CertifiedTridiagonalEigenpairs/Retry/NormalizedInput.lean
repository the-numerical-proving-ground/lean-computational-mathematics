import ComputationalMathematics.Analysis.FloatingPointArithmetic.UnboundedBinary.Widen
import ComputationalMathematics.Source.CertifiedTridiagonalEigenpairs.Retry.CertifiedExecution
import ComputationalMathematics.Source.CertifiedTridiagonalEigenpairs.Scaling

/-! The fixed normalized input supplied to every perturbation trial. -/

namespace NumStability.CertifiedTridiagonalEigenpairs

open FloatingPointFormat.UnboundedBinary

/-- Exact dyadic scaling followed by conversion to the working precision. -/
def normalizeTrialWord {n p : ℕ} {J : Finset ℕ} {hp : 2 ≤ p}
    (r : ℤ) (x : Word p hp) : TrialWord n J p :=
  (x.scale (-r)).widen (workingPrecision_ge_two (n + 1) J.card p)
    (by unfold workingPrecision; omega)

@[simp] theorem value_normalizeTrialWord {n p : ℕ} {J : Finset ℕ} {hp : 2 ≤ p}
    (r : ℤ) (x : Word p hp) :
    (normalizeTrialWord (n := n) (J := J) r x).value = (x.scale (-r)).value :=
  Word.value_widen _ _ _

/-- Both working-precision bands satisfy the input bounds of the actual gate
at the scale selected from the original stored matrix. -/
theorem normalizedTrialInput_bounds {n p : ℕ} {J : Finset ℕ} {hp : 2 ≤ p}
    (a : Fin (n + 1) → Word p hp) (b : Fin n → Word p hp)
    {r : ℤ} (hr : normalizationExponent a b = some r) :
    (∀ i, |(normalizeTrialWord (n := n) (J := J) r (a i)).value| ≤ 1 / 4) ∧
    (∀ e, |(normalizeTrialWord (n := n) (J := J) r (b e)).value| ≤ 1 / 4) := by
  have hentry := (normalizedTridiagonal_bounds a b hr).1
  constructor
  · intro i
    simpa only [normalizedTridiagonal, storedTridiagonal, sturmTridiagonal_diagonal,
      value_normalizeTrialWord] using hentry i i
  · intro e
    simpa only [normalizedTridiagonal, storedTridiagonal, sturmTridiagonal_upper,
      value_normalizeTrialWord] using hentry e.castSucc e.succ

/-- The gate's input reconstructed from its two stored bands is the scaled
input of the paper. Widening does not change either band. -/
theorem normalizedTrialMatrix_eq {n p : ℕ} {J : Finset ℕ} {hp : 2 ≤ p}
    (a : Fin (n + 1) → Word p hp) (b : Fin n → Word p hp) (r : ℤ) :
    sturmTridiagonal
      (fun i => (normalizeTrialWord (n := n) (J := J) r (a i)).value)
      (fun i => (normalizeTrialWord (n := n) (J := J) r (b i)).value) =
        normalizedTridiagonal a b r := by
  simp only [value_normalizeTrialWord, normalizedTridiagonal, storedTridiagonal]

/-- Materialize the two normalized bands once, before any trial. The same
working-precision values are read by each invocation of the gate. -/
noncomputable def normalizedRetryRun {n p : ℕ} {J : Finset ℕ} {hp : 2 ≤ p}
    (a : Fin (n + 1) → Word p hp) (b : Fin n → Word p hp)
    (bits : ℕ → GateBits n J) : Option (ℤ × RetryResult n J p) :=
  (normalizationExponent a b).bind fun r =>
    let diagonal : Vector (TrialWord n J p) (n + 1) :=
      Vector.ofFn fun i => normalizeTrialWord r (a i)
    let subdiagonal : Vector (TrialWord n J p) n :=
      Vector.ofFn fun i => normalizeTrialWord r (b i)
    (retryRun (fun i => diagonal[i.val]) (fun i => subdiagonal[i.val]) bits).map fun result => (r, result)

/-- A returned scale and matrix come from one normalization and a successful
call to the fixed-input retry loop. -/
theorem normalizedRetryRun_some {n p : ℕ} {J : Finset ℕ} {hp : 2 ≤ p}
    {a : Fin (n + 1) → Word p hp} {b : Fin n → Word p hp}
    {bits : ℕ → GateBits n J} {r : ℤ} {result : RetryResult n J p}
    (hrun : normalizedRetryRun a b bits = some (r, result)) :
    normalizationExponent a b = some r ∧
    retryRun (fun i => normalizeTrialWord (J := J) r (a i))
      (fun i => normalizeTrialWord (J := J) r (b i)) bits = some result := by
  cases hs : normalizationExponent a b with
  | none => simp [normalizedRetryRun, hs] at hrun
  | some e =>
    simp only [normalizedRetryRun, hs, Option.bind_some, Vector.getElem_ofFn] at hrun
    cases ht : retryRun (fun i => normalizeTrialWord (J := J) e (a i))
        (fun i => normalizeTrialWord (J := J) e (b i)) bits with
    | none => simp [ht] at hrun
    | some accepted =>
      simp only [ht, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hrun
      obtain ⟨rfl, rfl⟩ := hrun
      exact ⟨rfl, ht⟩

open MeasureTheory in
/-- The branch with a nonzero input of order at least two returns the
computed scale and the first accepted trial almost surely. -/
theorem normalizedRetryRun_returns {n p : ℕ} {J : Finset ℕ} {hp : 2 ≤ p}
    (a : Fin (n + 1) → Word p hp) (b : Fin n → Word p hp)
    (hn : 2 ≤ n + 1) (hguard : precisionGuard (n + 1) p)
    (hJ : J.Nonempty) (hJbounds : J ⊆ Finset.Icc 1 (n + 1))
    (hnonzero : storedTridiagonal a b ≠ 0) :
    ∀ᵐ bits ∂retryBitMeasure n J, ∃ (r : ℤ) (result : RetryResult n J p),
      normalizationExponent a b = some r ∧
      normalizedRetryRun a b bits = some (r, result) := by
  cases hs : normalizationExponent a b with
  | none => exact (hnonzero ((normalizationExponent_eq_none_iff a b).mp hs)).elim
  | some r =>
    obtain ⟨ha, hb⟩ := normalizedTrialInput_bounds (J := J) a b hs
    have h := (certifiedRetryRun
      (fun i => normalizeTrialWord (J := J) r (a i))
      (fun i => normalizeTrialWord (J := J) r (b i))
      hn hguard hJ hJbounds ha hb).1
    filter_upwards [h] with bits hbits
    obtain ⟨result, hresult⟩ := hbits
    refine ⟨r, result, rfl, ?_⟩
    simp only [normalizedRetryRun, hs, Option.bind_some, Vector.getElem_ofFn, hresult, Option.map_some]

end NumStability.CertifiedTridiagonalEigenpairs
