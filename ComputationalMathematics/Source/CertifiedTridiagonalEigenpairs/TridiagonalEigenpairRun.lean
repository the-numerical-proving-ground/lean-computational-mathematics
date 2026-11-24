import ComputationalMathematics.Source.CertifiedTridiagonalEigenpairs.AcceptedOutput.NormalizedExecution
import ComputationalMathematics.Source.CertifiedTridiagonalEigenpairs.TrivialBranchesTarget

/-! Dispatch and deterministic correctness for the exact and nontrivial tridiagonal runs. -/

namespace NumStability.CertifiedTridiagonalEigenpairs

open Matrix WithLp NoisyRankCertificate FloatingPointFormat.UnboundedBinary
open scoped Matrix.Norms.L2Operator

/-- The coordinate columns on the exact branches give the same common-witness
guarantee as the nontrivial solver, using the input matrix itself. -/
theorem exactBranch_returnedAccuracy {n k p : ℕ} {hp : 2 ≤ p}
    {a : Fin (n + 1) → Word p hp} {b : Fin n → Word p hp}
    {I : Fin k ↪o Fin (n + 1)} {out : ExactBranchOutput p hp n k}
    (hout : exactBranch a b I = some out) :
    let Q : Matrix (Fin (n + 1)) (Fin k) ℝ := .of fun i j => (out.columns i j).value
    ReturnedAccuracy I (storedTridiagonal a b) (sturmTridiagonal_isHermitian _ _)
      Q (fun j => (out.labels j).value) (unitRoundoff p) := by
  let T := storedTridiagonal a b
  let hT : T.IsHermitian := sturmTridiagonal_isHermitian _ _
  let Q : Matrix (Fin (n + 1)) (Fin k) ℝ := .of fun i j => (out.columns i j).value
  let labels := fun j => (out.labels j).value
  let u := unitRoundoff p
  change ReturnedAccuracy I T hT Q labels u
  obtain ⟨_, hlabel, hcoord, hres, hgram⟩ := exactBranch_correct hout
  change (∀ j, labels j = ascendingEigenvalue hT (I j)) at hlabel
  change (∀ i j, Q i j = if i = I j then 1 else 0) at hcoord
  change T * Q = Q * diagonal labels at hres
  change Qᵀ * Q = 1 at hgram
  have hu : 0 ≤ u := (unitRoundoff_pos p).le
  let V := fun j : Fin k => EuclideanSpace.basisFun (Fin (n + 1)) ℝ (I j)
  have hV (j : Fin k) : toLp 2 (Q.col j) = V j := by
    ext i
    simp [V, EuclideanSpace.basisFun_apply, EuclideanSpace.single_apply, hcoord i j]
  have hQ : (Matrix.of fun i j => V j i) = Q := by
    ext i j
    exact congrArg (fun v : EuclideanSpace ℝ (Fin (n + 1)) => v i) (hV j).symm
  have haction (j : Fin k) : T.toEuclideanLin (V j) = labels j • V j := by
    rw [← hV]
    ext i
    have h := congrArg (fun M : Matrix (Fin (n + 1)) (Fin k) ℝ => M i j) hres
    change (T * Q) i j = (Q * diagonal labels) i j at h
    rw [Matrix.mul_diagonal] at h
    simpa [Matrix.toEuclideanLin, Matrix.toLpLin_apply, Matrix.mulVec, Matrix.mul_apply,
      dotProduct, mul_comm] using h
  refine ⟨?_, ?_, ?_, ?_, ?_, T, hT, V, ?_, ?_, ?_, ?_⟩
  · intro j
    rw [hlabel j, sub_self, abs_zero]
    positivity
  · rw [hres, sub_self, norm_zero]
    positivity
  · rw [hgram, sub_self, norm_zero]
    positivity
  · intro i j hij
    rw [hgram, Matrix.one_apply_ne hij, abs_zero]
    positivity
  · intro j
    rw [hV j]
    have hr := haction j
    rw [← hV] at hr
    change toLp 2 (T *ᵥ Q.col j) = labels j • toLp 2 (Q.col j) at hr
    rw [hr, hV, sub_self, norm_zero]
    positivity
  · rw [sub_self, norm_zero]
    positivity
  · exact (EuclideanSpace.basisFun (Fin (n + 1)) ℝ).orthonormal.comp I I.injective
  · rw [hQ, sub_self]
    change Real.sqrt (∑ i : Fin (n + 1), ∑ j : Fin k, (0 : ℝ) ^ 2) ≤ _
    simp only [zero_pow (by decide : 2 ≠ 0), Finset.sum_const_zero, Real.sqrt_zero]
    positivity
  · intro j
    exact ⟨haction j, (hlabel j).symm, by rw [hV, sub_self, norm_zero]; positivity⟩

theorem exactBranch_eq_none_iff {n k p : ℕ} {hp : 2 ≤ p}
    (a : Fin (n + 1) → Word p hp) (b : Fin n → Word p hp)
    (I : Fin k ↪o Fin (n + 1)) :
    exactBranch a b I = none ↔ storedTridiagonal a b ≠ 0 ∧ 2 ≤ n + 1 := by
  have hs : (exactBranch a b I).isSome ↔ storedTridiagonal a b = 0 ∨ n = 0 := by
    simpa only [exactBranch, Option.isSome_map] using exactBranchLabel_isSome_iff a b
  constructor
  · intro he
    have hn : ¬(storedTridiagonal a b = 0 ∨ n = 0) := by
      simpa [he] using hs.not
    exact ⟨fun hz => hn (.inl hz), by by_contra! h; exact hn (.inr (by omega))⟩
  · rintro ⟨hz, hn⟩
    cases he : exactBranch a b I with
    | none => rfl
    | some out =>
      have h := hs.mp (by simp [he])
      exact (h.elim hz (fun hn0 => by omega)).elim

/-- Native output from either exact dispatch or the first successful refinement. -/
inductive NativeTridiagonalOutput (n p : ℕ) (J : Finset ℕ) (hp : 2 ≤ p) where
  | exact (out : ExactBranchOutput p hp n J.card) (words : List (Word p hp))
  | refined (out : NativeAcceptedEigenpairs n p J hp)

variable {n p : ℕ} {J : Finset ℕ} {hp : 2 ≤ p}

noncomputable def NativeTridiagonalOutput.labels :
    NativeTridiagonalOutput n p J hp → Fin J.card → ℝ
  | .exact out _ => fun j => (out.labels j).value
  | .refined out => out.labels

noncomputable def NativeTridiagonalOutput.columns : NativeTridiagonalOutput n p J hp →
    Matrix (Fin (n + 1)) (Fin J.card) ℝ
  | .exact out _ => .of fun i j => (out.columns i j).value
  | .refined out => out.columns

/-- Handle the exact cases before running the normalized retry and output loops. -/
noncomputable def runTridiagonalEigenpairs
    (a : Fin (n + 1) → Word p hp) (b : Fin n → Word p hp)
    (bits : ℕ → GateBits n J) (hguard : precisionGuard (n + 1) p)
    (hJ : J.Nonempty) (hJvalid : J ⊆ Finset.Icc 1 (n + 1)) :
    Option (NativeTridiagonalOutput n p J hp) :=
  match he : exactBranch a b (requestedRankOrder hJvalid) with
  | some out => some (.exact out (exactBranchOutputWords out))
  | none => (normalizedEigenpairRun a b bits
      ((exactBranch_eq_none_iff ..).mp he).2 hguard hJ hJvalid).map .refined

theorem runTridiagonalEigenpairs_accuracy
    (a : Fin (n + 1) → Word p hp) (b : Fin n → Word p hp)
    (bits : ℕ → GateBits n J) (hguard : precisionGuard (n + 1) p)
    (hJ : J.Nonempty) (hJvalid : J ⊆ Finset.Icc 1 (n + 1))
    (out : NativeTridiagonalOutput n p J hp)
    (h : runTridiagonalEigenpairs a b bits hguard hJ hJvalid = some out) :
    ReturnedAccuracy (requestedRankOrder hJvalid) (storedTridiagonal a b)
      (sturmTridiagonal_isHermitian _ _) out.columns out.labels (unitRoundoff p) := by
  unfold runTridiagonalEigenpairs at h
  split at h
  · rename_i exactOut he
    obtain rfl := Option.some.inj h
    exact exactBranch_returnedAccuracy he
  · rename_i he
    have hn := ((exactBranch_eq_none_iff ..).mp he).2
    cases hr : normalizedEigenpairRun a b bits hn hguard hJ hJvalid with
    | none => simp [hr] at h
    | some out =>
      simp only [hr, Option.map_some] at h
      cases Option.some.inj h
      exact normalizedEigenpairRun_accuracy a b bits hn hguard hJ hJvalid out hr

open MeasureTheory in
theorem runTridiagonalEigenpairs_returns
    (a : Fin (n + 1) → Word p hp) (b : Fin n → Word p hp)
    (hguard : precisionGuard (n + 1) p)
    (hJ : J.Nonempty) (hJvalid : J ⊆ Finset.Icc 1 (n + 1)) :
    ∀ᵐ bits ∂retryBitMeasure n J, ∃ out,
      runTridiagonalEigenpairs a b bits hguard hJ hJvalid = some out := by
  cases he : exactBranch a b (requestedRankOrder hJvalid) with
  | some out =>
    exact ae_of_all _ fun bits =>
      ⟨.exact out (exactBranchOutputWords out), by
        unfold runTridiagonalEigenpairs
        split
        · rename_i output houtput
          rw [he] at houtput
          cases Option.some.inj houtput
          rfl
        · rename_i hnone
          rw [he] at hnone
          cases hnone⟩
  | none =>
    obtain ⟨hnonzero, hn⟩ := (exactBranch_eq_none_iff ..).mp he
    filter_upwards [normalizedEigenpairRun_returns a b hn hguard hJ hJvalid hnonzero] with bits hb
    obtain ⟨out, ho⟩ := hb
    exact ⟨.refined out, by
      unfold runTridiagonalEigenpairs
      split
      · rename_i output houtput
        rw [he] at houtput
        cases houtput
      · simp only [ho, Option.map_some]⟩

end NumStability.CertifiedTridiagonalEigenpairs
