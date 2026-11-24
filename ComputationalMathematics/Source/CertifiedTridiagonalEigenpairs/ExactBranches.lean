import ComputationalMathematics.Source.CertifiedTridiagonalEigenpairs.Scaling
import ComputationalMathematics.Analysis.Eigenvalues.StrictSpectralCount

/-!
# Exact zero and scalar branches

For a zero matrix the returned labels are zero and the returned columns are
the requested coordinate unit vectors. In dimension one the label is the
stored diagonal word and the only possible nonempty request has column `(1)`.
These branches use no trial and return native words directly.
-/

namespace NumStability.CertifiedTridiagonalEigenpairs

open FloatingPointFormat.UnboundedBinary
open NoisyRankCertificate (ascendingEigenvalue)
open scoped Matrix

variable {p n k : ℕ} {hp : 2 ≤ p}

/-- The common label for an exact branch, if either exact branch applies. -/
def exactBranchLabel (a : Fin (n + 1) → Word p hp) (b : Fin n → Word p hp) :
    Option (Word p hp) :=
  match largestStoredEntry a b with
  | .zero => some .zero
  | .normal .. => if n = 0 then some (a 0) else none

theorem exactBranchLabel_eq_some_zero
    {a : Fin (n + 1) → Word p hp} {b : Fin n → Word p hp}
    (hz : storedTridiagonal a b = 0) : exactBranchLabel a b = some .zero := by
  have h := (normalizationExponent_eq_none_iff a b).mpr hz
  unfold exactBranchLabel
  cases H : largestStoredEntry a b with
  | zero => rfl
  | normal negative m e hm => simp [normalizationExponent, H, coveringExponent] at h

theorem exactBranchLabel_eq_some_scalar
    (a : Fin 1 → Word p hp) (b : Fin 0 → Word p hp) :
    exactBranchLabel a b = some (a 0) := by
  have hscan : largestStoredEntry a b = a 0 := by
    simp only [largestStoredEntry, List.ofFn_succ, List.ofFn_zero,
      List.append_nil, List.foldr_cons, List.foldr_nil]
    cases h : a 0 <;> rfl
  unfold exactBranchLabel
  rw [hscan]
  cases a 0 <;> simp

theorem exactBranchLabel_isSome_iff
    (a : Fin (n + 1) → Word p hp) (b : Fin n → Word p hp) :
    (exactBranchLabel a b).isSome ↔ storedTridiagonal a b = 0 ∨ n = 0 := by
  unfold exactBranchLabel
  have h := normalizationExponent_eq_none_iff a b
  cases H : largestStoredEntry a b with
  | zero =>
    have hzero : storedTridiagonal a b = 0 := by
      apply h.mp
      simp [normalizationExponent, H, coveringExponent]
    simp [hzero]
  | normal negative m e hm =>
    have hne : storedTridiagonal a b ≠ 0 := by
      intro hzero
      have hz := h.mpr hzero
      simp [normalizationExponent, H, coveringExponent] at hz
    simp [hne]

/-- One column of the exact native output, in the original coordinate system. -/
def coordinateWord (p : ℕ) (hp : 2 ≤ p) (i j : Fin (n + 1)) : Word p hp :=
  if i = j then
    .normal false (format p hp).minNormalMantissa 1 (format p hp).minNormalMantissa_normalized
  else .zero

theorem value_coordinateWord (i j : Fin (n + 1)) :
    (coordinateWord p hp i j).value = if i = j then 1 else 0 := by
  by_cases hij : i = j
  · rw [coordinateWord, if_pos hij, if_pos hij]
    change (format p hp).normalizedValue false (format p hp).minNormalMantissa 1 = 1
    rw [(format p hp).normalizedValue_false_minNormalMantissa_eq]
    simp
  · simp [coordinateWord, hij, Word.value]

/-- Packed native output on the exact branches. The request embedding puts the
columns and labels in their original rank order. -/
structure ExactBranchOutput (p : ℕ) (hp : 2 ≤ p) (n k : ℕ) where
  labels : Fin k → Word p hp
  columns : Fin (n + 1) → Fin k → Word p hp
  trials : ℕ

/-- Return the exact output, or dispatch the input to the nontrivial path. -/
def exactBranch (a : Fin (n + 1) → Word p hp) (b : Fin n → Word p hp)
    (J : Fin k ↪o Fin (n + 1)) : Option (ExactBranchOutput p hp n k) :=
  (exactBranchLabel a b).map fun label =>
    ⟨fun _ => label, fun i j => coordinateWord p hp i (J j), 0⟩

theorem storedTridiagonal_eq_label_smul_one
    {a : Fin (n + 1) → Word p hp} {b : Fin n → Word p hp} {label : Word p hp}
    (hlabel : exactBranchLabel a b = some label) :
    storedTridiagonal a b = label.value • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) := by
  have hs : (exactBranchLabel a b).isSome := by simp [hlabel]
  rcases (exactBranchLabel_isSome_iff a b).mp hs with hzero | hdim
  · rw [exactBranchLabel_eq_some_zero hzero, Option.some.injEq] at hlabel
    subst label
    simpa [Word.value] using hzero
  · subst n
    rw [exactBranchLabel_eq_some_scalar, Option.some.injEq] at hlabel
    subst label
    ext i j
    have hij : j = i := by apply Fin.ext; omega
    have h0 : i = 0 := by apply Fin.ext; simp
    subst j
    simp [storedTridiagonal, sturmTridiagonal_diagonal, h0]

private theorem orderedEigenvalue_scalar_matrix {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.IsHermitian) (x : ℝ) (h : A = x • (1 : Matrix (Fin n) (Fin n) ℝ))
    (i : Fin n) : ascendingEigenvalue hA i = x := by
  let v := hermitianOrderedEigenbasis hA i.rev
  have hnorm : ‖v‖ = 1 := (hermitianOrderedEigenbasis hA).orthonormal.norm_eq_one i.rev
  have hv := matrixRayleighForm_hermitianOrderedEigenbasis hA i.rev
  change matrixRayleighForm A v = ascendingEigenvalue hA i at hv
  rw [← hv]
  rw [h]
  simp [matrixRayleighForm, Matrix.toLpLin_one, real_inner_smul_right, hnorm]

/-- An exact result has the requested indexed eigenvalues, coordinate
eigenvectors and orthonormal columns, with zero trials. -/
theorem exactBranch_correct
    {a : Fin (n + 1) → Word p hp} {b : Fin n → Word p hp}
    {J : Fin k ↪o Fin (n + 1)} {out : ExactBranchOutput p hp n k}
    (hout : exactBranch a b J = some out) :
    let T := storedTridiagonal a b
    let hT : T.IsHermitian := sturmTridiagonal_isHermitian _ _
    let Q : Matrix (Fin (n + 1)) (Fin k) ℝ := fun i j => (out.columns i j).value
    let D := Matrix.diagonal (fun j => (out.labels j).value)
    out.trials = 0 ∧ (∀ j, (out.labels j).value = ascendingEigenvalue hT (J j)) ∧
      (∀ i j, Q i j = if i = J j then 1 else 0) ∧ T * Q = Q * D ∧ Qᵀ * Q = 1 := by
  dsimp only
  unfold exactBranch at hout
  cases H : exactBranchLabel a b with
  | none => simp [H] at hout
  | some label =>
    rw [H, Option.map_some, Option.some.injEq] at hout
    subst out
    have hT := storedTridiagonal_eq_label_smul_one H
    refine ⟨rfl, ?_, (fun i j => value_coordinateWord i (J j)), ?_, ?_⟩
    · intro j
      exact (orderedEigenvalue_scalar_matrix (sturmTridiagonal_isHermitian _ _)
        label.value hT (J j)).symm
    · have hdiag : storedTridiagonal a b = Matrix.diagonal (fun _ => label.value) := by
        rw [hT]
        ext i j
        by_cases hij : i = j <;> simp [hij]
      rw [hdiag]
      ext i j
      simp [Matrix.diagonal_mul, Matrix.mul_diagonal, mul_comm]
    · classical
      ext i j
      simp only [Matrix.mul_apply, Matrix.transpose_apply, value_coordinateWord]
      rw [Finset.sum_eq_single (J i)]
      · simp [Matrix.one_apply, J.injective.eq_iff]
      · intro l _ hne
        simp [hne]
      · simp


/-- A charge bound for each successful exact path. The packed scan allows up
to eight operations per stored slot, including index and representation work.
The fixed charge covers dispatch and the constants used in the output.
Each output label is written once and each dense coordinate requires a comparison
and a write. -/
def exactBranchWorkBound (n k : ℕ) : ℕ :=
  (2 * n + 1) * 8 + 4 + k + 2 * ((n + 1) * k)

/-- The exact-path bound is uniform in the input precision and the data. -/
theorem exactBranchWorkBound_le {n k : ℕ} (hk : 0 < k) :
    exactBranchWorkBound n k ≤ 23 * ((n + 1) * k) := by
  have h : n + 1 ≤ (n + 1) * k := Nat.le_mul_of_pos_right _ hk
  have h' : k ≤ (n + 1) * k := Nat.le_mul_of_pos_left _ (by omega)
  unfold exactBranchWorkBound
  omega

end NumStability.CertifiedTridiagonalEigenpairs
