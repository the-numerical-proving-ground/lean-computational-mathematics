import ComputationalMathematics.Source.CertifiedTridiagonalEigenpairs.BidiagonalSVDScaling
import ComputationalMathematics.Source.CertifiedTridiagonalEigenpairs.ExactBranches
import ComputationalMathematics.Analysis.SingularValues.FullRealSVD.Unsorted

/-!
# Exact branches of the selected bidiagonal SVD

The zero branch writes the two requested coordinate arrays. The scalar branch
clears the label's sign bit and uses that original sign for the left unit vector.
The branches use the original word precision throughout.
-/

namespace NumStability.CertifiedTridiagonalEigenpairs

open FloatingPointFormat.UnboundedBinary

variable {p n k : ℕ} {hp : 2 ≤ p}

private def unsignedWord : Word p hp → Word p hp
  | .zero => .zero
  | .normal _ m e hm => .normal false m e hm

private def wordSign : Word p hp → Bool
  | .zero => false
  | .normal negative _ _ _ => negative

private noncomputable def signFactor (negative : Bool) : ℝ :=
  if negative then -1 else 1

private theorem value_unsignedWord (w : Word p hp) : (unsignedWord w).value = |w.value| := by
  cases w with
  | zero => simp [unsignedWord, Word.value]
  | normal negative m e hm =>
    change (format p hp).normalizedValue false m e =
      |(format p hp).normalizedValue negative m e|
    rw [FloatingPointFormat.normalizedValue_abs, ←
      FloatingPointFormat.normalizedValue_abs (format p hp) false]
    exact (abs_of_nonneg
      (FloatingPointFormat.normalizedValue_false_pos hm).le).symm

private theorem signFactor_mul_unsignedWord (w : Word p hp) :
    signFactor (wordSign w) * (unsignedWord w).value = w.value := by
  cases w with
  | zero => simp [unsignedWord, Word.value]
  | normal negative m e hm =>
    cases negative
    · simp [signFactor, wordSign, unsignedWord]
    · simp [signFactor, wordSign, unsignedWord, Word.value,
        FloatingPointFormat.normalizedValue_true_eq_neg_false]

private def signedCoordinateWord (p : ℕ) (hp : 2 ≤ p) (s : Bool)
    (i j : Fin (n + 1)) : Word p hp :=
  if s then
    if i = j then .normal true (format p hp).minNormalMantissa 1
      (format p hp).minNormalMantissa_normalized else .zero
  else coordinateWord p hp i j

private theorem value_signedCoordinateWord (s : Bool) (i j : Fin (n + 1)) :
    (signedCoordinateWord p hp s i j).value =
      signFactor s * (coordinateWord p hp i j).value := by
  cases s
  · simp [signedCoordinateWord, signFactor]
  · rw [value_coordinateWord]
    by_cases hij : i = j
    · simp [signedCoordinateWord, signFactor, hij, Word.value,
        FloatingPointFormat.normalizedValue_true_eq_neg_false,
        FloatingPointFormat.normalizedValue_false_minNormalMantissa_eq]
    · simp [signedCoordinateWord, signFactor, hij, Word.value]

/-- The actual p-bit labels and both dense requested column arrays. -/
structure BidiagonalExactOutput (p : ℕ) (hp : 2 ≤ p) (n k : ℕ) where
  labels : Fin k → Word p hp
  left : Fin (n + 1) → Fin k → Word p hp
  right : Fin (n + 1) → Fin k → Word p hp
  trials : ℕ

/-- The exact dispatch scans the packed input once, then returns native words. -/
def bidiagonalExactBranch (a : Fin (n + 1) → Word p hp) (b : Fin n → Word p hp)
    (J : Fin k ↪o Fin (n + 1)) : Option (BidiagonalExactOutput p hp n k) :=
  (exactBranchLabel a b).map fun w =>
    ⟨fun _ => unsignedWord w, fun i j => signedCoordinateWord p hp (wordSign w) i (J j),
      fun i j => coordinateWord p hp i (J j), 0⟩

theorem bidiagonalExactBranch_isSome_iff (upper : Bool)
    (a : Fin (n + 1) → Word p hp) (b : Fin n → Word p hp) (J : Fin k ↪o Fin (n + 1)) :
    (bidiagonalExactBranch a b J).isSome ↔ storedBidiagonal upper a b = 0 ∨ n = 0 := by
  have hz := (normalizationExponent_eq_none_iff a b).symm.trans
    (bidiagonal_normalizationExponent_eq_none_iff upper a b)
  simpa only [bidiagonalExactBranch, Option.isSome_map, hz] using exactBranchLabel_isSome_iff a b

/-- The zero branch returns zero labels and the requested coordinate columns in both factors. -/
theorem bidiagonalExactBranch_zero {upper : Bool}
    {a : Fin (n + 1) → Word p hp} {b : Fin n → Word p hp}
    (J : Fin k ↪o Fin (n + 1)) (hB : storedBidiagonal upper a b = 0) :
    bidiagonalExactBranch a b J =
      some ⟨fun _ => .zero, fun i j => coordinateWord p hp i (J j),
        fun i j => coordinateWord p hp i (J j), 0⟩ := by
  have hz := (normalizationExponent_eq_none_iff a b).mp
    ((bidiagonal_normalizationExponent_eq_none_iff upper a b).mpr hB)
  simp [bidiagonalExactBranch, exactBranchLabel_eq_some_zero hz, unsignedWord, wordSign,
    signedCoordinateWord]

/-- The scalar branch returns the absolute input, its sign on the left, and one on the right. -/
theorem bidiagonalExactBranch_scalar
    (a : Fin 1 → Word p hp) (b : Fin 0 → Word p hp) (J : Fin k ↪o Fin 1) :
    ∃ out, bidiagonalExactBranch a b J = some out ∧ out.trials = 0 ∧
      (∀ j, (out.labels j).value = |(a 0).value|) ∧
      (∀ i j, (out.left i j).value = if (a 0).value < 0 then -1 else 1) ∧
      (∀ i j, (out.right i j).value = 1) := by
  simp only [bidiagonalExactBranch, exactBranchLabel_eq_some_scalar, Option.map_some]
  refine ⟨_, rfl, rfl, fun _ => value_unsignedWord _, ?_, ?_⟩
  · intro i j
    rw [value_signedCoordinateWord, value_coordinateWord, if_pos ((Fin.eq_zero i).trans (Fin.eq_zero (J j)).symm),
      mul_one]
    cases a 0 with
    | zero => simp [wordSign, signFactor, Word.value]
    | normal sign m e hm =>
      cases sign
      · have hn := not_lt.mpr (FloatingPointFormat.normalizedValue_false_pos (e := e) hm).le
        simp [wordSign, signFactor, Word.value, hn]
      · simp [wordSign, signFactor, Word.value,
          FloatingPointFormat.normalizedValue_true_neg (e := e) hm]
  · intro i j
    simp [value_coordinateWord, (Fin.eq_zero i).trans (Fin.eq_zero (J j)).symm]

private theorem storedBidiagonal_eq_of_exact_label (upper : Bool)
    {a : Fin (n + 1) → Word p hp} {b : Fin n → Word p hp} {w : Word p hp}
    (hw : exactBranchLabel a b = some w) :
    storedBidiagonal upper a b = w.value • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) := by
  have hs := (exactBranchLabel_isSome_iff a b).mp (by simp [hw])
  rcases hs with hz | rfl
  · rw [exactBranchLabel_eq_some_zero hz, Option.some.injEq] at hw
    subst w
    rw [((bidiagonal_normalizationExponent_eq_none_iff upper a b).mp
      ((normalizationExponent_eq_none_iff a b).mpr hz))]
    simp [Word.value]
  · rw [exactBranchLabel_eq_some_scalar, Option.some.injEq] at hw
    subst w
    ext i j
    have hi : i = 0 := Fin.eq_zero i
    have hj : j = 0 := Fin.eq_zero j
    simp [hi, hj]

/-- Either exact path has exact requested singular values and zero residuals,
orthonormal returned columns, and a single common full ordered SVD of the input. -/
theorem bidiagonalExactBranch_correct (upper : Bool)
    {a : Fin (n + 1) → Word p hp} {b : Fin n → Word p hp}
    {J : Fin k ↪o Fin (n + 1)} {out : BidiagonalExactOutput p hp n k}
    (hout : bidiagonalExactBranch a b J = some out) :
    let B := storedBidiagonal upper a b
    let U : Matrix (Fin (n + 1)) (Fin k) ℝ := fun i j => (out.left i j).value
    let V : Matrix (Fin (n + 1)) (Fin k) ℝ := fun i j => (out.right i j).value
    let d : Fin k → ℝ := fun j => (out.labels j).value
    out.trials = 0 ∧ (∀ j, d j = ascendingRealSpectrum B (J j)) ∧
      (∀ j, 0 ≤ d j) ∧ Monotone d ∧
      B * V = U * Matrix.diagonal d ∧ B.transpose * U = V * Matrix.diagonal d ∧
      U.transpose * U = 1 ∧ V.transpose * V = 1 ∧
      ∃ Uf Vf : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ,
        Uf.transpose * Uf = 1 ∧ Vf.transpose * Vf = 1 ∧
        B = Uf * Matrix.diagonal (ascendingRealSpectrum B) * Vf.transpose ∧
        (∀ i j, U i j = Uf i (J j)) ∧ ∀ i j, V i j = Vf i (J j) := by
  dsimp only
  unfold bidiagonalExactBranch at hout
  cases hw : exactBranchLabel a b with
  | none => simp [hw] at hout
  | some w =>
    rw [hw, Option.map_some, Option.some.injEq] at hout
    subst out
    let s := signFactor (wordSign w)
    let d := (unsignedWord w).value
    let B := storedBidiagonal upper a b
    let Uf : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ := s • 1
    let Vf : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ := 1
    let V : Matrix (Fin (n + 1)) (Fin k) ℝ := fun i j => (coordinateWord p hp i (J j)).value
    let U : Matrix (Fin (n + 1)) (Fin k) ℝ :=
      fun i j => (signedCoordinateWord p hp (wordSign w) i (J j)).value
    have hsd : s * d = w.value := signFactor_mul_unsignedWord w
    have hs2 : s * s = 1 := by
      dsimp [s]
      cases wordSign w <;> simp [signFactor]
    have hds : w.value * s = d := by
      rw [← hsd, mul_comm s d, mul_assoc, hs2, mul_one]
    have hd : 0 ≤ d := by
      dsimp [d]
      rw [value_unsignedWord]
      exact abs_nonneg _
    have hB : B = w.value • 1 := storedBidiagonal_eq_of_exact_label upper hw
    have hBt : B.transpose = w.value • 1 := by simp [hB, Matrix.transpose_smul]
    have hU : U = s • V := by
      ext i j
      exact value_signedCoordinateWord _ i (J j)
    have hUf : Uf.transpose * Uf = 1 := by
      simp [Uf, Matrix.transpose_smul, smul_smul, hs2]
    have hVf : Vf.transpose * Vf = 1 := by simp [Vf]
    have hdiag : Matrix.diagonal (fun _ : Fin (n + 1) => d) = d • 1 := by
      ext i j
      by_cases hij : i = j <;> simp [hij]
    have hfact : B = Uf * Matrix.diagonal (fun _ => d) * Vf.transpose := by
      simp [Uf, Vf, hB, hdiag, smul_smul, (mul_comm d s).trans hsd]
    have hspec : ascendingRealSpectrum B = fun _ => d :=
      ascendingRealSpectrum_eq_sorted_of_orthogonal_factorization B Uf Vf _ hUf hVf
        (fun _ => hd) hfact
    have hV : V.transpose * V = 1 := by
      classical
      ext i j
      simp only [Matrix.mul_apply, Matrix.transpose_apply, V, value_coordinateWord]
      rw [Finset.sum_eq_single (J i)]
      · simp [Matrix.one_apply, J.injective.eq_iff]
      · intro l _ hne
        simp [hne]
      · simp
    have hD : Matrix.diagonal (fun _ : Fin k => d) = d • 1 := by
      ext i j
      by_cases hij : i = j <;> simp [hij]
    refine ⟨rfl, fun j => (congrFun hspec (J j)).symm, fun _ => hd, fun _ _ _ => le_rfl,
      ?_, ?_, ?_, hV, Uf, Vf, hUf, hVf, ?_, ?_, ?_⟩
    · change B * V = U * Matrix.diagonal (fun _ => d)
      simp [hB, hU, hD, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hsd, mul_comm]
    · change B.transpose * U = V * Matrix.diagonal (fun _ => d)
      simp [hBt, hU, hD, Matrix.smul_mul, Matrix.mul_smul, smul_smul, (mul_comm s w.value).trans hds]
    · change U.transpose * U = 1
      simp [hU, Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hs2, hV]
    · rw [hspec]
      exact hfact
    · intro i j
      change U i j = Uf i (J j)
      simp [hU, V, Uf, value_coordinateWord, Matrix.one_apply]
    · intro i j
      change V i j = Vf i (J j)
      simp [V, Vf, value_coordinateWord, Matrix.one_apply]

/-- One word for each label and one word per entry of the two dense arrays. -/
def bidiagonalExactOutputWords (out : BidiagonalExactOutput p hp n k) : List (Word p hp) :=
  List.ofFn out.labels ++
    List.ofFn (fun i : Fin (k * (n + 1)) =>
      let ji := (finProdFinEquiv (m := k) (n := n + 1)).symm i
      out.left ji.2 ji.1) ++
    List.ofFn (fun i : Fin (k * (n + 1)) =>
      let ji := (finProdFinEquiv (m := k) (n := n + 1)).symm i
      out.right ji.2 ji.1)

theorem bidiagonalExactOutputWords_length (out : BidiagonalExactOutput p hp n k) :
    (bidiagonalExactOutputWords out).length = k + 2 * ((n + 1) * k) := by
  simp [bidiagonalExactOutputWords, Nat.mul_comm, two_mul]

end NumStability.CertifiedTridiagonalEigenpairs
