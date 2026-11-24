import ComputationalMathematics.Analysis.MatrixNorms.Nuclear.Basic
import Mathlib.Analysis.CStarAlgebra.Matrix

/-! Exact rectangular nuclear Sylvester estimates by finite normalized contraction.
No integral representation or assumed nuclear norm structure. Empty shapes are included. -/

open Matrix
open scoped BigOperators Matrix.Norms.L2Operator
namespace NumStability.PositiveSylvesterNuclear

private theorem norm_normalized_le {n : Type*} [Fintype n] [DecidableEq n]
    (G : Matrix n n ℝ) (hG : G.IsHermitian) {β γ : ℝ}
    (hβ : 0 < β) (hγβ : γ ≤ β) (hspec : spectrum ℝ G ⊆ Set.Icc γ β) :
    ‖1 - β⁻¹ • G‖ ≤ 1 - γ / β := by
  have hρ0 : 0 ≤ 1 - γ / β := sub_nonneg.mpr ((div_le_one hβ).2 hγβ)
  let e := (Unitary.conjStarAlgAut ℝ (Matrix n n ℝ)) hG.eigenvectorUnitary
  have he : e (Matrix.diagonal hG.eigenvalues) = G := by
    simpa [e, Function.comp_def] using hG.spectral_theorem.symm
  have heq : 1 - β⁻¹ • G =
      e (Matrix.diagonal (fun i : n => 1 - β⁻¹ * hG.eigenvalues i)) := by
    have hd : Matrix.diagonal (fun i : n => 1 - β⁻¹ * hG.eigenvalues i) =
        1 - β⁻¹ • Matrix.diagonal hG.eigenvalues := by
      rw [← Matrix.diagonal_one, ← Matrix.diagonal_smul, ← Matrix.diagonal_sub]
      rfl
    rw [hd, map_sub, map_one, map_smul, he]
  rw [heq]
  simp only [e, Unitary.conjStarAlgAut_apply, ← Unitary.coe_star,
    CStarRing.norm_mul_coe_unitary, CStarRing.norm_coe_unitary_mul,
    Matrix.l2_opNorm_diagonal]
  apply (pi_norm_le_iff_of_nonneg hρ0).mpr
  intro i
  have hi := hspec (hG.eigenvalues_mem_spectrum_real i)
  have ht0 : 0 ≤ 1 - β⁻¹ * hG.eigenvalues i := by
    rw [← div_eq_inv_mul]
    exact sub_nonneg.mpr ((div_le_one hβ).2 hi.2)
  rw [Real.norm_eq_abs, abs_of_nonneg ht0, div_eq_inv_mul]
  exact sub_le_sub_left (mul_le_mul_of_nonneg_left hi.1 (inv_nonneg.mpr hβ.le)) 1

/-- A finite contraction proof of the positive Sylvester bound. Both square
coefficient matrices share a normalization scale; the unknown is rectangular. -/
theorem norm_le_of_contractions {m n : ℕ}
    (A : Matrix (Fin m) (Fin m) ℝ) (B : Matrix (Fin n) (Fin n) ℝ)
    (X F : Matrix (Fin m) (Fin n) ℝ) (a b β : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hβ : 0 < β)
    (hA : realMatrixOperatorNorm (1 - β⁻¹ • A) ≤ 1 - a / β)
    (hB : realMatrixOperatorNorm (1 - β⁻¹ • B) ≤ 1 - b / β)
    (hXF : A * X + X * B = F) :
    realMatrixNuclearNorm X ≤ realMatrixNuclearNorm F / (a + b) := by
  let T := (1 : Matrix (Fin m) (Fin m) ℝ) - β⁻¹ • A
  let U := (1 : Matrix (Fin n) (Fin n) ℝ) - β⁻¹ • B
  have hT : ‖T‖ ≤ 1 - a / β := hA
  have hU : ‖U‖ ≤ 1 - b / β := hB
  have hTX : β • (T * X) = β • X - A * X := by
    dsimp only [T]
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.smul_mul, smul_sub, smul_smul,
      mul_inv_cancel₀ hβ.ne', one_smul]
  have hXU : β • (X * U) = β • X - X * B := by
    dsimp only [U]
    rw [Matrix.mul_sub, Matrix.mul_one, Matrix.mul_smul, smul_sub, smul_smul,
      mul_inv_cancel₀ hβ.ne', one_smul]
  have hid : (2 * β) • X = β • (T * X + X * U) + F := by
    ext i j
    have ht := congrFun (congrFun hTX i) j
    have hu := congrFun (congrFun hXU i) j
    have hf := congrFun (congrFun hXF i) j
    simp only [Matrix.smul_apply, smul_eq_mul, Matrix.add_apply, Matrix.sub_apply] at ht hu hf ⊢
    nlinarith
  have hprod : realMatrixNuclearNorm (T * X) + realMatrixNuclearNorm (X * U) ≤
      (1 - a / β) * realMatrixNuclearNorm X + realMatrixNuclearNorm X * (1 - b / β) := by
    exact add_le_add ((realMatrixNuclearNorm_rectMatMul_left_le T X).trans
      (mul_le_mul_of_nonneg_right hT (realMatrixNuclearNorm_nonneg X)))
      ((realMatrixNuclearNorm_rectMatMul_right_le X U).trans
      (mul_le_mul_of_nonneg_left hU (realMatrixNuclearNorm_nonneg X)))
  have hnorm : (2 * β) * realMatrixNuclearNorm X ≤
      β * ((1 - a / β) * realMatrixNuclearNorm X + realMatrixNuclearNorm X * (1 - b / β)) + realMatrixNuclearNorm F := by
    calc
      _ = realMatrixNuclearNorm ((2 * β) • X) := by
        rw [realMatrixNuclearNorm_smul, abs_of_pos (mul_pos (by norm_num) hβ)]
      _ = realMatrixNuclearNorm (β • (T * X + X * U) + F) := by rw [hid]
      _ ≤ realMatrixNuclearNorm (β • (T * X + X * U)) + realMatrixNuclearNorm F := realMatrixNuclearNorm_add_le _ _
      _ = β * realMatrixNuclearNorm (T * X + X * U) + realMatrixNuclearNorm F := by
        rw [realMatrixNuclearNorm_smul, abs_of_pos hβ]
      _ ≤ β * (realMatrixNuclearNorm (T * X) + realMatrixNuclearNorm (X * U)) + realMatrixNuclearNorm F :=
        add_le_add (mul_le_mul_of_nonneg_left (realMatrixNuclearNorm_add_le _ _) hβ.le) le_rfl
      _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left hprod hβ.le) le_rfl
  have hcoeff : β * ((1 - a / β) * realMatrixNuclearNorm X + realMatrixNuclearNorm X * (1 - b / β)) =
      (2 * β - (a + b)) * realMatrixNuclearNorm X := by
    field_simp
    ring
  rw [hcoeff] at hnorm
  apply (le_div_iff₀ (add_pos ha hb)).2
  nlinarith

/-- Hermitian spectral intervals supply the two normalized contractions. No
rank or nonempty-dimension assumption is required. -/
theorem norm_le_of_spectral_intervals {m n : ℕ}
    (A : Matrix (Fin m) (Fin m) ℝ) (B : Matrix (Fin n) (Fin n) ℝ)
    (X F : Matrix (Fin m) (Fin n) ℝ) (a b β : ℝ)
    (hAh : A.IsHermitian) (hBh : B.IsHermitian)
    (ha : 0 < a) (hb : 0 < b) (hβ : 0 < β) (haβ : a ≤ β) (hbβ : b ≤ β)
    (hAspec : spectrum ℝ A ⊆ Set.Icc a β) (hBspec : spectrum ℝ B ⊆ Set.Icc b β)
    (hXF : A * X + X * B = F) :
    realMatrixNuclearNorm X ≤ realMatrixNuclearNorm F / (a + b) := by
  apply norm_le_of_contractions A B X F a b β ha hb hβ
  · exact norm_normalized_le A hAh hβ haβ hAspec
  · exact norm_normalized_le B hBh hβ hbβ hBspec
  · exact hXF

/-- Positive spectral floors alone suffice: a common finite normalization bound is
chosen from the two actual operator norms, with no nonempty-dimension premise. -/
theorem norm_le_of_spectral_floors {m n : ℕ}
    (A : Matrix (Fin m) (Fin m) ℝ) (B : Matrix (Fin n) (Fin n) ℝ)
    (X F : Matrix (Fin m) (Fin n) ℝ) (a b : ℝ)
    (hAh : A.IsHermitian) (hBh : B.IsHermitian) (ha : 0<a) (hb : 0<b)
    (hAspec : spectrum ℝ A ⊆ Set.Ici a) (hBspec : spectrum ℝ B ⊆ Set.Ici b)
    (hXF : A*X+X*B=F) : realMatrixNuclearNorm X ≤ realMatrixNuclearNorm F/(a+b) := by
  let cA := ‖A‖*‖(1 : Matrix (Fin m) (Fin m) ℝ)‖
  let cB := ‖B‖*‖(1 : Matrix (Fin n) (Fin n) ℝ)‖
  let β := a+b+cA+cB+1
  have hcA : 0≤cA := mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have hcB : 0≤cB := mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have hβ : 0<β := by dsimp [β]; linarith
  apply norm_le_of_spectral_intervals A B X F a b β hAh hBh ha hb hβ
    (by dsimp [β]; linarith) (by dsimp [β]; linarith) _ _ hXF
  · intro t ht
    have hn : |t|≤cA := spectrum.norm_le_norm_mul_of_mem ht
    exact ⟨hAspec ht, (le_abs_self t).trans (hn.trans (by dsimp [β]; linarith))⟩
  · intro t ht
    have hn : |t|≤cB := spectrum.norm_le_norm_mul_of_mem ht
    exact ⟨hBspec ht, (le_abs_self t).trans (hn.trans (by dsimp [β]; linarith))⟩

/-- Positive diagonal Sylvester bound from entry floors only. A common finite
normalization scale is chosen internally above both diagonal maxima, even when
one or both index groups are empty. -/
theorem diagonal_norm_le {m n : ℕ}
    (dA : Fin m → ℝ) (dB : Fin n → ℝ)
    (X F : Matrix (Fin m) (Fin n) ℝ) (a b : ℝ)
    (ha : 0 < a) (hb : 0 < b)
    (hA : ∀ i, a ≤ dA i) (hB : ∀ j, b ≤ dB j)
    (hXF : diagonal dA * X + X * diagonal dB = F) :
    realMatrixNuclearNorm X ≤ realMatrixNuclearNorm F / (a + b) := by
  let sA := ∑ i, |dA i|
  let sB := ∑ j, |dB j|
  let β := a + b + sA + sB + 1
  have hsA : 0 ≤ sA := Finset.sum_nonneg (fun i _ => abs_nonneg (dA i))
  have hsB : 0 ≤ sB := Finset.sum_nonneg (fun j _ => abs_nonneg (dB j))
  have hβ : 0 < β := by dsimp [β]; linarith
  have haβ : a ≤ β := by dsimp [β]; linarith
  have hbβ : b ≤ β := by dsimp [β]; linarith
  have hAβ (i : Fin m) : dA i ≤ β := by
    have hi : |dA i| ≤ sA := Finset.single_le_sum
      (fun j _ => abs_nonneg (dA j)) (Finset.mem_univ i)
    have hi' := le_abs_self (dA i)
    dsimp [β]
    linarith
  have hBβ (i : Fin n) : dB i ≤ β := by
    have hi : |dB i| ≤ sB := Finset.single_le_sum
      (fun j _ => abs_nonneg (dB j)) (Finset.mem_univ i)
    have hi' := le_abs_self (dB i)
    dsimp [β]
    linarith
  have hAspec : spectrum ℝ (diagonal dA) ⊆ Set.Icc a β := by
    intro t ht
    rw [spectrum_diagonal] at ht
    obtain ⟨i, rfl⟩ := ht
    exact ⟨hA i, hAβ i⟩
  have hBspec : spectrum ℝ (diagonal dB) ⊆ Set.Icc b β := by
    intro t ht
    rw [spectrum_diagonal] at ht
    obtain ⟨i, rfl⟩ := ht
    exact ⟨hB i, hBβ i⟩
  exact norm_le_of_spectral_intervals (diagonal dA) (diagonal dB) X F a b β
    (Matrix.isHermitian_diagonal _) (Matrix.isHermitian_diagonal _)
    ha hb hβ haβ hbβ hAspec hBspec hXF

/-- Separated diagonal Sylvester bound. Only the supplied uniform gap is used;
there is no sign, rank, distinctness or nonempty-group assumption. -/
theorem separated_diagonal_norm_le {m n : ℕ}
    (dA : Fin m → ℝ) (dB : Fin n → ℝ)
    (X F : Matrix (Fin m) (Fin n) ℝ) (a b gap : ℝ)
    (hgap : 0 < gap) (hsep : gap ≤ a - b)
    (hA : ∀ i, a ≤ dA i) (hB : ∀ j, dB j ≤ b)
    (hXF : diagonal dA * X - X * diagonal dB = F) :
    realMatrixNuclearNorm X ≤ realMatrixNuclearNorm F / gap := by
  let c := (a + b) / 2
  let dA' := fun i => dA i - c
  let dB' := fun j => c - dB j
  have hfloor : 0 < gap / 2 := by positivity
  have hA' (i : Fin m) : gap / 2 ≤ dA' i := by
    have hi := hA i
    dsimp [dA', c]
    linarith
  have hB' (j : Fin n) : gap / 2 ≤ dB' j := by
    have hj := hB j
    dsimp [dB', c]
    linarith
  have hXF' : diagonal dA' * X + X * diagonal dB' = F := by
    ext i j
    have hij := congrFun (congrFun hXF i) j
    simp only [Matrix.sub_apply, Matrix.diagonal_mul, Matrix.mul_diagonal] at hij
    simp only [Matrix.add_apply, Matrix.diagonal_mul, Matrix.mul_diagonal]
    dsimp only [dA', dB']
    nlinarith
  have h := diagonal_norm_le dA' dB' X F (gap / 2) (gap / 2) hfloor hfloor hA' hB' hXF'
  simpa only [add_halves] using h

end NumStability.PositiveSylvesterNuclear
