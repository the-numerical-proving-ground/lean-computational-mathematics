import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp

/-!
# Dimension-free positive and separated Sylvester bounds

Normalized contractions give a finite algebraic norm estimate, with no
Frobenius factor or integral construction. Rectangular unknowns and empty
index groups are included. Separated real diagonals reduce to the positive
case by a common midpoint shift.
-/

open Matrix
open scoped BigOperators Matrix.Norms.L2Operator

namespace NumStability.PositiveSylvesterBound

/-- A finite contraction proof of the positive Sylvester bound. Both square
coefficient matrices share a normalization scale; the unknown is rectangular. -/
private theorem norm_le_of_contractions {m n : ℕ}
    (A : Matrix (Fin m) (Fin m) ℝ) (B : Matrix (Fin n) (Fin n) ℝ)
    (X F : Matrix (Fin m) (Fin n) ℝ) (a b β : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hβ : 0 < β)
    (hA : ‖1 - β⁻¹ • A‖ ≤ 1 - a / β)
    (hB : ‖1 - β⁻¹ • B‖ ≤ 1 - b / β)
    (hXF : A * X + X * B = F) :
    ‖X‖ ≤ ‖F‖ / (a + b) := by
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
  have hprod : ‖T * X‖ + ‖X * U‖ ≤
      (1 - a / β) * ‖X‖ + ‖X‖ * (1 - b / β) := by
    exact add_le_add ((Matrix.l2_opNorm_mul T X).trans
      (mul_le_mul_of_nonneg_right hT (norm_nonneg X)))
      ((Matrix.l2_opNorm_mul X U).trans
      (mul_le_mul_of_nonneg_left hU (norm_nonneg X)))
  have hnorm : (2 * β) * ‖X‖ ≤
      β * ((1 - a / β) * ‖X‖ + ‖X‖ * (1 - b / β)) + ‖F‖ := by
    calc
      _ = ‖(2 * β) • X‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (mul_pos (by norm_num) hβ)]
      _ = ‖β • (T * X + X * U) + F‖ := by rw [hid]
      _ ≤ ‖β • (T * X + X * U)‖ + ‖F‖ := norm_add_le _ _
      _ = β * ‖T * X + X * U‖ + ‖F‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos hβ]
      _ ≤ β * (‖T * X‖ + ‖X * U‖) + ‖F‖ :=
        add_le_add (mul_le_mul_of_nonneg_left (norm_add_le _ _) hβ.le) le_rfl
      _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left hprod hβ.le) le_rfl
  have hcoeff : β * ((1 - a / β) * ‖X‖ + ‖X‖ * (1 - b / β)) =
      (2 * β - (a + b)) * ‖X‖ := by
    field_simp
    ring
  rw [hcoeff] at hnorm
  apply (le_div_iff₀ (add_pos ha hb)).2
  nlinarith

private theorem diagonal_contraction {n : ℕ} (d : Fin n → ℝ) {a β : ℝ}
    (hβ : 0 < β) (haβ : a ≤ β) (hdlo : ∀ i, a ≤ d i) (hdhi : ∀ i, d i ≤ β) :
    ‖1 - β⁻¹ • diagonal d‖ ≤ 1 - a / β := by
  rw [← Matrix.diagonal_one, ← Matrix.diagonal_smul, Matrix.diagonal_sub,
    Matrix.l2_opNorm_diagonal]
  have hn : 0 ≤ 1 - a / β := sub_nonneg.mpr ((div_le_one hβ).2 haβ)
  apply (pi_norm_le_iff_of_nonneg hn).2
  intro i
  change ‖1 - β⁻¹ * d i‖ ≤ 1 - a / β
  have h : 0 ≤ 1 - β⁻¹ * d i := by
    rw [mul_comm, ← div_eq_mul_inv]
    exact sub_nonneg.mpr ((div_le_one hβ).2 (hdhi i))
  rw [Real.norm_eq_abs, abs_of_nonneg h, mul_comm, ← div_eq_mul_inv]
  exact sub_le_sub_left (div_le_div_of_nonneg_right (hdlo i) hβ.le) 1

/-- Positive diagonal Sylvester bound from entry floors only. A common finite
normalization scale is chosen internally above both diagonal maxima, even when
one or both index groups are empty. -/
theorem diagonal_norm_le {m n : ℕ}
    (dA : Fin m → ℝ) (dB : Fin n → ℝ)
    (X F : Matrix (Fin m) (Fin n) ℝ) (a b : ℝ)
    (ha : 0 < a) (hb : 0 < b)
    (hA : ∀ i, a ≤ dA i) (hB : ∀ j, b ≤ dB j)
    (hXF : diagonal dA * X + X * diagonal dB = F) :
    ‖X‖ ≤ ‖F‖ / (a + b) := by
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
  apply norm_le_of_contractions (diagonal dA) (diagonal dB) X F a b β ha hb hβ
  · exact diagonal_contraction dA hβ haβ hA hAβ
  · exact diagonal_contraction dB hβ hbβ hB hBβ
  · exact hXF

/-- Separated diagonal Sylvester bound. Only the supplied uniform gap is used;
there is no sign, rank, distinctness or nonempty-group assumption. -/
theorem separated_diagonal_norm_le {m n : ℕ}
    (dA : Fin m → ℝ) (dB : Fin n → ℝ)
    (X F : Matrix (Fin m) (Fin n) ℝ) (a b gap : ℝ)
    (hgap : 0 < gap) (hsep : gap ≤ a - b)
    (hA : ∀ i, a ≤ dA i) (hB : ∀ j, dB j ≤ b)
    (hXF : diagonal dA * X - X * diagonal dB = F) :
    ‖X‖ ≤ ‖F‖ / gap := by
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

end NumStability.PositiveSylvesterBound
