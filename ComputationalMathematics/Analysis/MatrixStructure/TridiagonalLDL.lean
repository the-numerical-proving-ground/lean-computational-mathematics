import ComputationalMathematics.Algorithms.LU.TridiagonalRecurrence
import ComputationalMathematics.Analysis.MatrixStructure.SymmetricTridiagonal

/-!
# Exact tridiagonal LDL factorization from nonzero pivots

The lower factor is constructed from the witnessed off-diagonals divided by the
preceding pivot. Its determinant is one. All algebraic results include
empty and singleton matrices and require no positive-definiteness or gap.
-/

namespace NumStability

open scoped BigOperators Matrix
noncomputable section

/-- A symmetric tridiagonal with lower-band entries `s i` at rows `i > 0`.
The unused entry `s 0` has no effect on the represented matrix. -/
def symmetricTridiagData {m : ℕ} (a s : Fin m → ℝ) : TridiagData m where
  a := s
  d := a
  c := fun i => if hi : i.val + 1 < m then s ⟨i.val + 1, hi⟩ else 0

/-- The preceding lower entry divided by its nonzero stored pivot. -/
def tridiagonalLDLMultipliers {m : ℕ} (s d : Fin m → ℝ) : Fin m → ℝ :=
  fun i => if hi : 0 < i.val then s i / d (tridiag_prevIndex i hi) else 0

/-- Explicit unit lower-bidiagonal exact factor. -/
def tridiagonalLDLLower {m : ℕ} (s d : Fin m → ℝ) : Matrix (Fin m) (Fin m) ℝ :=
  tridiag_L_matrix (tridiagonalLDLMultipliers s d)

/-- The constructed factor has unit diagonal. -/
theorem tridiagonalLDLLower_diagonal {m : ℕ} (s d : Fin m → ℝ) (i : Fin m) :
    tridiagonalLDLLower s d i i = 1 :=
  tridiag_L_diag (tridiagonalLDLMultipliers s d) i

/-- The constructed factor vanishes strictly above its diagonal. -/
theorem tridiagonalLDLLower_upper_zero {m : ℕ} (s d : Fin m → ℝ)
    (i j : Fin m) (hij : i.val < j.val) : tridiagonalLDLLower s d i j = 0 :=
  tridiag_L_upper_zero (tridiagonalLDLMultipliers s d) i j hij

/-- The only possible subdiagonal lies immediately below the diagonal. -/
theorem tridiagonalLDLLower_lower_zero {m : ℕ} (s d : Fin m → ℝ)
    (i j : Fin m) (hij : j.val + 1 < i.val) : tridiagonalLDLLower s d i j = 0 :=
  tridiag_L_lower_bidiag (tridiagonalLDLMultipliers s d) i j hij

/-- The actual subdiagonal entry uses the preceding pivot. -/
theorem tridiagonalLDLLower_subdiagonal {m : ℕ} (s d : Fin m → ℝ)
    (i : Fin m) (hi : 0 < i.val) :
    tridiagonalLDLLower s d i (tridiag_prevIndex i hi) = s i / d (tridiag_prevIndex i hi) := by
  have hv : (tridiag_prevIndex i hi).val + 1 = i.val := by
    simp only [tridiag_prevIndex, Fin.val_mk]
    omega
  have hne : (tridiag_prevIndex i hi).val ≠ i.val := by omega
  simp [tridiagonalLDLLower, tridiag_L_matrix, hne, hv,
    tridiagonalLDLMultipliers, hi]

private theorem symmetricTridiagData_prev_super {m : ℕ} (a s : Fin m → ℝ)
    (i : Fin m) (hi : 0 < i.val) :
    (symmetricTridiagData a s).c (tridiag_prevIndex i hi) = s i := by
  have hv : (tridiag_prevIndex i hi).val + 1 = i.val := by
    simp only [tridiag_prevIndex, Fin.val_mk]
    omega
  have hb : (tridiag_prevIndex i hi).val + 1 < m := by rw [hv]; exact i.isLt
  simp only [symmetricTridiagData, dif_pos hb]
  congr 1
  exact Fin.ext hv

/-- The exact scalar recurrence supplies the full tridiagonal matrix product;
no LU product identity is assumed. -/
theorem symmetricTridiagData_exactLU {m : ℕ} (a s d : Fin m → ℝ)
    (hd : ∀ i, d i ≠ 0)
    (hfirst : ∀ i, i.val = 0 → d i = a i)
    (hrec : ∀ i, ∀ hi : 0 < i.val,
      d i = a i - (s i) ^ 2 / d (tridiag_prevIndex i hi)) :
    tridiagonalLDLLower s d *
      Matrix.of (tridiag_U_matrix d (symmetricTridiagData a s).c) =
        Matrix.of (tridiag_to_matrix (symmetricTridiagData a s)) := by
  have hLU : TridiagExactLURecurrence (symmetricTridiagData a s)
      (tridiagonalLDLMultipliers s d) d := by
    refine ⟨hfirst, ?_, ?_⟩
    · intro i hi
      simp only [tridiagonalLDLMultipliers, dif_pos hi, symmetricTridiagData]
      exact div_mul_cancel₀ (s i) (hd _)
    · intro i hi
      rw [symmetricTridiagData_prev_super a s i hi]
      simp only [tridiagonalLDLMultipliers, dif_pos hi, symmetricTridiagData]
      rw [hrec i hi]
      ring
  ext i j
  exact tridiag_exact_product_of_recurrence (symmetricTridiagData a s)
    (tridiagonalLDLMultipliers s d) d hLU i j

/-- Symmetry of the bands identifies the computed upper factor with `D Lᵀ`. -/
theorem symmetricTridiagData_upper_eq_diagonal_mul_transpose {m : ℕ}
    (a s d : Fin m → ℝ) (hd : ∀ i, d i ≠ 0) :
    Matrix.of (tridiag_U_matrix d (symmetricTridiagData a s).c) =
      Matrix.diagonal d * (tridiagonalLDLLower s d).transpose := by
  ext i j
  rw [Matrix.diagonal_mul]
  simp only [Matrix.of_apply, tridiag_U_matrix, Matrix.transpose_apply, tridiagonalLDLLower,
    tridiag_L_matrix]
  by_cases hdiag : j.val = i.val
  · have hji : j = i := Fin.ext hdiag
    subst j
    simp
  · have hne : i.val ≠ j.val := Ne.symm hdiag
    by_cases hadj : i.val + 1 = j.val
    · have hjpos : 0 < j.val := by omega
      have hprev : tridiag_prevIndex j hjpos = i := by
        apply Fin.ext
        simp only [tridiag_prevIndex, Fin.val_mk]
        omega
      have hib : i.val + 1 < m := by rw [hadj]; exact j.isLt
      have hsucc : (⟨i.val + 1, hib⟩ : Fin m) = j := Fin.ext hadj
      simp only [if_neg hdiag, if_pos hadj, if_neg hne, tridiagonalLDLMultipliers,
        dif_pos hjpos, hprev, symmetricTridiagData, dif_pos hib, hsucc]
      exact (mul_div_cancel₀ (s j) (hd i)).symm
    · simp [hdiag, hne, hadj]

/-- Full exact LDLᵀ factorization derived from the scalar recurrence. -/
theorem symmetricTridiagData_ldl {m : ℕ} (a s d : Fin m → ℝ)
    (hd : ∀ i, d i ≠ 0)
    (hfirst : ∀ i, i.val = 0 → d i = a i)
    (hrec : ∀ i, ∀ hi : 0 < i.val,
      d i = a i - (s i) ^ 2 / d (tridiag_prevIndex i hi)) :
    Matrix.of (tridiag_to_matrix (symmetricTridiagData a s)) =
      tridiagonalLDLLower s d * Matrix.diagonal d * (tridiagonalLDLLower s d).transpose := by
  rw [← symmetricTridiagData_exactLU a s d hd hfirst hrec,
    symmetricTridiagData_upper_eq_diagonal_mul_transpose a s d hd, Matrix.mul_assoc]

/-- Determinant one is derived from the explicit lower-bidiagonal entries,
including the empty product in dimension zero. -/
theorem tridiagonalLDLLower_det {m : ℕ} (s d : Fin m → ℝ) :
    (tridiagonalLDLLower s d).det = 1 := by
  rw [Matrix.det_of_lowerTriangular]
  · simp [tridiagonalLDLLower, tridiag_L_diag]
  · intro i j hij
    exact tridiag_L_upper_zero (tridiagonalLDLMultipliers s d) i j hij

/-- The explicit lower factor is a unit; invertibility is not an input. -/
theorem tridiagonalLDLLower_isUnit {m : ℕ} (s d : Fin m → ℝ) :
    IsUnit (tridiagonalLDLLower s d) := by
  apply (Matrix.isUnit_iff_isUnit_det _).mpr
  rw [tridiagonalLDLLower_det]
  exact isUnit_one

/-- The source-independent scalar tridiagonal builder agrees with the exact
edge-based matrix already used by the native backward witness. -/
theorem symmetricTridiagData_of_edges {n : ℕ} (a : Fin (n + 1) → ℝ) (s : Fin n → ℝ) :
    Matrix.of (tridiag_to_matrix (symmetricTridiagData a (Fin.cases 0 s))) =
      sturmTridiagonal a s := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp [tridiag_to_matrix, symmetricTridiagData, sturmTridiagonal_diagonal]
  · have hji : j.val ≠ i.val := by
      intro h
      exact hij (Fin.ext h.symm)
    by_cases hlo : j.val + 1 = i.val
    · let k : Fin n := ⟨j.val, by have hi := i.isLt; omega⟩
      have hki : k.succ = i := Fin.ext hlo
      have hkj : k.castSucc = j := Fin.ext rfl
      rw [← hki, ← hkj, sturmTridiagonal_lower]
      simp [tridiag_to_matrix, symmetricTridiagData, Matrix.of_apply]
    · by_cases hup : i.val + 1 = j.val
      · let k : Fin n := ⟨i.val, by have hj := j.isLt; omega⟩
        have hki : k.castSucc = i := Fin.ext rfl
        have hkj : k.succ = j := Fin.ext hup
        rw [← hki, ← hkj, sturmTridiagonal_upper]
        simp [tridiag_to_matrix, symmetricTridiagData, Matrix.of_apply,
          show ¬k.val + 1 + 1 = k.val by omega]
      · rw [sturmTridiagonal_support a s i j hij hup hlo]
        simp [tridiag_to_matrix, symmetricTridiagData, hji, hlo, hup]

/-- Exact shifted elimination equations for specified diagonal and edges. -/
def IsSturmBackwardRecurrence {n : ℕ} (d a : Fin (n + 1) → ℝ)
    (b : Fin n → ℝ) (x : ℝ) : Prop :=
  d 0 = a 0 - x ∧
    ∀ i : Fin n, d i.succ = a i.succ - x - (b i) ^ 2 / d i.castSucc

/-- The exact scalar recurrence gives the shifted tridiagonal LDLᵀ factorization. -/
theorem sturmBackwardRecurrence_ldl {n : ℕ} (d e : Fin (n + 1) → ℝ)
    (s : Fin n → ℝ) (x : ℝ) (hd : ∀ i, d i ≠ 0)
    (hrec : IsSturmBackwardRecurrence d e s x) :
    sturmTridiagonal e s - x • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) =
      tridiagonalLDLLower (Fin.cases 0 s) d * Matrix.diagonal d *
        (tridiagonalLDLLower (Fin.cases 0 s) d).transpose := by
  let a : Fin (n + 1) → ℝ := fun i => e i - x
  let lower : Fin (n + 1) → ℝ := Fin.cases 0 s
  have hfirst : ∀ i : Fin (n + 1), i.val = 0 → d i = a i := by
    intro i hi
    have hi0 : i = 0 := Fin.ext hi
    subst i
    have h := hrec.1
    dsimp [a]
    linarith
  have hsteps : ∀ i : Fin (n + 1), ∀ hi : 0 < i.val,
      d i = a i - (lower i) ^ 2 / d (tridiag_prevIndex i hi) := by
    intro i hi
    let k : Fin n := ⟨i.val - 1, by have hi' := i.isLt; omega⟩
    have hprev : tridiag_prevIndex i hi = k.castSucc := Fin.ext rfl
    have hki : i = k.succ := by
      apply Fin.ext
      simp only [Fin.val_succ]
      dsimp [k]
      omega
    have h := hrec.2 k
    dsimp [a, lower]
    rw [hprev, hki, Fin.cases_succ]
    linarith
  have hfact := symmetricTridiagData_ldl a lower d hd hfirst hsteps
  rw [symmetricTridiagData_of_edges a s] at hfact
  have hconst : sturmTridiagonal (fun _ : Fin (n + 1) => x) 0 =
      x • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) := by
    ext i j
    by_cases hij : i = j <;> simp [sturmTridiagonal, hij]
  have hshift : sturmTridiagonal a s =
      sturmTridiagonal e s - x • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) := by
    apply (eq_sub_iff_add_eq).mpr
    rw [← hconst, ← sturmTridiagonal_add]
    congr 1
    · funext i
      dsimp [a]
      ring
    · funext i
      simp
  rw [hshift] at hfact
  exact hfact

end
end NumStability
