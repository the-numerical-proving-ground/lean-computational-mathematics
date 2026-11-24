import ComputationalMathematics.Source.CertifiedTridiagonalEigenpairs.RoundedVectorLocal.Proof

namespace NumStability.CertifiedTridiagonalEigenpairs

open FloatingPointFormat.UnboundedBinary

/-- The rounded left sweep on zero-based row indices. The diagonal function
supplies the exact shifted entry before its first rounding. -/
noncomputable def vectorLeftSweep (p : ℕ) (hp : 2 ≤ p) (a b : ℕ → ℝ) (η : ℝ) :
    ℕ → ℝ × ℝ
  | 0 => (roundToEven p hp (a 0), η)
  | i + 1 =>
    let d := vectorLeftSweep p hp a b η i
    vectorPivotStep p hp (roundToEven p hp (a (i + 1))) η (b i) d.1 d.2

/-- The same calculation on the reversed entries, with results read off in the
original row order. Only indices less than n represent rows. -/
noncomputable def vectorRightSweep (p : ℕ) (hp : 2 ≤ p) (n : ℕ) (a b : ℕ → ℝ)
    (η : ℝ) (i : ℕ) : ℝ × ℝ :=
  vectorLeftSweep p hp (fun j => a (n - 1 - j)) (fun j => b (n - 2 - j)) η (n - 1 - i)

/-- The source twist on row r, with a zero edge and harmless dummy pivot for
each absent correction at an endpoint. -/
noncomputable def vectorSweepTwist (p : ℕ) (hp : 2 ≤ p) (n : ℕ) (a b : ℕ → ℝ)
    (η : ℝ) (r : Fin n) : ℝ × ℝ :=
  let left := if 0 < r.val then vectorLeftSweep p hp a b η (r.val - 1) else (0, η)
  let right := if r.val + 1 < n then vectorRightSweep p hp n a b η (r.val + 1) else (0, η)
  let bL := if 0 < r.val then b (r.val - 1) else 0
  let bR := if r.val + 1 < n then b r.val else 0
  vectorTwist p hp (roundToEven p hp (a r.val)) η bL left.1 left.2 bR right.1 right.2

/-- Magnitude and positive-imaginary-component bounds on a directional pivot. -/
def VectorPivotBounds (η : ℝ) (d : ℝ × ℝ) : Prop :=
  |d.1| ≤ 4 / η ∧ η ≤ d.2 ∧ d.2 ≤ 2 / η ∧ ‖(⟨d.1, -d.2⟩ : ℂ)‖ ≤ 8 / η

theorem vectorLeftSweep_bounds
    (p : ℕ) (hp : 2 ≤ p) (n : ℕ) (a b : ℕ → ℝ) (η : ℝ)
    (hω : unitRoundoff p ≤ 1 / 128) (hη₀ : 0 < η) (hη₁ : η ≤ 1 / 2) (hNative : Native p hp η)
    (ha : ∀ i < n, |a i| ≤ 5) (hb : ∀ i, i + 1 < n → |b i| ≤ 1)
    (i : ℕ) (hi : i < n) : VectorPivotBounds η (vectorLeftSweep p hp a b η i) := by
  induction i with
  | zero =>
    obtain ⟨hx, hy, hd⟩ := rounded_vector_initial_pivot_bounds p hp hω (a 0) η (ha 0 hi) hη₀ hη₁
    exact ⟨hx, le_rfl, hy, hd⟩
  | succ i ih =>
    let d := vectorLeftSweep p hp a b η i
    exact rounded_vector_pivot_step_bounds p hp hω (a (i + 1)) η (b i) d.1 d.2 (ha _ hi)
      (hb _ hi) hη₀ hη₁ hNative (ih (by omega)).2.1

theorem vectorRightSweep_bounds
    (p : ℕ) (hp : 2 ≤ p) (n : ℕ) (a b : ℕ → ℝ) (η : ℝ)
    (hω : unitRoundoff p ≤ 1 / 128) (hη₀ : 0 < η) (hη₁ : η ≤ 1 / 2) (hNative : Native p hp η)
    (ha : ∀ i < n, |a i| ≤ 5) (hb : ∀ i, i + 1 < n → |b i| ≤ 1)
    (i : ℕ) (hi : i < n) : VectorPivotBounds η (vectorRightSweep p hp n a b η i) := by
  apply vectorLeftSweep_bounds p hp n _ _ η hω hη₀ hη₁ hNative
  · intro j hj
    exact ha _ (by omega)
  · intro j hj
    exact hb _ (by omega)
  · omega

theorem vectorRightSweep_step
    (p : ℕ) (hp : 2 ≤ p) (n : ℕ) (a b : ℕ → ℝ) (η : ℝ) (i : ℕ) (hi : i + 1 < n) :
    let d := vectorRightSweep p hp n a b η (i + 1)
    vectorRightSweep p hp n a b η i = vectorPivotStep p hp (roundToEven p hp (a i)) η (b i) d.1 d.2 := by
  dsimp only [vectorRightSweep]
  rw [show n - 1 - i = (n - 1 - (i + 1)) + 1 by omega, vectorLeftSweep]
  rw [show n - 1 - (n - 1 - (i + 1) + 1) = i by omega,
    show n - 2 - (n - 1 - (i + 1)) = i by omega]

theorem vectorRightSweep_initial
    (p : ℕ) (hp : 2 ≤ p) (n : ℕ) (a b : ℕ → ℝ) (η : ℝ) (i : ℕ) (hi : i + 1 = n) :
    vectorRightSweep p hp n a b η i = (roundToEven p hp (a i), η) := by
  unfold vectorRightSweep
  rw [show n - 1 - i = 0 by omega, vectorLeftSweep, show n - 1 - 0 = i by omega]

theorem vectorSweepTwist_im_lower
    (p : ℕ) (hp : 2 ≤ p) (n : ℕ) (a b : ℕ → ℝ) (η : ℝ)
    (hω : unitRoundoff p ≤ 1 / 128) (hη₀ : 0 < η) (hη₁ : η ≤ 1 / 2) (hNative : Native p hp η)
    (ha : ∀ i < n, |a i| ≤ 5) (hb : ∀ i, i + 1 < n → |b i| ≤ 1)
    (r : Fin n) : η ≤ (vectorSweepTwist p hp n a b η r).2 := by
  unfold vectorSweepTwist
  apply vectorTwist_im_lower p hp hω _ _ _ _ _ _ _ _ hNative
  · split_ifs with hl
    · exact hη₀.trans_le
        (vectorLeftSweep_bounds p hp n a b η hω hη₀ hη₁ hNative ha hb _ (by omega)).2.1
    · exact hη₀
  · split_ifs with hr
    · exact hη₀.trans_le
        (vectorRightSweep_bounds p hp n a b η hω hη₀ hη₁ hNative ha hb _ hr).2.1
    · exact hη₀

end NumStability.CertifiedTridiagonalEigenpairs
