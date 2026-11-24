import ComputationalMathematics.Source.CertifiedTridiagonalEigenpairs.RoundedVectorLocal.Target
import ComputationalMathematics.Analysis.MatrixStructure.ComplexTridiagonalNorm

namespace NumStability.CertifiedTridiagonalEigenpairs

open scoped Matrix Matrix.Norms.L2Operator
open FloatingPointFormat.UnboundedBinary

private def VectorEdgeBound (ω b : ℝ) (β : ℂ) : Prop :=
  (b = 0 → β = 0) ∧ (b ≠ 0 → ‖β / (b : ℂ) - 1‖ ≤ 11 * ω)

private theorem vector_initial_diag_bound (q : ℕ) (hq : 2 ≤ q) (a η : ℝ) (ha : |a| ≤ 5) :
    ‖vectorComplexPivot (roundToEven q hq a, η) - ⟨a, -η⟩‖ ≤ 17 * unitRoundoff q := by
  have he : vectorComplexPivot (roundToEven q hq a, η) - ⟨a, -η⟩ =
      ((roundToEven q hq a - a : ℝ) : ℂ) := by
    apply Complex.ext <;>
      simp only [vectorComplexPivot, Complex.sub_re, Complex.sub_im, Complex.ofReal_re,
        Complex.ofReal_im, sub_self]
  rw [he, Complex.norm_real, Real.norm_eq_abs]
  calc
    _ ≤ unitRoundoff q * 5 := abs_roundToEven_sub_le_of_abs_le q hq a 5 ha
    _ ≤ _ := by linarith [unitRoundoff_pos q]

private theorem vector_row_witness
    (n q : ℕ) (hq : 2 ≤ q) (a b : ℕ → ℝ) (η : ℝ)
    (hω : unitRoundoff q ≤ 1 / 128) (hη₀ : 0 < η) (hη₁ : η ≤ 1 / 2) (hNative : Native q hq η)
    (ha : ∀ i < n, |a i| ≤ 5) (hb : ∀ i, i + 1 < n → |b i| ≤ 1) (r i : Fin n) :
    let d := vectorAssemblyPivot q hq n a b η r i
    let left := vectorComplexPivot (vectorLeftSweep q hq a b η (i.val - 1))
    let right := vectorComplexPivot (vectorRightSweep q hq n a b η (i.val + 1))
    ∃ D l u : ℂ, D = d + (l ^ 2 / left + u ^ 2 / right) ∧
      ‖D - ⟨a i.val, -η⟩‖ ≤ 17 * unitRoundoff q ∧
      VectorEdgeBound (unitRoundoff q) (if 0 < i.val ∧ i.val ≤ r.val then b (i.val - 1) else 0) l ∧
      VectorEdgeBound (unitRoundoff q) (if i.val + 1 < n ∧ r.val ≤ i.val then b i.val else 0) u := by
  dsimp only
  by_cases hl : i.val < r.val
  · have hnr : ¬ (i.val + 1 < n ∧ r.val ≤ i.val) := by omega
    rw [if_neg hnr]
    simp only [vectorAssemblyPivot, if_pos hl]
    by_cases hii : 0 < i.val
    · have hl' : 0 < i.val ∧ i.val ≤ r.val := ⟨hii, hl.le⟩
      rw [if_pos hl']
      let left := vectorLeftSweep q hq a b η (i.val - 1)
      have hstep : vectorLeftSweep q hq a b η i.val =
          vectorPivotStep q hq (roundToEven q hq (a i.val)) η (b (i.val - 1)) left.1 left.2 := by
        conv_lhs => rw [show i.val = (i.val - 1) + 1 by omega]
        rw [vectorLeftSweep, show i.val - 1 + 1 = i.val by omega]
      have hyl : 0 < left.2 := hη₀.trans_le
        (vectorLeftSweep_bounds q hq n a b η hω hη₀ hη₁ hNative ha hb _ (by have := i.isLt; omega)).2.1
      obtain ⟨D, β, he, hD, hβ₀, hβ⟩ :=
        rounded_vector_pivot_step_backward q hq hω (a i.val) η (b (i.val - 1)) left.1 left.2
          (ha _ i.isLt) hη₀.le hη₁ hyl
      refine ⟨D, β, 0, ?_, hD.trans ?_, ⟨hβ₀, hβ⟩, ?_⟩
      · rw [hstep, zero_pow (by decide : 2 ≠ 0), zero_div, add_zero]
        change vectorComplexPivot (vectorPivotStep _ _ _ _ _ _ _) =
          D - β ^ 2 / vectorComplexPivot left at he
        linear_combination -he
      · linarith [unitRoundoff_pos q]
      · simp [VectorEdgeBound]
    · have hl' : ¬ (0 < i.val ∧ i.val ≤ r.val) := fun h => hii h.1
      have hi₀ : i.val = 0 := by omega
      rw [if_neg hl', hi₀, vectorLeftSweep]
      refine ⟨vectorComplexPivot (roundToEven q hq (a 0), η), 0, 0, by simp,
        vector_initial_diag_bound q hq (a 0) η (ha _ (by have := i.isLt; omega)), ?_, ?_⟩
      all_goals simp [VectorEdgeBound]
  · by_cases hr : r.val < i.val
    · have hnl : ¬ (0 < i.val ∧ i.val ≤ r.val) := by omega
      rw [if_neg hnl]
      simp only [vectorAssemblyPivot, if_neg hl, if_pos hr]
      by_cases hii : i.val + 1 < n
      · have hr' : i.val + 1 < n ∧ r.val ≤ i.val := ⟨hii, hr.le⟩
        rw [if_pos hr']
        let right := vectorRightSweep q hq n a b η (i.val + 1)
        have hstep := vectorRightSweep_step q hq n a b η i.val hii
        have hyr : 0 < right.2 := hη₀.trans_le
          (vectorRightSweep_bounds q hq n a b η hω hη₀ hη₁ hNative ha hb _ hii).2.1
        obtain ⟨D, β, he, hD, hβ₀, hβ⟩ :=
          rounded_vector_pivot_step_backward q hq hω (a i.val) η (b i.val) right.1 right.2
            (ha _ i.isLt) hη₀.le hη₁ hyr
        refine ⟨D, 0, β, ?_, hD.trans ?_, ?_, ⟨hβ₀, hβ⟩⟩
        · rw [hstep, zero_pow (by decide : 2 ≠ 0), zero_div, zero_add]
          change vectorComplexPivot (vectorPivotStep _ _ _ _ _ _ _) =
            D - β ^ 2 / vectorComplexPivot right at he
          linear_combination -he
        · linarith [unitRoundoff_pos q]
        · simp [VectorEdgeBound]
      · have hr' : ¬ (i.val + 1 < n ∧ r.val ≤ i.val) := fun h => hii h.1
        rw [if_neg hr', vectorRightSweep_initial q hq n a b η i.val (by have := i.isLt; omega)]
        refine ⟨vectorComplexPivot (roundToEven q hq (a i.val), η), 0, 0, by simp,
          vector_initial_diag_bound q hq (a i.val) η (ha _ i.isLt), ?_, ?_⟩
        all_goals simp [VectorEdgeBound]
    · have e : i = r := Fin.ext (by omega)
      subst i
      simp only [vectorAssemblyPivot, lt_irrefl, if_false, le_refl, and_true]
      let left := if 0 < r.val then vectorLeftSweep q hq a b η (r.val - 1) else (0, η)
      let right := if r.val + 1 < n then vectorRightSweep q hq n a b η (r.val + 1) else (0, η)
      let bL := if 0 < r.val then b (r.val - 1) else 0
      let bR := if r.val + 1 < n then b r.val else 0
      have hyl : 0 < left.2 := by
        dsimp only [left]
        split_ifs with h
        · exact hη₀.trans_le
            (vectorLeftSweep_bounds q hq n a b η hω hη₀ hη₁ hNative ha hb _
              (by have := r.isLt; omega)).2.1
        · exact hη₀
      have hyr : 0 < right.2 := by
        dsimp only [right]
        split_ifs with h
        · exact hη₀.trans_le (vectorRightSweep_bounds q hq n a b η hω hη₀ hη₁ hNative ha hb _ h).2.1
        · exact hη₀
      obtain ⟨D, l, u, he, hD, hl₀, hle, hu₀, hue⟩ :=
        rounded_vector_twist_backward q hq hω (a r.val) η bL left.1 left.2 bR right.1 right.2
          (ha _ r.isLt) hη₀.le hη₁ hyl hyr
      refine ⟨D, l, u, ?_, hD, ⟨hl₀, hle⟩, ⟨hu₀, hue⟩⟩
      change vectorComplexPivot (vectorSweepTwist q hq n a b η r) =
        D - l ^ 2 / vectorComplexPivot left - u ^ 2 / vectorComplexPivot right at he
      have el : l ^ 2 / vectorComplexPivot left =
          l ^ 2 / vectorComplexPivot (vectorLeftSweep q hq a b η (r.val - 1)) := by
        by_cases h : 0 < r.val
        · simp [left, h]
        · have hzero : l = 0 := hl₀ (by simp [bL, h])
          simp [hzero]
      have er : u ^ 2 / vectorComplexPivot right =
          u ^ 2 / vectorComplexPivot (vectorRightSweep q hq n a b η (r.val + 1)) := by
        by_cases h : r.val + 1 < n
        · simp [right, h]
        · have hzero : u = 0 := hu₀ (by simp [bR, h])
          simp [hzero]
      rw [el, er] at he
      linear_combination -he

private theorem vectorEdgeBound_norm_sub {ω b : ℝ} {β : ℂ} (hω : 0 ≤ ω)
    (hb : |b| ≤ 1) (h : VectorEdgeBound ω b β) : ‖β - (b : ℂ)‖ ≤ 11 * ω := by
  by_cases hb₀ : b = 0
  · have := h.1 hb₀
    simp [this, hb₀, hω]
  · have hc : (b : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hb₀
    rw [show β - (b : ℂ) = (β / (b : ℂ) - 1) * b by rw [sub_mul, div_mul_cancel₀ _ hc, one_mul],
      norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact (mul_le_mul_of_nonneg_right (h.2 hb₀) (abs_nonneg _)).trans
      (mul_le_of_le_one_right (by positivity) hb)

private theorem vector_shifted_band {n : ℕ} (a b : ℕ → ℝ) (η : ℝ) (i j : Fin n)
    (hij : i.val + 1 < j.val ∨ j.val + 1 < i.val) : vectorShiftedMatrix n a b η i j = 0 := by
  have hin : i ≠ j := by intro h; subst j; omega
  have hl : i.val + 1 ≠ j.val := by omega
  have hr : j.val + 1 ≠ i.val := by omega
  simp only [vectorShiftedMatrix, hin, hl, hr, if_false]

private theorem vector_shifted_edge {n : ℕ} (a b : ℕ → ℝ) (η : ℝ) (i j : Fin n)
    (hij : i.val + 1 = j.val) : vectorShiftedMatrix n a b η i j = (b i.val : ℂ) := by
  have hin : i ≠ j := by intro h; subst j; omega
  simp only [vectorShiftedMatrix, hin, hij, if_false, if_true]

private theorem vector_shifted_symm {n : ℕ} (a b : ℕ → ℝ) (η : ℝ) (i j : Fin n) :
    vectorShiftedMatrix n a b η i j = vectorShiftedMatrix n a b η j i := by
  by_cases he : i = j
  · subst j; rfl
  · by_cases hl : i.val + 1 = j.val
    · have hr : j.val + 1 ≠ i.val := by omega
      simp only [vectorShiftedMatrix, he, Ne.symm he, hl, hr, if_false, if_true]
    · by_cases hr : j.val + 1 = i.val
      · simp only [vectorShiftedMatrix, he, Ne.symm he, hl, hr, if_false, if_true]
      · simp only [vectorShiftedMatrix, he, Ne.symm he, hl, hr, if_false]

private theorem vector_assemble_row_witnesses
    {n q : ℕ} (hq : 2 ≤ q) (a b : ℕ → ℝ) (η : ℝ)
    (hω : unitRoundoff q ≤ 1 / 128) (hη₀ : 0 < η) (hη₁ : η ≤ 1 / 2) (hNative : Native q hq η)
    (ha : ∀ i < n, |a i| ≤ 5) (hb : ∀ i, i + 1 < n → |b i| ≤ 1) (r : Fin n) :
    let d := vectorAssemblyPivot q hq n a b η r
    ∃ D β : Fin n → ℂ,
      (∀ i, D i = d i + ∑ j, if j ≠ r ∧ vectorParent r j = i then β j ^ 2 / d j else 0) ∧
      (∀ i, ‖D i - ⟨a i.val, -η⟩‖ ≤ 17 * unitRoundoff q) ∧
      ∀ i j : Fin n, i.val + 1 = j.val →
        VectorEdgeBound (unitRoundoff q) (b i.val) (if i.val < r.val then β i else β j) := by
  let d := vectorAssemblyPivot q hq n a b η r
  have hwitness := vector_row_witness n q hq a b η hω hη₀ hη₁ hNative ha hb r
  dsimp only at hwitness
  choose D l u hD hDerr hl hu using hwitness
  let β (j : Fin n) := if j.val < r.val then l (vectorParent r j) else u (vectorParent r j)
  refine ⟨D, β, ?_, hDerr, ?_⟩
  · apply vector_rooted_diag_from_children r d D β
    intro i
    have hleft :
        (if h : 0 < i.val ∧ i.val ≤ r.val then (β ⟨i.val - 1, by omega⟩) ^ 2 /
            d ⟨i.val - 1, by omega⟩ else 0) =
        l i ^ 2 / vectorComplexPivot (vectorLeftSweep q hq a b η (i.val - 1)) := by
      by_cases hi : 0 < i.val ∧ i.val ≤ r.val
      · let j : Fin n := ⟨i.val - 1, by omega⟩
        have hji : j.val + 1 = i.val := by dsimp [j]; omega
        have hjr : j.val < r.val := by omega
        have hp : vectorParent r j = i := ((vectorParent_eq_iff r i j).2 (Or.inl ⟨hji, hjr⟩)).2
        rw [dif_pos hi]
        change β j ^ 2 / d j = _
        simp only [β, if_pos hjr, hp, d, vectorAssemblyPivot, j]
      · have hβ := hl i
        rw [if_neg hi] at hβ
        rw [dif_neg hi, hβ.1 rfl, zero_pow (by decide : 2 ≠ 0), zero_div]
    have hright :
        (if h : i.val + 1 < n ∧ r.val ≤ i.val then (β ⟨i.val + 1, h.1⟩) ^ 2 /
            d ⟨i.val + 1, h.1⟩ else 0) =
        u i ^ 2 / vectorComplexPivot (vectorRightSweep q hq n a b η (i.val + 1)) := by
      by_cases hi : i.val + 1 < n ∧ r.val ≤ i.val
      · let j : Fin n := ⟨i.val + 1, hi.1⟩
        have hjr : r.val < j.val := by dsimp [j]; omega
        have hjn : ¬ j.val < r.val := by omega
        have hp : vectorParent r j = i := ((vectorParent_eq_iff r i j).2 (Or.inr ⟨rfl, hjr⟩)).2
        rw [dif_pos hi]
        change β j ^ 2 / d j = _
        simp only [β, if_neg hjn, if_pos hjr, hp, d, vectorAssemblyPivot, j]
      · have hβ := hu i
        rw [if_neg hi] at hβ
        rw [dif_neg hi, hβ.1 rfl, zero_pow (by decide : 2 ≠ 0), zero_div]
    rw [hleft, hright]
    exact hD i
  · intro i j hij
    by_cases hi : i.val < r.val
    · have hp : vectorParent r i = j := ((vectorParent_eq_iff r j i).2 (Or.inl ⟨hij, hi⟩)).2
      have hj : 0 < j.val ∧ j.val ≤ r.val := by omega
      have he : j.val - 1 = i.val := by omega
      have hw := hl j
      rw [if_pos hj, he] at hw
      simpa only [β, if_pos hi, hp] using hw
    · have hj : r.val < j.val := by omega
      have hjn : ¬ j.val < r.val := by omega
      have hp : vectorParent r j = i := ((vectorParent_eq_iff r i j).2 (Or.inr ⟨hij, hj⟩)).2
      have hi' : i.val + 1 < n ∧ r.val ≤ i.val := by have := j.isLt; omega
      have hw := hu i
      rw [if_pos hi'] at hw
      simpa only [β, if_neg hi, if_neg hjn, hp] using hw

private theorem vector_rooted_parent_edge {n : ℕ} (r : Fin n) (β D : Fin n → ℂ) (j : Fin n)
    (hj : j ≠ r) : rootedSymmetricMatrix r (vectorParent r) β D (vectorParent r j) j = β j := by
  have hne := vectorParent_ne_self r j hj
  have hnil : ¬ (vectorParent r j ≠ r ∧ vectorParent r (vectorParent r j) = j) := by
    intro hbad
    have h₁ := vectorRootDistance_parent r j hj
    have h₂ := vectorRootDistance_parent r (vectorParent r j) hbad.1
    rw [hbad.2] at h₂
    omega
  rw [rootedSymmetricMatrix, if_neg hne, if_pos ⟨hj, rfl⟩, if_neg hnil, add_zero]

/-- The actual rounded sweeps and twist give the source structured backward
factorization at each candidate row. -/
theorem roundedVectorStructuredBackward : SourceTargets.roundedVectorStructuredBackward := by
  intro n q _ hq a b η hω hη₀ hη₁ hNative ha hb
  have hleft (i : Fin n) : VectorPivotBounds η (vectorLeftSweep q hq a b η i.val) :=
    vectorLeftSweep_bounds q hq n a b η hω hη₀ hη₁ hNative ha hb i.val i.isLt
  have hright (i : Fin n) : VectorPivotBounds η (vectorRightSweep q hq n a b η i.val) :=
    vectorRightSweep_bounds q hq n a b η hω hη₀ hη₁ hNative ha hb i.val i.isLt
  constructor
  · intro i
    exact ⟨hleft i, hright i, vectorSquaredModulus_pos q hq _ _ (hη₀.trans_le (hleft i).2.1),
      vectorSquaredModulus_pos q hq _ _ (hη₀.trans_le (hright i).2.1)⟩
  · intro r
    let twist := vectorSweepTwist q hq n a b η r
    let d := vectorAssemblyPivot q hq n a b η r
    let K := vectorShiftedMatrix n a b η
    have ht : η ≤ twist.2 :=
      vectorSweepTwist_im_lower q hq n a b η hω hη₀ hη₁ hNative ha hb r
    refine ⟨ht, vectorSquaredModulus_pos q hq _ _ (hη₀.trans_le ht), ?_⟩
    obtain ⟨D, β, hD, hdiag, hEdge⟩ :=
      vector_assemble_row_witnesses hq a b η hω hη₀ hη₁ hNative ha hb r
    let M := rootedSymmetricMatrix r (vectorParent r) β D
    let E := M - K
    let L := 1 + rootedEliminationPart r (vectorParent r) β d
    have hKE : K + E = M := by dsimp [E]; abel
    have hd (i : Fin n) : d i ≠ 0 := by
      have him : 0 < -(d i).im := by
        dsimp only [d, vectorAssemblyPivot, vectorComplexPivot]
        split_ifs <;> rw [neg_neg]
        · exact hη₀.trans_le (hleft i).2.1
        · exact hη₀.trans_le (hright i).2.1
        · exact hη₀.trans_le ht
      intro heq
      rw [heq, Complex.zero_im, neg_zero] at him
      exact (lt_irrefl 0) him
    have hfac : M = L * Matrix.diagonal d * Lᵀ :=
      rootedElimination_factor r (vectorParent r) β d D hd (vectorParent_ne_self r) hD
    obtain ⟨hunit, hinv⟩ := rootedElimination_inv_apply r (vectorParent r) β d hd
      (vectorRootDistance r) n (vectorRootDistance_lt r) (vectorRootDistance_parent r)
    change IsUnit (L * Matrix.diagonal d * Lᵀ) at hunit
    change (L * Matrix.diagonal d * Lᵀ)⁻¹ r r = (d r)⁻¹ at hinv
    rw [← hfac] at hunit hinv
    have hdr : d r = vectorComplexPivot twist := by
      simp only [d, twist, vectorAssemblyPivot, lt_irrefl, if_false]
    have hsymm (i j : Fin n) : E i j = E j i := by
      change M i j - K i j = M j i - K j i
      rw [show M i j = M j i from vector_rooted_symm r β D i j, show K i j = K j i from vector_shifted_symm a b η i j]
    have hband (i j : Fin n) (hij : i.val + 1 < j.val ∨ j.val + 1 < i.val) : E i j = 0 := by
      change M i j - K i j = 0
      dsimp only [M, K]
      rw [vector_rooted_band r β D i j hij, vector_shifted_band a b η i j hij, sub_self]
    have hw₀ := (unitRoundoff_pos q).le
    have hEdiag (i : Fin n) : ‖E i i‖ ≤ 17 * unitRoundoff q := by
      simpa only [E, M, K, Matrix.sub_apply, vectorShiftedMatrix, rootedSymmetricMatrix,
        if_pos rfl] using hdiag i
    have hEedge (i j : Fin n) (hij : i.val + 1 = j.val) : ‖E i j‖ ≤ 11 * unitRoundoff q := by
      change ‖M i j - K i j‖ ≤ _
      dsimp only [M, K]
      rw [vector_rooted_edge r β D i j hij, vector_shifted_edge a b η i j hij]
      apply vectorEdgeBound_norm_sub hw₀ _ (hEdge i j hij)
      exact hb i.val (by rw [hij]; exact j.isLt)
    have hEoff (i j : Fin n) (hij : i.val + 1 = j.val ∨ j.val + 1 = i.val) :
        ‖E i j‖ ≤ 11 * unitRoundoff q := by
      rcases hij with h | h
      · exact hEedge i j h
      · rw [hsymm i j]
        exact hEedge j i h
    have hnorm := complexMatrixOperatorNorm_le_of_tridiagonal E
      (show 0 ≤ 17 * unitRoundoff q by positivity) (show 0 ≤ 11 * unitRoundoff q by positivity)
      hband hEdiag hEoff
    refine ⟨E, β, Matrix.ext fun i j => hsymm j i, hband, ?_, ?_, ?_, hnorm.trans ?_, ?_, ?_⟩
    · rw [hKE, hfac]
    · rwa [hKE]
    · rwa [hKE, ← hdr]
    · linarith
    · intro j hj
      rw [hKE]
      exact vector_rooted_parent_edge r β D j hj
    · intro i j hij
      rw [hKE]
      simpa only [M, vector_rooted_edge r β D i j hij, VectorEdgeBound] using hEdge i j hij

end NumStability.CertifiedTridiagonalEigenpairs
