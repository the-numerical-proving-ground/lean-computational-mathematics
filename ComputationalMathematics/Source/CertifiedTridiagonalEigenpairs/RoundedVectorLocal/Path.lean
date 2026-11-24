import ComputationalMathematics.Source.CertifiedTridiagonalEigenpairs.RoundedVectorLocal.MatrixFactorization
import ComputationalMathematics.Source.CertifiedTridiagonalEigenpairs.RoundedVectorLocal.Sweep

namespace NumStability.CertifiedTridiagonalEigenpairs

/-- Parent in the elimination toward row r. Every non-root parent is one
row nearer r and the root is fixed. -/
def vectorParent {n : ℕ} (r j : Fin n) : Fin n :=
  if h : j.val < r.val then ⟨j.val + 1, by omega⟩
  else if h' : r.val < j.val then ⟨j.val - 1, by omega⟩
  else r

theorem vectorParent_eq_iff {n : ℕ} (r i j : Fin n) :
    j ≠ r ∧ vectorParent r j = i ↔
      (j.val + 1 = i.val ∧ j.val < r.val) ∨ (i.val + 1 = j.val ∧ r.val < j.val) := by
  by_cases h : j.val < r.val
  · have hne : j ≠ r := by intro e; subst j; omega
    have hp : (vectorParent r j).val = j.val + 1 := by rw [vectorParent, dif_pos h]
    constructor
    · rintro ⟨_, he⟩
      exact Or.inl ⟨hp.symm.trans (congrArg Fin.val he), h⟩
    · intro hor
      refine ⟨hne, Fin.ext ?_⟩
      omega
  · by_cases h' : r.val < j.val
    · have hne : j ≠ r := by intro e; subst j; omega
      have hp : (vectorParent r j).val = j.val - 1 := by rw [vectorParent, dif_neg h, dif_pos h']
      constructor
      · rintro ⟨_, he⟩
        have hv := congrArg Fin.val he
        exact Or.inr ⟨by omega, h'⟩
      · intro hor
        refine ⟨hne, Fin.ext ?_⟩
        omega
    · have he : j = r := Fin.ext (by omega)
      simp [he, vectorParent]

/-- Number of path edges between two row indices. -/
def vectorRootDistance {n : ℕ} (r j : Fin n) : ℕ :=
  (r.val - j.val) + (j.val - r.val)

theorem vectorRootDistance_lt {n : ℕ} (r j : Fin n) : vectorRootDistance r j < n := by
  unfold vectorRootDistance
  have := r.isLt
  have := j.isLt
  omega

theorem vectorRootDistance_parent {n : ℕ} (r j : Fin n) (hj : j ≠ r) :
    vectorRootDistance r (vectorParent r j) + 1 = vectorRootDistance r j := by
  rcases (vectorParent_eq_iff r (vectorParent r j) j).1 ⟨hj, rfl⟩ with hl | hr
  · unfold vectorRootDistance
    omega
  · unfold vectorRootDistance
    omega

theorem vectorParent_ne_self {n : ℕ} (r j : Fin n) (hj : j ≠ r) : vectorParent r j ≠ j := by
  intro h
  have hr := vectorRootDistance_parent r j hj
  rw [h] at hr
  omega

/-- Exact shifted input matrix K in path order. Here a is the exact shifted
real diagonal, so a i stands for A[i,i] minus the supplied label. -/
noncomputable def vectorShiftedMatrix (n : ℕ) (a b : ℕ → ℝ) (η : ℝ) :
    Matrix (Fin n) (Fin n) ℂ :=
  fun i j => if i = j then ⟨a i.val, -η⟩
    else if i.val + 1 = j.val then (b i.val : ℂ)
    else if j.val + 1 = i.val then (b j.val : ℂ) else 0

/-- The complex pivot obtained from its stored real and positive imaginary
components. -/
def vectorComplexPivot (d : ℝ × ℝ) : ℂ := ⟨d.1, -d.2⟩

/-- The pivot sequence for exact elimination toward the selected row. -/
noncomputable def vectorAssemblyPivot (p : ℕ) (hp : 2 ≤ p) (n : ℕ) (a b : ℕ → ℝ)
    (η : ℝ) (r i : Fin n) : ℂ :=
  vectorComplexPivot
    (if i.val < r.val then vectorLeftSweep p hp a b η i.val
     else if r.val < i.val then vectorRightSweep p hp n a b η i.val
     else vectorSweepTwist p hp n a b η r)

private theorem vector_child_sum {n : ℕ} (r i : Fin n) (f : Fin n → ℂ) :
    (∑ j, if j ≠ r ∧ vectorParent r j = i then f j else 0) =
      (if h : 0 < i.val ∧ i.val ≤ r.val then f ⟨i.val - 1, by omega⟩ else 0) +
      (if h : i.val + 1 < n ∧ r.val ≤ i.val then f ⟨i.val + 1, h.1⟩ else 0) := by
  rw [← show
    (∑ j : Fin n, if j.val + 1 = i.val ∧ j.val < r.val then f j else 0) =
      (if h : 0 < i.val ∧ i.val ≤ r.val then f ⟨i.val - 1, by omega⟩ else 0) from by
        by_cases h : 0 < i.val ∧ i.val ≤ r.val
        · rw [dif_pos h, Finset.sum_eq_single ⟨i.val - 1, by omega⟩]
          · rw [if_pos (show i.val - 1 + 1 = i.val ∧ i.val - 1 < r.val by omega)]
          · intro j _ hj
            apply if_neg
            intro h'
            apply hj
            apply Fin.ext
            change j.val = i.val - 1
            omega
          · simp
        · rw [dif_neg h]
          apply Finset.sum_eq_zero
          intro j _
          apply if_neg
          omega,
      ← show
    (∑ j : Fin n, if i.val + 1 = j.val ∧ r.val < j.val then f j else 0) =
      (if h : i.val + 1 < n ∧ r.val ≤ i.val then f ⟨i.val + 1, h.1⟩ else 0) from by
        by_cases h : i.val + 1 < n ∧ r.val ≤ i.val
        · rw [dif_pos h, Finset.sum_eq_single ⟨i.val + 1, h.1⟩]
          · rw [if_pos (show i.val + 1 = i.val + 1 ∧ r.val < i.val + 1 by omega)]
          · intro j _ hj
            apply if_neg
            intro h'
            apply hj
            exact Fin.ext h'.1.symm
          · simp
        · rw [dif_neg h]
          apply Finset.sum_eq_zero
          intro j _
          apply if_neg
          have hj := j.isLt
          omega, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hl : j.val + 1 = i.val ∧ j.val < r.val
  · have hr : ¬ (i.val + 1 = j.val ∧ r.val < j.val) := by omega
    rw [if_pos ((vectorParent_eq_iff r i j).2 (Or.inl hl)), if_pos hl, if_neg hr, add_zero]
  · simp only [vectorParent_eq_iff, hl, false_or, if_false, zero_add]

theorem vector_rooted_diag_from_children {n : ℕ} (r : Fin n) (d D β : Fin n → ℂ)
    (hchild : ∀ i,
      D i = d i +
        ((if h : 0 < i.val ∧ i.val ≤ r.val then (β ⟨i.val - 1, by omega⟩) ^ 2 /
            d ⟨i.val - 1, by omega⟩ else 0) +
         (if h : i.val + 1 < n ∧ r.val ≤ i.val then (β ⟨i.val + 1, h.1⟩) ^ 2 /
            d ⟨i.val + 1, h.1⟩ else 0))) :
    ∀ i, D i = d i + ∑ j, if j ≠ r ∧ vectorParent r j = i then β j ^ 2 / d j else 0 := by
  intro i
  rw [vector_child_sum, hchild i]

theorem vector_rooted_band {n : ℕ} (r : Fin n) (β D : Fin n → ℂ) (i j : Fin n)
    (hij : i.val + 1 < j.val ∨ j.val + 1 < i.val) :
    rootedSymmetricMatrix r (vectorParent r) β D i j = 0 := by
  have hin : i ≠ j := by intro h; subst j; omega
  simp only [rootedSymmetricMatrix, hin, if_false, vectorParent_eq_iff]
  have h₁ : ¬ ((j.val + 1 = i.val ∧ j.val < r.val) ∨ (i.val + 1 = j.val ∧ r.val < j.val)) := by omega
  have h₂ : ¬ ((i.val + 1 = j.val ∧ i.val < r.val) ∨ (j.val + 1 = i.val ∧ r.val < i.val)) := by omega
  simp only [h₁, h₂, if_false, add_zero]

theorem vector_rooted_edge {n : ℕ} (r : Fin n) (β D : Fin n → ℂ) (i j : Fin n)
    (hij : i.val + 1 = j.val) :
    rootedSymmetricMatrix r (vectorParent r) β D i j = if i.val < r.val then β i else β j := by
  have hin : i ≠ j := by intro h; subst j; omega
  simp only [rootedSymmetricMatrix, hin, if_false, vectorParent_eq_iff]
  by_cases hi : i.val < r.val
  · have hj : ¬ ((j.val + 1 = i.val ∧ j.val < r.val) ∨ (i.val + 1 = j.val ∧ r.val < j.val)) := by omega
    rw [if_neg hj, if_pos (Or.inl ⟨hij, hi⟩), if_pos hi, zero_add]
  · have hj : r.val < j.val := by omega
    have hn : ¬ (j.val + 1 = i.val) := by omega
    simp only [hj, hi, hn, hij, false_and, and_false, true_and, false_or, if_true, if_false,
      add_zero]

theorem vector_rooted_symm {n : ℕ} (r : Fin n) (β D : Fin n → ℂ) (i j : Fin n) :
    rootedSymmetricMatrix r (vectorParent r) β D i j =
      rootedSymmetricMatrix r (vectorParent r) β D j i := by
  by_cases h : i = j
  · subst j; rfl
  · simp [rootedSymmetricMatrix, h, Ne.symm h, add_comm]

end NumStability.CertifiedTridiagonalEigenpairs
