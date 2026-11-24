import ComputationalMathematics.Source.CertifiedTridiagonalEigenpairs.RoundedVectorLocal.Path
import ComputationalMathematics.Source.CertifiedTridiagonalEigenpairs.Section06.RoundedPath

namespace NumStability.CertifiedTridiagonalEigenpairs

open scoped Matrix
open FloatingPointFormat.UnboundedBinary

section RootedRecurrence

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Inverse column recurrence for the matrix reconstructed from a rooted exact
factorization. The root column of the lower factor is the root basis vector;
the remaining equations each use the stored pivot and one absorbed edge. -/
theorem rootedElimination_inverseColumn_recurrence
    (r : ι) (parent : ι → ι) (β d : ι → ℂ) (hd : ∀ i, d i ≠ 0)
    (rank : ι → ℕ) (bound : ℕ) (hbound : ∀ i, rank i < bound)
    (hparent : ∀ j ≠ r, rank (parent j) + 1 = rank j) :
    let L := 1 + rootedEliminationPart r parent β d
    let w := fun i => (L * Matrix.diagonal d * Lᵀ)⁻¹ i r
    w r = (d r)⁻¹ ∧ ∀ j ≠ r, w j = -(β j / d j) * w (parent j) := by
  let L := 1 + rootedEliminationPart r parent β d
  let D : Matrix ι ι ℂ := Matrix.diagonal d
  let M := L * D * Lᵀ
  let e : ι → ℂ := Pi.single r 1
  let w := fun i => M⁻¹ i r
  obtain ⟨hM, hwr⟩ := rootedElimination_inv_apply r parent β d hd rank bound hbound hparent
  have hunit : IsUnit (L.det * D.det * Lᵀ.det) := by
    simpa only [M, Matrix.det_mul] using (M.isUnit_iff_isUnit_det.mp hM)
  have hL := L.isUnit_iff_isUnit_det.mpr
    (isUnit_of_mul_isUnit_left (isUnit_of_mul_isUnit_left hunit))
  have hLe : L *ᵥ e = e := by
    change L *ᵥ Pi.single r 1 = e
    rw [Matrix.mulVec_single_one]
    funext i
    by_cases hi : i = r
    · subst i
      simp [L, rootedEliminationPart, Matrix.col, e]
    · simp [L, rootedEliminationPart, Matrix.col, e, Matrix.one_apply_ne hi, Pi.single_eq_of_ne hi]
  have hcol : M *ᵥ w = e := by
    change M *ᵥ M⁻¹.col r = e
    rw [← Matrix.mulVec_single_one, Matrix.mulVec_mulVec,
      Matrix.mul_nonsing_inv M (M.isUnit_iff_isUnit_det.mp hM), Matrix.one_mulVec]
  have he : D *ᵥ (Lᵀ *ᵥ w) = e := by
    apply Matrix.mulVec_injective_of_isUnit hL
    rw [hLe, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
    exact hcol
  have hrow (j : ι) (hj : j ≠ r) :
      (Lᵀ *ᵥ w) j = w j + (β j / d j) * w (parent j) := by
    change ((1 + rootedEliminationPart r parent β d)ᵀ *ᵥ w) j = _
    rw [Matrix.transpose_add, Matrix.transpose_one, Matrix.add_mulVec, Matrix.one_mulVec]
    simp only [Pi.add_apply, add_right_inj, Matrix.mulVec, Matrix.transpose_apply, dotProduct,
      rootedEliminationPart]
    rw [Finset.sum_eq_single (parent j)]
    · simp [hj]
    · intro i _ hi
      simp [hj, Ne.symm hi]
    · simp
  refine ⟨hwr, fun j hj => ?_⟩
  have h := congrFun he j
  change (Matrix.diagonal d *ᵥ (Lᵀ *ᵥ w)) j = e j at h
  rw [Matrix.mulVec_diagonal, hrow j hj, show e j = 0 from Pi.single_eq_of_ne hj 1] at h
  have hz := (mul_eq_zero.mp h).resolve_left (hd j)
  linear_combination hz

end RootedRecurrence

section Paths

variable {ι : Type*} [DecidableEq ι]

/-- Steps on the path from a coordinate back to the root. The fuel is only
used to make the recursion total. Each step visits its parent. -/
def inversePathIndices (r : ι) (parent : ι → ι) : ℕ → ι → List ι
  | 0, _ => []
  | k + 1, i => if i = r then [] else i :: inversePathIndices r parent k (parent i)

private theorem inversePathIndices_length_le (r : ι) (parent : ι → ι) (k : ℕ) (i : ι) :
    (inversePathIndices r parent k i).length ≤ k := by
  induction k generalizing i with
  | zero => simp [inversePathIndices]
  | succ k ih =>
    by_cases hi : i = r
    · simp [inversePathIndices, hi]
    · simp only [inversePathIndices, if_neg hi, List.length_cons]
      exact Nat.succ_le_succ (ih (parent i))

private theorem inversePathIndices_ne_root (r : ι) (parent : ι → ι) (k : ℕ) (i j : ι)
    (hj : j ∈ inversePathIndices r parent k i) : j ≠ r := by
  induction k generalizing i with
  | zero => simp [inversePathIndices] at hj
  | succ k ih =>
    by_cases hi : i = r
    · simp [inversePathIndices, hi] at hj
    · simp only [inversePathIndices, if_neg hi, List.mem_cons] at hj
      exact hj.elim (fun h => h ▸ hi) (ih (parent i))

private theorem inversePathIndices_eq_of_rank (r : ι) (parent : ι → ι) (rank : ι → ℕ)
    (hparent : ∀ i ≠ r, rank (parent i) + 1 = rank i) (i : ι) (k₁ k₂ : ℕ)
    (h₁ : rank i ≤ k₁) (h₂ : rank i ≤ k₂) :
    inversePathIndices r parent k₁ i = inversePathIndices r parent k₂ i := by
  induction k₁ generalizing i k₂ with
  | zero =>
    have hr : i = r := by by_contra h; have := hparent i h; omega
    cases k₂ <;> simp [inversePathIndices, hr]
  | succ k₁ ih =>
    by_cases hr : i = r
    · cases k₂ <;> simp [inversePathIndices, hr]
    · have hh := hparent i hr
      cases k₂ with
      | zero => omega
      | succ k₂ =>
        simp only [inversePathIndices, if_neg hr, List.cons.injEq, true_and]
        exact ih (parent i) k₂ (by omega) (by omega)

private theorem inversePathIndices_root (r : ι) (parent : ι → ι) (k : ℕ) :
    inversePathIndices r parent k r = [] := by
  cases k <;> simp [inversePathIndices]

private theorem inversePathIndices_step (r : ι) (parent : ι → ι) (rank : ι → ℕ)
    (hparent : ∀ i ≠ r, rank (parent i) + 1 = rank i) (i : ι) (hi : i ≠ r)
    (k : ℕ) (hk : rank i ≤ k) :
    inversePathIndices r parent k i = i :: inversePathIndices r parent k (parent i) := by
  have hpar := hparent i hi
  cases k with
  | zero => omega
  | succ k =>
    simp only [inversePathIndices, if_neg hi, List.cons.injEq, true_and]
    exact inversePathIndices_eq_of_rank r parent rank hparent (parent i) k (k + 1)
      (by omega) (by omega)

/-- The rounded inverse column from one twist, the original edges, and the
pivots already computed by the two directional eliminations. -/
noncomputable def roundedInverseColumn (n p : ℕ) (hp : 2 ≤ p) (r : Fin n)
    (parent : Fin n → Fin n) (edge : Fin n → InversePathEdge) (x y : ℝ) (i : Fin n) : ℂ :=
  roundedInversePath p hp x y ((inversePathIndices r parent n i).map edge)

/-- The rounded column obeys the original-edge outward recurrence with the
stored twist reciprocal at the root. Every non-root coordinate uses the
rounded value of its parent. -/
theorem roundedInverseColumn_recurrence (n p : ℕ) (hp : 2 ≤ p) (r : Fin n)
    (parent : Fin n → Fin n) (edge : Fin n → InversePathEdge) (x y : ℝ)
    (rank : Fin n → ℕ) (hbound : ∀ i, rank i < n)
    (hparent : ∀ i ≠ r, rank (parent i) + 1 = rank i) :
    roundedInverseColumn n p hp r parent edge x y r = roundedTwistReciprocal p hp x y ∧
    ∀ i ≠ r, roundedInverseColumn n p hp r parent edge x y i =
      roundedInverseStep p hp (edge i) (roundedInverseColumn n p hp r parent edge x y (parent i)) := by
  constructor
  · simp [roundedInverseColumn, inversePathIndices_root, roundedInversePath]
  · intro i hi
    unfold roundedInverseColumn
    rw [inversePathIndices_step r parent rank hparent i hi n ((hbound i).le)]
    rfl

/-- In the exact column only the absorbed edges and the stored pivots occur. -/
theorem exactInversePath_eq_inverseColumn [Fintype ι]
    (r : ι) (parent : ι → ι) (edge : ι → InversePathEdge) (x y : ℝ) (hy : 0 < y)
    (hpivot : ∀ j ≠ r, 0 < (edge j).pivotNegIm)
    (rank : ι → ℕ) (bound : ℕ) (hbound : ∀ i, rank i < bound)
    (hparent : ∀ j ≠ r, rank (parent j) + 1 = rank j) (i : ι) :
    let d := fun j => if j = r then (⟨x, -y⟩ : ℂ) else (edge j).pivot
    let L := 1 + rootedEliminationPart r parent (fun j => (edge j).absorbed) d
    exactInversePath x y ((inversePathIndices r parent bound i).map edge) =
      (L * Matrix.diagonal d * Lᵀ)⁻¹ i r := by
  let d := fun j => if j = r then (⟨x, -y⟩ : ℂ) else (edge j).pivot
  let β := fun j => (edge j).absorbed
  have hd (j : ι) : d j ≠ 0 := by
    by_cases hj : j = r
    · intro hz
      have h := congrArg Complex.im hz
      simp [d, hj, hy.ne'] at h
    · intro hz
      have h := congrArg Complex.im hz
      simp [d, hj, InversePathEdge.pivot, (hpivot j hj).ne'] at h
  let L := 1 + rootedEliminationPart r parent β d
  let w := fun j => (L * Matrix.diagonal d * Lᵀ)⁻¹ j r
  obtain ⟨hroot, hstep⟩ :=
    rootedElimination_inverseColumn_recurrence r parent β d hd rank bound hbound hparent
  change w r = (d r)⁻¹ at hroot
  change ∀ j ≠ r, w j = -(β j / d j) * w (parent j) at hstep
  have aux (k : ℕ) (j : ι) (hk : rank j ≤ k) :
      exactInversePath x y ((inversePathIndices r parent k j).map edge) = w j := by
    induction k generalizing j with
    | zero =>
      have hr : j = r := by by_contra hj; have := hparent j hj; omega
      subst j
      simp [inversePathIndices, exactInversePath, hroot, d]
    | succ k ih =>
      by_cases hj : j = r
      · subst j
        simp [inversePathIndices, exactInversePath, hroot, d]
      · have hpar := hparent j hj
        simp only [inversePathIndices, if_neg hj, List.map_cons, exactInversePath]
        rw [ih (parent j) (by omega), hstep j hj]
        simp [exactInverseStep, β, d, hj]
  exact aux bound i (hbound i).le

end Paths

/-- Directional pivot and original edge for one outward tridiagonal step. -/
noncomputable def vectorOutwardEdge (q : ℕ) (hq : 2 ≤ q) (n : ℕ) (a b : ℕ → ℝ)
    (η : ℝ) (r i : Fin n) (β : ℂ) : InversePathEdge :=
  let left := i.val < r.val
  let d := if left then vectorLeftSweep q hq a b η i.val
    else vectorRightSweep q hq n a b η i.val
  ⟨if left then b i.val else b (i.val - 1), β, d.1, d.2⟩

/-- Section 6's rounded selected column. The stored sweeps and twist and
the original edges are its arithmetic inputs. -/
noncomputable def vectorRoundedInverseColumn (q : ℕ) (hq : 2 ≤ q) (n : ℕ)
    (a b : ℕ → ℝ) (η : ℝ) (r : Fin n) (i : Fin n) : ℂ :=
  let γ := vectorSweepTwist q hq n a b η r
  roundedInverseColumn n q hq r (vectorParent r)
    (fun j => vectorOutwardEdge q hq n a b η r j 0) γ.1 γ.2 i

/-- The selected score is the central imaginary part, and each outward
propagation uses the rounded parent and the input edge on that side. -/
theorem vectorRoundedInverseColumn_recurrence (q : ℕ) (hq : 2 ≤ q) (n : ℕ)
    (a b : ℕ → ℝ) (η : ℝ) (r : Fin n) :
    let γ := vectorSweepTwist q hq n a b η r
    let wHat := vectorRoundedInverseColumn q hq n a b η r
    wHat r = roundedTwistReciprocal q hq γ.1 γ.2 ∧
    (wHat r).im = vectorScore q hq γ ∧
    ∀ i ≠ r, wHat i = roundedInverseStep q hq (vectorOutwardEdge q hq n a b η r i 0)
      (wHat (vectorParent r i)) := by
  let γ := vectorSweepTwist q hq n a b η r
  obtain ⟨hr, hi⟩ := roundedInverseColumn_recurrence n q hq r (vectorParent r)
    (fun j => vectorOutwardEdge q hq n a b η r j 0) γ.1 γ.2 (vectorRootDistance r)
    (vectorRootDistance_lt r) (vectorRootDistance_parent r)
  exact ⟨hr, congrArg Complex.im hr, hi⟩

/-- The imaginary components supplied to normalization belong to the
working format. -/
theorem vectorRoundedInverseColumn_im_native (q : ℕ) (hq : 2 ≤ q) (n : ℕ)
    (a b : ℕ → ℝ) (η : ℝ) (r i : Fin n) :
    Native q hq (vectorRoundedInverseColumn q hq n a b η r i).im :=
  roundedInversePath_im_native q hq _ _ _

private theorem rounded_outward_path_independent_of_absorbed (q : ℕ) (hq : 2 ≤ q) (n : ℕ)
    (a b : ℕ → ℝ) (η : ℝ) (r : Fin n) (path : List (Fin n)) (β : Fin n → ℂ) :
    let γ := vectorSweepTwist q hq n a b η r
    roundedInversePath q hq γ.1 γ.2 (path.map (fun j => vectorOutwardEdge q hq n a b η r j (β j))) =
      roundedInversePath q hq γ.1 γ.2 (path.map (fun j => vectorOutwardEdge q hq n a b η r j 0)) := by
  induction path with
  | nil => rfl
  | cons i path ih =>
    simp only [List.map_cons, roundedInversePath]
    rw [ih]
    rfl

/-- Section 6's path error and filtered component error for the selected
column of the matrix reconstructed by the structured backward analysis. -/
theorem vectorRoundedInverseColumn_bounds (q : ℕ) (hq : 2 ≤ q) (n : ℕ) (hn : 2 ≤ n)
    (a b : ℕ → ℝ) (η : ℝ) (r : Fin n) (hη : 0 < η) {u : ℝ}
    (hu : u ≤ 1 / 128) (hnω : (n : ℝ) * unitRoundoff q ≤ 1 / 128)
    (hprecision : (n : ℝ) * unitRoundoff q ≤ u / 65536)
    (hpivots : ∀ i : Fin n, η ≤ (vectorLeftSweep q hq a b η i.val).2 ∧
      η ≤ (vectorRightSweep q hq n a b η i.val).2)
    (htwist : η ≤ (vectorSweepTwist q hq n a b η r).2)
    (E : Matrix (Fin n) (Fin n) ℂ) (β : Fin n → ℂ) (hE : Eᵀ = E)
    (hfactor :
      let d := vectorAssemblyPivot q hq n a b η r
      let L := 1 + rootedEliminationPart r (vectorParent r) β d
      vectorShiftedMatrix n a b η + E = L * Matrix.diagonal d * Lᵀ)
    (hedge : ∀ j : Fin n, j ≠ r → (vectorShiftedMatrix n a b η + E) (vectorParent r j) j = β j)
    (hperturb : ∀ i j : Fin n, i.val + 1 = j.val →
      let e := (vectorShiftedMatrix n a b η + E) i j
      (b i.val = 0 → e = 0) ∧
      (b i.val ≠ 0 → ‖e / (b i.val : ℂ) - 1‖ ≤ 11 * unitRoundoff q)) :
    let w : PiLp 2 (fun _ : Fin n => ℂ) :=
      WithLp.toLp 2 (fun i => (vectorShiftedMatrix n a b η + E)⁻¹ i r)
    let wHat : PiLp 2 (fun _ : Fin n => ℂ) :=
      WithLp.toLp 2 (vectorRoundedInverseColumn q hq n a b η r)
    let y : PiLp 2 (fun _ : Fin n => ℝ) := WithLp.toLp 2 (fun i => (w i).im)
    let yHat : PiLp 2 (fun _ : Fin n => ℝ) := WithLp.toLp 2 (fun i => (wHat i).im)
    ‖wHat - w‖ ≤ 64 * (n : ℝ) * unitRoundoff q * ‖w‖ ∧
    ‖wHat - w‖ ≤ u / 1024 * ‖w‖ ∧
    (‖w‖ ≤ 3 * ‖y‖ → ‖yHat - y‖ ≤ (3 * u / 1024) * ‖y‖ ∧ yHat ≠ 0) := by
  let γ := vectorSweepTwist q hq n a b η r
  let edge := fun j => vectorOutwardEdge q hq n a b η r j (β j)
  let path := fun i => (inversePathIndices r (vectorParent r) n i).map edge
  let M := vectorShiftedMatrix n a b η + E
  have hγ : 0 < γ.2 := hη.trans_le htwist
  have hp (j : Fin n) : 0 < (edge j).pivotNegIm := by
    by_cases h : j.val < r.val
    · simpa [edge, vectorOutwardEdge, h, (show j < r from h)] using hη.trans_le (hpivots j).1
    · simpa [edge, vectorOutwardEdge, h, (show ¬ j < r from h)] using hη.trans_le (hpivots j).2
  have hpert (j : Fin n) (hj : j ≠ r) :
      ‖(edge j).absorbed - ((edge j).original : ℂ)‖ ≤ 11 * unitRoundoff q * ‖((edge j).original : ℂ)‖ := by
    have hrel (e : ℂ) (c : ℝ) (h₀ : c = 0 → e = 0)
        (h₁ : c ≠ 0 → ‖e / (c : ℂ) - 1‖ ≤ 11 * unitRoundoff q) :
        ‖e - (c : ℂ)‖ ≤ 11 * unitRoundoff q * ‖(c : ℂ)‖ := by
      by_cases hz : c = 0
      · simp [h₀ hz, hz]
      have hc : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hz
      have hb := h₁ hz
      rw [← div_self hc, ← sub_div, norm_div] at hb
      exact (div_le_iff₀ (norm_pos_iff.mpr hc)).mp hb
    let i := vectorParent r j
    have hβ : M i j = β j := hedge j hj
    rcases (vectorParent_eq_iff r i j).mp ⟨hj, rfl⟩ with hl | hr
    · change ‖β j - ((if j.val < r.val then b j.val else b (j.val - 1)) : ℝ)‖ ≤ _
      have hm : M j i = M i j := by
        have hi : i ≠ j := vectorParent_ne_self r j hj
        have hne : ¬ i.val + 1 = j.val := by omega
        have he := congrArg (fun T : Matrix (Fin n) (Fin n) ℂ => T i j) hE
        change E j i = E i j at he
        simp [M, vectorShiftedMatrix, hi, Ne.symm hi, hl.1, hne, he]
      have h := hperturb j i hl.1
      simpa [edge, vectorOutwardEdge, hl.2, (show j < r from hl.2), hm, hβ] using hrel (M j i) (b j.val) h.1 h.2
    · have h := hperturb i j hr.1
      have hi : i.val = j.val - 1 := by omega
      have hnlt : ¬ j.val < r.val := by omega
      simpa [edge, vectorOutwardEdge, hnlt, (show ¬ j < r from hnlt), ← hi, hβ] using hrel (M i j) (b i.val) h.1 h.2
  have hw (i : Fin n) :
      exactInversePath γ.1 γ.2 (path i) = M⁻¹ i r := by
    have hd : (fun j => if j = r then (⟨γ.1, -γ.2⟩ : ℂ) else (edge j).pivot) =
        vectorAssemblyPivot q hq n a b η r := by
      funext j
      by_cases hj : j = r
      · subst j
        simp [vectorAssemblyPivot, vectorComplexPivot, γ]
      · have hne : j.val ≠ r.val := fun h => hj (Fin.ext h)
        by_cases hl : j.val < r.val
        · simp [hj, hl, (show j < r from hl), edge, vectorOutwardEdge, vectorAssemblyPivot, InversePathEdge.pivot,
            vectorComplexPivot]
        · have hr : r.val < j.val := by omega
          simp [hj, hl, hr, (show ¬ j < r from hl), edge, vectorOutwardEdge, vectorAssemblyPivot, InversePathEdge.pivot,
            vectorComplexPivot]
    have h := exactInversePath_eq_inverseColumn r (vectorParent r) edge γ.1 γ.2 hγ (fun j _ => hp j)
      (vectorRootDistance r) n (vectorRootDistance_lt r) (vectorRootDistance_parent r) i
    dsimp only at h
    rw [hd] at h
    have hb : (fun j => (edge j).absorbed) = β := rfl
    rw [hb, ← hfactor] at h
    exact h
  have hh (i : Fin n) :
      roundedInversePath q hq γ.1 γ.2 (path i) = vectorRoundedInverseColumn q hq n a b η r i :=
    rounded_outward_path_independent_of_absorbed q hq n a b η r _ β
  have hlen (i : Fin n) : (path i).length ≤ n := by
    simpa [path] using inversePathIndices_length_le r (vectorParent r) n i
  have hpath := roundedInversePathVectors_bounds n q hq hn hnω hprecision γ.1 γ.2 hγ path hlen
    (fun i e he => by
      obtain ⟨j, _, rfl⟩ := List.mem_map.mp he
      exact hp j)
    (fun i e he => by
      obtain ⟨j, hj, rfl⟩ := List.mem_map.mp he
      exact hpert j (inversePathIndices_ne_root r (vectorParent r) n i j hj))
  simp only [hw, hh] at hpath
  dsimp only
  refine ⟨hpath.1, hpath.2.1, fun hphase => ⟨hpath.2.2 hphase, ?_⟩⟩
  let y : PiLp 2 (fun _ : Fin n => ℝ) := WithLp.toLp 2 (fun i => (M⁻¹ i r).im)
  have hy : y ≠ 0 := by
    intro hz
    have hroot := congrFun (congrArg WithLp.ofLp hz) r
    change (M⁻¹ r r).im = 0 at hroot
    rw [← hw r] at hroot
    simp only [path, inversePathIndices_root, List.map_nil, exactInversePath,
      Complex.inv_im, Complex.normSq_apply] at hroot
    have hden : 0 < γ.1 * γ.1 + (-γ.2) * (-γ.2) := by
      nlinarith [sq_nonneg γ.1, sq_pos_of_pos hγ]
    exact (div_pos hγ hden).ne' (by simpa only [neg_neg] using hroot)
  intro hyHat
  have h := hpath.2.2 hphase
  rw [hyHat, zero_sub, norm_neg] at h
  have hcoef : 3 * u / 1024 < 1 := by linarith
  exact (not_lt_of_ge h) (by
    change 3 * u / 1024 * ‖y‖ < ‖y‖
    calc
      _ < 1 * ‖y‖ := mul_lt_mul_of_pos_right hcoef (norm_pos_iff.mpr hy)
      _ = _ := one_mul _)

end NumStability.CertifiedTridiagonalEigenpairs
