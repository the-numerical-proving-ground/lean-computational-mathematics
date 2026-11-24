import ComputationalMathematics.Analysis.SingularValues.Transpose
import ComputationalMathematics.Analysis.OperatorNorms.RealMatrixEuclidean
import Mathlib.Tactic

/-!
# Concrete real rectangular nuclear norm and trace duality

The nuclear norm is the sum of the canonical right-Gram singular values across
all source coordinates, including their zero tail. The trace-duality witness is
the actual unit-diagonal orthonormal factor from an existing real SVD. All shapes,
including zero dimensions and rank zero, are included. No norm/ideal structure
with the desired laws is assumed.
-/

namespace NumStability
noncomputable section
open scoped BigOperators

/-- Actual rectangular nuclear norm, with the canonical zero-extended singular list. -/
def realMatrixNuclearNorm {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) : ℝ :=
  ∑ i : Fin n, rectSingularValue A i

/-- Real rectangular Frobenius/trace pairing, with no shape-dependent normalization. -/
def realMatrixTracePairing {m n : ℕ} (W A : Matrix (Fin m) (Fin n) ℝ) : ℝ :=
  ∑ i : Fin m, ∑ j : Fin n, W i j*A i j

/-- Actual rectangular rank-one matrix. -/
def realRankOneMatrix {m n : ℕ} (x : Fin m → ℝ) (y : Fin n → ℝ) :
    Matrix (Fin m) (Fin n) ℝ := fun i j => x i*y j

/-- A concrete partial isometry presented by orthonormal initial/final families. -/
def IsRealMatrixPartialIsometry {m n : ℕ} (W : Matrix (Fin m) (Fin n) ℝ) : Prop :=
  ∃ (r : ℕ) (u : Fin r → EuclideanSpace ℝ (Fin m))
    (v : Fin r → EuclideanSpace ℝ (Fin n)),
    Orthonormal ℝ u ∧ Orthonormal ℝ v ∧
      W = realOrthonormalDiagonalFactor u (fun _ => 1) v

theorem realMatrixNuclearNorm_nonneg {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) :
    0 ≤ realMatrixNuclearNorm A := Finset.sum_nonneg (fun i _ => rectSingularValue_nonneg A i)

theorem realMatrixTracePairing_comm {m n : ℕ} (W A : Matrix (Fin m) (Fin n) ℝ) :
    realMatrixTracePairing W A = realMatrixTracePairing A W := by
  unfold realMatrixTracePairing
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem realMatrixTracePairing_add_right {m n : ℕ}
    (W A B : Matrix (Fin m) (Fin n) ℝ) :
    realMatrixTracePairing W (A+B) = realMatrixTracePairing W A+realMatrixTracePairing W B := by
  simp [realMatrixTracePairing, mul_add, Finset.sum_add_distrib]

theorem realMatrixTracePairing_smul_right {m n : ℕ}
    (W A : Matrix (Fin m) (Fin n) ℝ) (t : ℝ) :
    realMatrixTracePairing W (t • A) = t*realMatrixTracePairing W A := by
  simp only [realMatrixTracePairing, Matrix.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem realMatrixTracePairing_sum_right {m n : ℕ} {ι : Type*}
    (W : Matrix (Fin m) (Fin n) ℝ) (s : Finset ι) (F : ι → Matrix (Fin m) (Fin n) ℝ) :
    realMatrixTracePairing W (∑ k ∈ s, F k) = ∑ k ∈ s, realMatrixTracePairing W (F k) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [realMatrixTracePairing]
  | @insert k s hk ih =>
      rw [Finset.sum_insert hk, Finset.sum_insert hk, realMatrixTracePairing_add_right, ih]

theorem realMatrixTracePairing_rankOne {m n : ℕ}
    (W : Matrix (Fin m) (Fin n) ℝ) (x : Fin m → ℝ) (y : Fin n → ℝ) :
    realMatrixTracePairing W (realRankOneMatrix x y) =
      ∑ i : Fin m, x i*rectMatMulVec W y i := by
  unfold realMatrixTracePairing realRankOneMatrix rectMatMulVec
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  ring

/-- The rank-one pairing bound uses the actual Euclidean operator norm. -/
theorem abs_realMatrixTracePairing_rankOne_le {m n : ℕ}
    (W : Matrix (Fin m) (Fin n) ℝ) (x : Fin m → ℝ) (y : Fin n → ℝ) :
    |realMatrixTracePairing W (realRankOneMatrix x y)| ≤
      realMatrixOperatorNorm W*(vecNorm2 x*vecNorm2 y) := by
  rw [realMatrixTracePairing_rankOne]
  calc
    _ ≤ vecNorm2 x*vecNorm2 (rectMatMulVec W y) := abs_vecInnerProduct_le_vecNorm2_mul _ _
    _ ≤ vecNorm2 x*(realMatrixOperatorNorm W*vecNorm2 y) :=
      mul_le_mul_of_nonneg_left (RealMatrixOperator.rectOpNorm2Le_realMatrixOperatorNorm W y)
        (vecNorm2_nonneg x)
    _ = _ := by ring

/-- A supplied SVD computes the actual nuclear norm, including its zero extension. -/
theorem IsRealMatrixSVD.nuclearNorm_eq_sum_rank {m n r : ℕ}
    {A : Matrix (Fin m) (Fin n) ℝ} {s : Fin n → ℝ}
    {u : Fin r → EuclideanSpace ℝ (Fin m)} {v : Fin r → EuclideanSpace ℝ (Fin n)}
    (h : IsRealMatrixSVD A r s u v) :
    realMatrixNuclearNorm A = ∑ k : Fin r, s (Fin.castLE h.rank_le_width k) := by
  let e : Fin r ↪ Fin n := ⟨Fin.castLE h.rank_le_width, Fin.castLE_injective h.rank_le_width⟩
  let t : Finset (Fin n) := Finset.univ.map e
  have hout : ∀ i ∈ (Finset.univ : Finset (Fin n)), i ∉ t → s i = 0 := by
    intro i hi hit
    apply h.singularValues_zero_of_rank_le i
    by_contra hn
    have hir : i.val < r := Nat.lt_of_not_ge hn
    have he : e ⟨i.val,hir⟩ = i := by apply Fin.ext; rfl
    exact hit (Finset.mem_map.mpr ⟨⟨i.val,hir⟩,Finset.mem_univ _,he⟩)
  unfold realMatrixNuclearNorm
  simp_rw [← h.singularValue_eq_rectSingularValue]
  calc
    (∑ i : Fin n, s i) = ∑ i ∈ t, s i :=
      (Finset.sum_subset (Finset.subset_univ t) hout).symm
    _ = ∑ k : Fin r, s (Fin.castLE h.rank_le_width k) := by simp [t,e]

/-- Exact SVD rank-one decomposition; no new SVD existence construction. -/
theorem IsRealMatrixSVD.eq_sum_rankOne {m n r : ℕ}
    {A : Matrix (Fin m) (Fin n) ℝ} {s : Fin n → ℝ}
    {u : Fin r → EuclideanSpace ℝ (Fin m)} {v : Fin r → EuclideanSpace ℝ (Fin n)}
    (h : IsRealMatrixSVD A r s u v) :
    A = ∑ k : Fin r, s (Fin.castLE h.rank_le_width k) •
      realRankOneMatrix (fun i => u k i) (fun j => v k j) := by
  ext i j
  rw [h.reconstruction i j]
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, realRankOneMatrix]
  apply Finset.sum_congr rfl
  intro k hk
  ring

private theorem euclidean_vecNorm2 {d : ℕ} (x : EuclideanSpace ℝ (Fin d)) :
    vecNorm2 (fun i => x i) = ‖x‖ := by
  simp [vecNorm2, vecNorm2Sq, EuclideanSpace.norm_eq, Real.norm_eq_abs, sq_abs]

/-- Concrete rectangular trace duality, without a dimension factor. -/
theorem abs_realMatrixTracePairing_le_operatorNorm_mul_nuclearNorm {m n : ℕ}
    (W A : Matrix (Fin m) (Fin n) ℝ) :
    |realMatrixTracePairing W A| ≤ realMatrixOperatorNorm W*realMatrixNuclearNorm A := by
  obtain ⟨r,s,u,v,h⟩ := exists_isRealMatrixSVD A
  have hpair : realMatrixTracePairing W A = ∑ k : Fin r,
      s (Fin.castLE h.rank_le_width k)*
        realMatrixTracePairing W (realRankOneMatrix (fun i => u k i) (fun j => v k j)) := by
    conv_lhs => rw [h.eq_sum_rankOne]
    rw [realMatrixTracePairing_sum_right]
    simp only [realMatrixTracePairing_smul_right]
  rw [hpair, h.nuclearNorm_eq_sum_rank, Finset.mul_sum]
  calc
    _ ≤ ∑ k : Fin r, |s (Fin.castLE h.rank_le_width k)*
        realMatrixTracePairing W (realRankOneMatrix (fun i => u k i) (fun j => v k j))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k : Fin r, realMatrixOperatorNorm W*s (Fin.castLE h.rank_le_width k) := by
      apply Finset.sum_le_sum
      intro k hk
      rw [abs_mul, abs_of_nonneg (h.singularValues_nonnegative _)]
      have hb := abs_realMatrixTracePairing_rankOne_le W (fun i => u k i) (fun j => v k j)
      rw [euclidean_vecNorm2, euclidean_vecNorm2,
        h.leftSingularVectors_orthonormal.norm_eq_one k,
        h.rightSingularVectors_orthonormal.norm_eq_one k, one_mul, mul_one] at hb
      exact (mul_le_mul_of_nonneg_left hb (h.singularValues_nonnegative _)).trans_eq (mul_comm _ _)

private theorem orthonormal_coordinate_inner {d r : ℕ}
    (u : Fin r → EuclideanSpace ℝ (Fin d)) (hu : Orthonormal ℝ u) (a b : Fin r) :
    (∑ i : Fin d, u a i*u b i) = if a=b then 1 else 0 := by
  simpa [PiLp.inner_apply, real_inner_eq_re_inner, RCLike.inner_apply, mul_comm]
    using (orthonormal_iff_ite.mp hu a b)

private theorem partialIsometry_action {m n r : ℕ}
    (u : Fin r → EuclideanSpace ℝ (Fin m)) (v : Fin r → EuclideanSpace ℝ (Fin n))
    (hv : Orthonormal ℝ v) (k : Fin r) :
    rectMatMulVec (realOrthonormalDiagonalFactor u (fun _ => 1) v) (fun j => v k j) =
      fun i => u k i := by
  ext i
  unfold rectMatMulVec realOrthonormalDiagonalFactor
  simp only [one_mul]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  calc
    (∑ a : Fin r, ∑ j : Fin n, u a i*v a j*v k j) =
        ∑ a : Fin r, u a i*(∑ j : Fin n, v a j*v k j) := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      ring
    _ = u k i := by simp [orthonormal_coordinate_inner v hv]

/-- An actual SVD partial isometry attains the canonical nuclear norm. -/
theorem exists_realMatrixNuclearNorm_partialIsometry {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) :
    ∃ W : Matrix (Fin m) (Fin n) ℝ, IsRealMatrixPartialIsometry W ∧
      realMatrixOperatorNorm W ≤ 1 ∧ realMatrixTracePairing W A = realMatrixNuclearNorm A := by
  obtain ⟨r,s,u,v,h⟩ := exists_isRealMatrixSVD A
  let W := realOrthonormalDiagonalFactor u (fun _ => 1) v
  have hunit : ∀ k : Fin r,
      realMatrixTracePairing W (realRankOneMatrix (fun i => u k i) (fun j => v k j)) = 1 := by
    intro k
    rw [realMatrixTracePairing_rankOne, partialIsometry_action u v h.rightSingularVectors_orthonormal k]
    simpa using orthonormal_coordinate_inner u h.leftSingularVectors_orthonormal k k
  refine ⟨W,⟨r,u,v,h.leftSingularVectors_orthonormal,h.rightSingularVectors_orthonormal,rfl⟩,?_,?_⟩
  · apply realMatrixOperatorNorm_le_of_rectOpNorm2Le W (by norm_num)
    intro x
    exact realOrthonormalDiagonalFactor_vecNorm2_le u (fun _ => 1) v
      h.leftSingularVectors_orthonormal h.rightSingularVectors_orthonormal
      (by norm_num) (fun _ => by norm_num) (fun _ => le_rfl) x
  · conv_lhs => rw [h.eq_sum_rankOne]
    rw [realMatrixTracePairing_sum_right, h.nuclearNorm_eq_sum_rank]
    simp only [realMatrixTracePairing_smul_right, hunit, mul_one]

/-- Attainment over the actual Euclidean operator unit ball. -/
theorem exists_realMatrixNuclearNorm_dual {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) :
    ∃ W : Matrix (Fin m) (Fin n) ℝ,
      realMatrixOperatorNorm W ≤ 1 ∧ realMatrixTracePairing W A = realMatrixNuclearNorm A := by
  obtain ⟨W,_,hW,hpair⟩ := exists_realMatrixNuclearNorm_partialIsometry A
  exact ⟨W,hW,hpair⟩


/-- Dual unit-ball characterization derived from the attained SVD witness. -/
theorem realMatrixNuclearNorm_le_iff {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (c : ℝ) :
    realMatrixNuclearNorm A ≤ c ↔ ∀ W : Matrix (Fin m) (Fin n) ℝ,
      realMatrixOperatorNorm W ≤ 1 → |realMatrixTracePairing W A| ≤ c := by
  constructor
  · intro h W hW
    exact (abs_realMatrixTracePairing_le_operatorNorm_mul_nuclearNorm W A).trans
      ((mul_le_of_le_one_left (realMatrixNuclearNorm_nonneg A) hW).trans h)
  · intro h
    obtain ⟨W,hW,hpair⟩ := exists_realMatrixNuclearNorm_dual A
    simpa [hpair, abs_of_nonneg (realMatrixNuclearNorm_nonneg A)] using h W hW

@[simp] theorem realMatrixNuclearNorm_zero {m n : ℕ} :
    realMatrixNuclearNorm (0 : Matrix (Fin m) (Fin n) ℝ) = 0 := by
  apply le_antisymm _ (realMatrixNuclearNorm_nonneg _)
  apply (realMatrixNuclearNorm_le_iff _ _).2
  intro W hW
  simp [realMatrixTracePairing]

theorem realMatrixNuclearNorm_add_le {m n : ℕ} (A B : Matrix (Fin m) (Fin n) ℝ) :
    realMatrixNuclearNorm (A+B) ≤ realMatrixNuclearNorm A+realMatrixNuclearNorm B := by
  apply (realMatrixNuclearNorm_le_iff _ _).2
  intro W hW
  rw [realMatrixTracePairing_add_right]
  exact (abs_add_le _ _).trans (add_le_add
    ((realMatrixNuclearNorm_le_iff A _).1 le_rfl W hW)
    ((realMatrixNuclearNorm_le_iff B _).1 le_rfl W hW))

@[simp] theorem realMatrixNuclearNorm_smul {m n : ℕ}
    (t : ℝ) (A : Matrix (Fin m) (Fin n) ℝ) :
    realMatrixNuclearNorm (t • A) = |t| * realMatrixNuclearNorm A := by
  apply le_antisymm
  · apply (realMatrixNuclearNorm_le_iff _ _).2
    intro W hW
    rw [realMatrixTracePairing_smul_right, abs_mul]
    exact mul_le_mul_of_nonneg_left
      ((realMatrixNuclearNorm_le_iff A _).1 le_rfl W hW) (abs_nonneg t)
  · obtain ⟨W,hW,hpair⟩ := exists_realMatrixNuclearNorm_dual A
    have hb := (realMatrixNuclearNorm_le_iff (t • A) _).1 le_rfl W hW
    simpa [realMatrixTracePairing_smul_right, hpair, abs_mul,
      abs_of_nonneg (realMatrixNuclearNorm_nonneg A)] using hb

theorem realMatrixNuclearNorm_sum_le {m n : ℕ} {ι : Type*} (s : Finset ι)
    (F : ι → Matrix (Fin m) (Fin n) ℝ) :
    realMatrixNuclearNorm (∑ k ∈ s, F k) ≤ ∑ k ∈ s, realMatrixNuclearNorm (F k) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert k s hk ih =>
      rw [Finset.sum_insert hk, Finset.sum_insert hk]
      exact (realMatrixNuclearNorm_add_le _ _).trans (add_le_add_right ih _)

/-- The rank-one upper bound is dimension-free, also for zero vectors/empty shapes. -/
theorem realMatrixNuclearNorm_rankOne_le {m n : ℕ} (x : Fin m → ℝ) (y : Fin n → ℝ) :
    realMatrixNuclearNorm (realRankOneMatrix x y) ≤ vecNorm2 x*vecNorm2 y := by
  apply (realMatrixNuclearNorm_le_iff _ _).2
  intro W hW
  exact (abs_realMatrixTracePairing_rankOne_le W x y).trans
    (mul_le_of_le_one_left (mul_nonneg (vecNorm2_nonneg x) (vecNorm2_nonneg y)) hW)

/-- Actual Euclidean operator norm is unchanged by rectangular transpose. -/
theorem realMatrixOperatorNorm_finiteTranspose {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) :
    realMatrixOperatorNorm (finiteTranspose A) = realMatrixOperatorNorm A := by
  have hle : ∀ {a b : ℕ} (B : Matrix (Fin a) (Fin b) ℝ),
      realMatrixOperatorNorm (finiteTranspose B) ≤ realMatrixOperatorNorm B := by
    intro a b B
    exact realMatrixOperatorNorm_le_of_rectOpNorm2Le _ (norm_nonneg _)
      (rectOpNorm2Le_finiteTranspose_of_rectOpNorm2Le B (norm_nonneg _)
        (RealMatrixOperator.rectOpNorm2Le_realMatrixOperatorNorm B))
  exact le_antisymm (hle A) (by simpa [finiteTranspose] using hle (finiteTranspose A))

theorem realMatrixOperatorNorm_rectMatMul_le {m n p : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (B : Matrix (Fin n) (Fin p) ℝ) :
    realMatrixOperatorNorm (rectMatMul A B) ≤ realMatrixOperatorNorm A*realMatrixOperatorNorm B :=
  realMatrixOperatorNorm_le_of_rectOpNorm2Le _ (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    (rectOpNorm2Le_rectMatMul A B (norm_nonneg _)
      (RealMatrixOperator.rectOpNorm2Le_realMatrixOperatorNorm A)
      (RealMatrixOperator.rectOpNorm2Le_realMatrixOperatorNorm B))

theorem realMatrixTracePairing_transpose {m n : ℕ} (W A : Matrix (Fin m) (Fin n) ℝ) :
    realMatrixTracePairing (finiteTranspose W) (finiteTranspose A) = realMatrixTracePairing W A := by
  unfold realMatrixTracePairing finiteTranspose
  exact Finset.sum_comm

@[simp] theorem realMatrixNuclearNorm_finiteTranspose {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) :
    realMatrixNuclearNorm (finiteTranspose A) = realMatrixNuclearNorm A := by
  have hle : ∀ {a b : ℕ} (B : Matrix (Fin a) (Fin b) ℝ),
      realMatrixNuclearNorm (finiteTranspose B) ≤ realMatrixNuclearNorm B := by
    intro a b B
    apply (realMatrixNuclearNorm_le_iff _ _).2
    intro W hW
    have hp : realMatrixTracePairing W (finiteTranspose B) =
        realMatrixTracePairing (finiteTranspose W) B := by
      simpa [finiteTranspose] using (realMatrixTracePairing_transpose W (finiteTranspose B)).symm
    rw [hp]
    exact (realMatrixNuclearNorm_le_iff B _).1 le_rfl _
      (by simpa [realMatrixOperatorNorm_finiteTranspose] using hW)
  exact le_antisymm (hle A) (by simpa [finiteTranspose] using hle (finiteTranspose A))

/-- Rectangular trace cyclicity for left multiplication. -/
theorem realMatrixTracePairing_rectMatMul {l m n : ℕ}
    (W : Matrix (Fin l) (Fin n) ℝ) (L : Matrix (Fin l) (Fin m) ℝ)
    (A : Matrix (Fin m) (Fin n) ℝ) :
    realMatrixTracePairing W (rectMatMul L A) =
      realMatrixTracePairing (rectMatMul (finiteTranspose L) W) A := by
  unfold realMatrixTracePairing rectMatMul finiteTranspose
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  calc
    _ = ∑ i : Fin l, ∑ k : Fin m, ∑ j : Fin n, W i j*(L i k*A k j) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.sum_comm]
    _ = ∑ k : Fin m, ∑ j : Fin n, ∑ i : Fin l, L i k*W i j*A k j := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro k hk
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j hj
      apply Finset.sum_congr rfl
      intro i hi
      ring

/-- Shape-changing left operator/nuclear ideal inequality. -/
theorem realMatrixNuclearNorm_rectMatMul_left_le {l m n : ℕ}
    (L : Matrix (Fin l) (Fin m) ℝ) (A : Matrix (Fin m) (Fin n) ℝ) :
    realMatrixNuclearNorm (rectMatMul L A) ≤ realMatrixOperatorNorm L*realMatrixNuclearNorm A := by
  apply (realMatrixNuclearNorm_le_iff _ _).2
  intro W hW
  rw [realMatrixTracePairing_rectMatMul]
  apply (abs_realMatrixTracePairing_le_operatorNorm_mul_nuclearNorm _ A).trans
  apply mul_le_mul_of_nonneg_right _ (realMatrixNuclearNorm_nonneg A)
  exact (realMatrixOperatorNorm_rectMatMul_le _ _).trans
    (by rw [realMatrixOperatorNorm_finiteTranspose];
        exact mul_le_of_le_one_right (norm_nonneg _) hW)

/-- Shape-changing right nuclear/operator ideal inequality. -/
theorem realMatrixNuclearNorm_rectMatMul_right_le {m n p : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (R : Matrix (Fin n) (Fin p) ℝ) :
    realMatrixNuclearNorm (rectMatMul A R) ≤ realMatrixNuclearNorm A*realMatrixOperatorNorm R := by
  have ht : finiteTranspose (rectMatMul A R) =
      rectMatMul (finiteTranspose R) (finiteTranspose A) := by
    ext i j
    simp only [finiteTranspose, rectMatMul]
    apply Finset.sum_congr rfl
    intro k hk
    ring
  calc
    _ = realMatrixNuclearNorm (finiteTranspose (rectMatMul A R)) :=
      (realMatrixNuclearNorm_finiteTranspose _).symm
    _ = _ := congrArg realMatrixNuclearNorm ht
    _ ≤ _ := realMatrixNuclearNorm_rectMatMul_left_le _ _
    _ = _ := by rw [realMatrixOperatorNorm_finiteTranspose, realMatrixNuclearNorm_finiteTranspose]; ring


/-- Rank-one action has the exact dimension-free Euclidean operator cap. -/
theorem realMatrixOperatorNorm_rankOne_le {m n : ℕ} (x : Fin m → ℝ) (y : Fin n → ℝ) :
    realMatrixOperatorNorm (realRankOneMatrix x y) ≤ vecNorm2 x*vecNorm2 y := by
  apply realMatrixOperatorNorm_le_of_rectOpNorm2Le _
    (mul_nonneg (vecNorm2_nonneg x) (vecNorm2_nonneg y))
  intro z
  have ha : rectMatMulVec (realRankOneMatrix x y) z =
      fun i => (∑ j : Fin n, y j*z j)*x i := by
    ext i
    simp only [rectMatMulVec, realRankOneMatrix, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [ha, vecNorm2_smul]
  calc
    _ ≤ (vecNorm2 y*vecNorm2 z)*vecNorm2 x :=
      mul_le_mul_of_nonneg_right (abs_vecInnerProduct_le_vecNorm2_mul y z) (vecNorm2_nonneg x)
    _ = _ := by ring

/-- Exact rank-one nuclear norm, including zero vectors and empty dimensions. -/
@[simp] theorem realMatrixNuclearNorm_rankOne {m n : ℕ} (x : Fin m → ℝ) (y : Fin n → ℝ) :
    realMatrixNuclearNorm (realRankOneMatrix x y) = vecNorm2 x*vecNorm2 y := by
  apply le_antisymm (realMatrixNuclearNorm_rankOne_le x y)
  let c := vecNorm2 x*vecNorm2 y
  have hc : 0 ≤ c := mul_nonneg (vecNorm2_nonneg x) (vecNorm2_nonneg y)
  by_cases hz : c=0
  · simpa [c, hz] using realMatrixNuclearNorm_nonneg (realRankOneMatrix x y)
  have hp : realMatrixTracePairing (realRankOneMatrix x y) (realRankOneMatrix x y) = c^2 := by
    unfold realMatrixTracePairing realRankOneMatrix c
    rw [mul_pow, vecNorm2_sq, vecNorm2_sq]
    unfold vecNorm2Sq
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  have hb := abs_realMatrixTracePairing_le_operatorNorm_mul_nuclearNorm
    (realRankOneMatrix x y) (realRankOneMatrix x y)
  rw [hp, abs_of_nonneg (sq_nonneg c)] at hb
  have hb2 := hb.trans (mul_le_mul_of_nonneg_right (realMatrixOperatorNorm_rankOne_le x y)
    (realMatrixNuclearNorm_nonneg (realRankOneMatrix x y)))
  have hpos : 0<c := lt_of_le_of_ne hc (Ne.symm hz)
  change c ≤ _
  nlinarith

/-- Literal decomposition into individual columns; no approximation is introduced. -/
theorem realMatrix_eq_sum_columns {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) :
    A = ∑ j : Fin n, realRankOneMatrix (fun i => A i j) (fun k => if k=j then 1 else 0) := by
  ext i k
  simp [Matrix.sum_apply, realRankOneMatrix]

/-- Nuclear residual bound by the sum of actual Euclidean column norms. -/
theorem realMatrixNuclearNorm_le_sum_column_norms {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) :
    realMatrixNuclearNorm A ≤ ∑ j : Fin n, vecNorm2 (fun i => A i j) := by
  calc
    _ = realMatrixNuclearNorm
        (∑ j : Fin n, realRankOneMatrix (fun i => A i j) (fun k => if k=j then 1 else 0)) :=
      congrArg realMatrixNuclearNorm (realMatrix_eq_sum_columns A)
    _ ≤ _ := realMatrixNuclearNorm_sum_le _ _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [realMatrixNuclearNorm_rankOne]
      have hu : vecNorm2 (fun k : Fin n => if k=j then (1:ℝ) else 0)=1 := by
        simp [vecNorm2, vecNorm2Sq]
      rw [hu, mul_one]

@[simp] theorem realMatrixNuclearNorm_empty_source {m : ℕ} (A : Matrix (Fin m) (Fin 0) ℝ) :
    realMatrixNuclearNorm A=0 := by simp [realMatrixNuclearNorm]

@[simp] theorem realMatrixNuclearNorm_empty_target {n : ℕ} (A : Matrix (Fin 0) (Fin n) ℝ) :
    realMatrixNuclearNorm A=0 := by
  apply le_antisymm _ (realMatrixNuclearNorm_nonneg _)
  simpa [vecNorm2, vecNorm2Sq] using realMatrixNuclearNorm_le_sum_column_norms A

/-- Entrywise column-residual budget, with no dimension loss beyond summing the columns. -/
theorem realMatrixNuclearNorm_le_sum_column_budgets {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin n → ℝ)
    (h : ∀ j, vecNorm2 (fun i => A i j) ≤ b j) :
    realMatrixNuclearNorm A ≤ ∑ j, b j :=
  (realMatrixNuclearNorm_le_sum_column_norms A).trans (Finset.sum_le_sum (fun j _ => h j))


/-- Definiteness follows from coordinate trace tests, with no rank/shape restriction. -/
@[simp] theorem realMatrixNuclearNorm_eq_zero_iff {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) : realMatrixNuclearNorm A=0 ↔ A=0 := by
  constructor
  · intro hz
    ext i j
    let W := realRankOneMatrix (fun k : Fin m => if k=i then (1:ℝ) else 0)
      (fun k : Fin n => if k=j then (1:ℝ) else 0)
    have hb := abs_realMatrixTracePairing_le_operatorNorm_mul_nuclearNorm W A
    have hp : realMatrixTracePairing W A=A i j := by
      simp [W, realMatrixTracePairing, realRankOneMatrix]
    rw [hz, mul_zero, hp] at hb
    exact abs_nonpos_iff.mp hb
  · intro hz
    rw [hz, realMatrixNuclearNorm_zero]

/-- The operator norm is bounded by the canonical nuclear sum. -/
theorem realMatrixOperatorNorm_le_nuclearNorm {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) : realMatrixOperatorNorm A ≤ realMatrixNuclearNorm A := by
  obtain ⟨r,s,u,v,h⟩ := exists_isRealMatrixSVD A
  have hA : A=realOrthonormalDiagonalFactor u (fun k => s (Fin.castLE h.rank_le_width k)) v := by
    ext i j
    exact h.reconstruction i j
  apply realMatrixOperatorNorm_le_of_rectOpNorm2Le _ (realMatrixNuclearNorm_nonneg A)
  intro x
  conv_lhs => rw [hA]
  apply realOrthonormalDiagonalFactor_vecNorm2_le u _ v
    h.leftSingularVectors_orthonormal h.rightSingularVectors_orthonormal
    (realMatrixNuclearNorm_nonneg A) (fun k => h.singularValues_nonnegative _) _ x
  intro k
  rw [h.nuclearNorm_eq_sum_rank]
  exact Finset.single_le_sum (fun a _ => h.singularValues_nonnegative _) (Finset.mem_univ k)

/-- Full rectangular two-sided ideal bound. -/
theorem realMatrixNuclearNorm_rectMatMul_both_le {l m n p : ℕ}
    (L : Matrix (Fin l) (Fin m) ℝ) (A : Matrix (Fin m) (Fin n) ℝ)
    (R : Matrix (Fin n) (Fin p) ℝ) :
    realMatrixNuclearNorm (rectMatMul (rectMatMul L A) R) ≤
      realMatrixOperatorNorm L*realMatrixNuclearNorm A*realMatrixOperatorNorm R :=
  (realMatrixNuclearNorm_rectMatMul_right_le _ _).trans
    (mul_le_mul_of_nonneg_right (realMatrixNuclearNorm_rectMatMul_left_le L A) (norm_nonneg _))

end
end NumStability
