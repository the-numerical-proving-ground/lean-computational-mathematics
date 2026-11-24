import ComputationalMathematics.Analysis.MatrixStructure.Bipartite.MassShift
import ComputationalMathematics.Analysis.MatrixInequalities.PositiveSylvesterBound
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.Tactic.Linarith

/-!
# Parity Grams of approximate mass-shift eigenvectors

The residuals are the actual differences `T Q - Q Λ`. All matrix norms in this
file are induced Euclidean operator norms. The algebra and estimates include
empty column groups and do not use an entrywise or Frobenius estimate.
-/

open Matrix
open scoped BigOperators Matrix.Norms.L2Operator RealInnerProductSpace

namespace NumStability.Matrix.Bipartite.MassParityGrams

noncomputable section

/-- Left and right coordinate restrictions; neither restriction normalizes columns. -/
def left {n : ℕ} {ι : Type*} (Q : Matrix (Fin n ⊕ Fin n) ι ℝ) := Q.toRows₁

def right {n : ℕ} {ι : Type*} (Q : Matrix (Fin n ⊕ Fin n) ι ℝ) := Q.toRows₂

/-- Compression of the parity signature between two possibly different groups. -/
def compression {n : ℕ} {ι κ : Type*} [Fintype ι] [Fintype κ]
    (P : Matrix (Fin n ⊕ Fin n) ι ℝ) (Q : Matrix (Fin n ⊕ Fin n) κ ℝ) :=
  Pᵀ * signature n * Q

/-- The two parity Grams sum to the full cross Gram. -/
theorem gram_sum {n : ℕ} {ι κ : Type*} [Fintype ι] [Fintype κ]
    (P : Matrix (Fin n ⊕ Fin n) ι ℝ) (Q : Matrix (Fin n ⊕ Fin n) κ ℝ) :
    (left P)ᵀ * left Q + (right P)ᵀ * right Q = Pᵀ * Q := by
  conv_rhs => rw [← Matrix.fromRows_toRows P, ← Matrix.fromRows_toRows Q]
  simp only [Matrix.transpose_fromRows, Matrix.fromCols_mul_fromRows, left, right]

/-- The signature compression is the difference of the two cross Grams. -/
theorem gram_difference {n : ℕ} {ι κ : Type*} [Fintype ι] [Fintype κ]
    (P : Matrix (Fin n ⊕ Fin n) ι ℝ) (Q : Matrix (Fin n ⊕ Fin n) κ ℝ) :
    compression P Q = (left P)ᵀ * left Q - (right P)ᵀ * right Q := by
  unfold compression
  conv_lhs => rw [← Matrix.fromRows_toRows P, ← Matrix.fromRows_toRows Q]
  simp only [signature, Matrix.transpose_fromRows, Matrix.fromCols_mul_fromBlocks,
    Matrix.fromCols_mul_fromRows, Matrix.mul_one, Matrix.mul_zero, Matrix.neg_mul,
    Matrix.mul_neg, add_zero, zero_add, left, right, sub_eq_add_neg]

theorem left_gram {n : ℕ} {ι κ : Type*} [Fintype ι] [Fintype κ]
    (P : Matrix (Fin n ⊕ Fin n) ι ℝ) (Q : Matrix (Fin n ⊕ Fin n) κ ℝ) :
    (left P)ᵀ * left Q = (1 / 2 : ℝ) • (Pᵀ * Q + compression P Q) := by
  rw [gram_difference, ← gram_sum P Q]
  module

theorem right_gram {n : ℕ} {ι κ : Type*} [Fintype ι] [Fintype κ]
    (P : Matrix (Fin n ⊕ Fin n) ι ℝ) (Q : Matrix (Fin n ⊕ Fin n) κ ℝ) :
    (right P)ᵀ * right Q = (1 / 2 : ℝ) • (Pᵀ * Q - compression P Q) := by
  rw [gram_difference, ← gram_sum P Q]
  module

/-- Joint orthogonality, rather than separate normalizations, fixes the mixed Gram. -/
theorem right_cross_gram {n h l : ℕ}
    (P : Matrix (Fin n ⊕ Fin n) (Fin h) ℝ)
    (Q : Matrix (Fin n ⊕ Fin n) (Fin l) ℝ) (hPQ : Pᵀ * Q = 0) :
    (right P)ᵀ * right Q = (- (1 / 2 : ℝ)) • compression P Q := by
  rw [right_gram, hPQ, zero_sub, smul_neg, neg_smul]

/-- Rectangular compression of the same anticommutator. This also handles
cross blocks of a single jointly orthonormal extraction. -/
theorem cross_sylvester {n h l : ℕ}
    (C : Matrix (Fin n) (Fin n) ℝ) (α : ℝ)
    (P : Matrix (Fin n ⊕ Fin n) (Fin h) ℝ)
    (Q : Matrix (Fin n ⊕ Fin n) (Fin l) ℝ)
    (A : Matrix (Fin h) (Fin h) ℝ) (B : Matrix (Fin l) (Fin l) ℝ)
    (hA : A.IsSymm) :
    A * compression P Q + compression P Q * B = (2 * α) • (Pᵀ * Q) -
      (massShift C α * P - P * A)ᵀ * signature n * Q -
      Pᵀ * signature n * (massShift C α * Q - Q * B) := by
  have hcompressed : Pᵀ * massShift C α * signature n * Q +
      Pᵀ * signature n * massShift C α * Q = (2 * α) • (Pᵀ * Q) := by
    calc
      _ = Pᵀ * (massShift C α * signature n + signature n * massShift C α) * Q := by
        simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
      _ = _ := by rw [massShift_anticommutator]; simp [Matrix.mul_smul, Matrix.smul_mul]
  rw [← hcompressed]
  simp only [compression, transpose_sub, transpose_mul, massShift_transpose, hA.eq,
    Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_assoc]
  abel

private theorem norm_transpose {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (A : Matrix m n ℝ) : ‖Aᵀ‖ = ‖A‖ := by
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using Matrix.l2_opNorm_conjTranspose A

private theorem norm_one_le {ι : Type*} [Fintype ι] [DecidableEq ι] :
    ‖(1 : Matrix ι ι ℝ)‖ ≤ 1 := by
  rw [← Matrix.diagonal_one, Matrix.l2_opNorm_diagonal]
  exact (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)).2 (by intro i; simp)

/-- Orthonormal rectangular columns have norm at most one, including zero columns. -/
theorem norm_le_one_of_orthonormal {m ι : Type*} [Fintype m] [Fintype ι]
    [DecidableEq m] [DecidableEq ι] (Q : Matrix m ι ℝ) (hQ : Qᵀ * Q = 1) : ‖Q‖ ≤ 1 := by
  have h := Matrix.l2_opNorm_conjTranspose_mul_self Q
  rw [Matrix.conjTranspose_eq_transpose_of_trivial, hQ] at h
  have hi := norm_one_le (ι := ι)
  nlinarith [norm_nonneg Q]

/-- The signature itself is a Euclidean isometry, also for empty row sets. -/
theorem signature_norm_le_one (n : ℕ) : ‖signature n‖ ≤ 1 :=
  norm_le_one_of_orthonormal _ (by simp)

/-- Dimension-free compression-error estimate from the actual residual matrices. -/
theorem compression_error_norm {n h l : ℕ}
    (P : Matrix (Fin n ⊕ Fin n) (Fin h) ℝ)
    (Q : Matrix (Fin n ⊕ Fin n) (Fin l) ℝ)
    (EP : Matrix (Fin n ⊕ Fin n) (Fin h) ℝ)
    (EQ : Matrix (Fin n ⊕ Fin n) (Fin l) ℝ)
    {η : ℝ} (_hη : 0 ≤ η) (hP : Pᵀ * P = 1) (hQ : Qᵀ * Q = 1)
    (hEP : ‖EP‖ ≤ η) (hEQ : ‖EQ‖ ≤ η) :
    ‖EPᵀ * signature n * Q + Pᵀ * signature n * EQ‖ ≤ 2 * η := by
  have hnP := norm_le_one_of_orthonormal P hP
  have hnQ := norm_le_one_of_orthonormal Q hQ
  have hnJ := signature_norm_le_one n
  have h1 : ‖EPᵀ * signature n * Q‖ ≤ η := by
    calc
      _ ≤ (‖EP‖ * ‖signature n‖) * ‖Q‖ := by
        grw [Matrix.l2_opNorm_mul, Matrix.l2_opNorm_mul, norm_transpose]
      _ ≤ η := by nlinarith [norm_nonneg EP, norm_nonneg (signature n), norm_nonneg Q,
        mul_le_mul hnJ hnQ (norm_nonneg Q) (by norm_num : (0 : ℝ) ≤ 1)]
  have h2 : ‖Pᵀ * signature n * EQ‖ ≤ η := by
    calc
      _ ≤ (‖P‖ * ‖signature n‖) * ‖EQ‖ := by
        grw [Matrix.l2_opNorm_mul, Matrix.l2_opNorm_mul, norm_transpose]
      _ ≤ η := by nlinarith [norm_nonneg P, norm_nonneg (signature n), norm_nonneg EQ,
        mul_le_mul hnP hnJ (norm_nonneg (signature n)) (by norm_num : (0 : ℝ) ≤ 1)]
  exact (norm_add_le _ _).trans (by linarith)

/-- Positive assigned labels: the deviation from the exact diagonal compression
is controlled solely by the actual assigned-label residual. -/
theorem positive_deviation_norm {n k : ℕ}
    (C : Matrix (Fin n) (Fin n) ℝ) (α η : ℝ)
    (Q : Matrix (Fin n ⊕ Fin n) (Fin k) ℝ) (a : Fin k → ℝ)
    (hα : 0 < α) (hη : 0 ≤ η) (ha : ∀ i, α ≤ a i) (hQ : Qᵀ * Q = 1)
    (hE : ‖massShift C α * Q - Q * diagonal a‖ ≤ η) :
    ‖compression Q Q - diagonal (fun i => α / a i)‖ ≤ η / α := by
  let E := massShift C α * Q - Q * diagonal a
  let F := Eᵀ * signature n * Q + Qᵀ * signature n * E
  have hF : ‖F‖ ≤ 2 * η :=
    compression_error_norm Q Q E E hη hQ hQ hE hE
  have hc := compressed_sylvester C α Q (diagonal a) hQ (by simp [Matrix.IsSymm])
  change diagonal a * compression Q Q + compression Q Q * diagonal a =
    (2 * α) • 1 - Eᵀ * signature n * Q - Qᵀ * signature n * E at hc
  have hbase : diagonal a * diagonal (fun i => α / a i) +
      diagonal (fun i => α / a i) * diagonal a = (2 * α) • (1 : Matrix (Fin k) (Fin k) ℝ) := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp only [Matrix.add_apply, Matrix.mul_diagonal,
        Matrix.diagonal_apply_eq, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one]
      have hi : a i ≠ 0 := ne_of_gt (lt_of_lt_of_le hα (ha i))
      field_simp
      ring
    · simp [hij]
  have heq : diagonal a * (compression Q Q - diagonal (fun i => α / a i)) +
      (compression Q Q - diagonal (fun i => α / a i)) * diagonal a = -F := by
    rw [Matrix.mul_sub, Matrix.sub_mul]
    calc
      _ = (diagonal a * compression Q Q + compression Q Q * diagonal a) -
        (diagonal a * diagonal (fun i => α / a i) +
          diagonal (fun i => α / a i) * diagonal a) := by abel
      _ = -F := by rw [hc, hbase]; dsimp only [F]; abel
  have h := PositiveSylvesterBound.diagonal_norm_le a a
    (compression Q Q - diagonal (fun i => α / a i)) (-F) α α hα hα ha ha heq
  have hn : ‖-F‖ = ‖F‖ := norm_neg F
  rw [hn] at h
  apply h.trans
  apply (div_le_iff₀ (by positivity : 0 < α + α)).2
  have hcancel : (η / α) * (α + α) = 2 * η := by field_simp; ring
  rw [hcancel]
  exact hF

/-- Negative assigned labels retain the opposite diagonal compression. -/
theorem negative_deviation_norm {n k : ℕ}
    (C : Matrix (Fin n) (Fin n) ℝ) (α η : ℝ)
    (Q : Matrix (Fin n ⊕ Fin n) (Fin k) ℝ) (b : Fin k → ℝ)
    (hα : 0 < α) (hη : 0 ≤ η) (hb : ∀ i, α ≤ b i) (hQ : Qᵀ * Q = 1)
    (hE : ‖massShift C α * Q - Q * diagonal (fun i => -b i)‖ ≤ η) :
    ‖compression Q Q + diagonal (fun i => α / b i)‖ ≤ η / α := by
  let E := massShift C α * Q - Q * diagonal (fun i => -b i)
  let F := Eᵀ * signature n * Q + Qᵀ * signature n * E
  have hF : ‖F‖ ≤ 2 * η :=
    compression_error_norm Q Q E E hη hQ hQ hE hE
  have hc := compressed_sylvester C α Q (diagonal (fun i => -b i)) hQ (by simp [Matrix.IsSymm])
  change diagonal (fun i => -b i) * compression Q Q +
    compression Q Q * diagonal (fun i => -b i) =
    (2 * α) • 1 - Eᵀ * signature n * Q - Qᵀ * signature n * E at hc
  have heq : diagonal b * (compression Q Q + diagonal (fun i => α / b i)) +
      (compression Q Q + diagonal (fun i => α / b i)) * diagonal b = F := by
    ext i j
    have hij := congrFun (congrFun hc i) j
    simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.diagonal_mul, Matrix.mul_diagonal,
      Matrix.smul_apply, smul_eq_mul] at hij ⊢
    dsimp only [F, Matrix.add_apply]
    by_cases he : i = j
    · subst j
      simp only [Matrix.diagonal_apply_eq, Matrix.one_apply_eq] at hij ⊢
      have hi : b i ≠ 0 := ne_of_gt (lt_of_lt_of_le hα (hb i))
      have hdiv : b i * (α / b i) = α := mul_div_cancel₀ α hi
      nlinarith
    · simp only [Matrix.diagonal_apply_ne _ he, Matrix.one_apply_ne he] at hij ⊢
      nlinarith
  have h := PositiveSylvesterBound.diagonal_norm_le b b
    (compression Q Q + diagonal (fun i => α / b i)) F α α hα hα hb hb heq
  apply h.trans
  apply (div_le_iff₀ (by positivity : 0 < α + α)).2
  have hcancel : (η / α) * (α + α) = 2 * η := by field_simp; ring
  rw [hcancel]
  exact hF

/-- A created cut in the assigned magnitudes controls the mixed signature
block. No gap in the actual spectrum and no rank assumption are used. -/
theorem mixed_compression_norm {n h l : ℕ}
    (C : Matrix (Fin n) (Fin n) ℝ) (α η : ℝ)
    (P : Matrix (Fin n ⊕ Fin n) (Fin h) ℝ)
    (Q : Matrix (Fin n ⊕ Fin n) (Fin l) ℝ)
    (a : Fin h → ℝ) (b : Fin l → ℝ) (alo bhi gap : ℝ)
    (hη : 0 ≤ η) (hP : Pᵀ * P = 1) (hQ : Qᵀ * Q = 1)
    (hPQ : Pᵀ * Q = 0) (hgap : 0 < gap) (hsep : gap ≤ alo - bhi)
    (ha : ∀ i, alo ≤ a i) (hb : ∀ j, b j ≤ bhi)
    (hEP : ‖massShift C α * P - P * diagonal a‖ ≤ η)
    (hEQ : ‖massShift C α * Q - Q * diagonal (fun j => -b j)‖ ≤ η) :
    ‖compression P Q‖ ≤ (2 * η) / gap := by
  let EP := massShift C α * P - P * diagonal a
  let EQ := massShift C α * Q - Q * diagonal (fun j => -b j)
  let F := EPᵀ * signature n * Q + Pᵀ * signature n * EQ
  have hF : ‖F‖ ≤ 2 * η :=
    compression_error_norm P Q EP EQ hη hP hQ hEP hEQ
  have hc := cross_sylvester C α P Q (diagonal a) (diagonal (fun j => -b j))
    (by simp [Matrix.IsSymm])
  rw [hPQ, smul_zero] at hc
  have heq : diagonal a * compression P Q - compression P Q * diagonal b = -F := by
    simpa only [F, EP, EQ, ← Matrix.diagonal_neg, Matrix.mul_neg,
      sub_eq_add_neg, neg_neg, neg_add, zero_add] using hc
  have h := PositiveSylvesterBound.separated_diagonal_norm_le a b (compression P Q) (-F)
    alo bhi gap hgap hsep ha hb heq
  have hn : ‖-F‖ = ‖F‖ := norm_neg F
  rw [hn] at h
  exact h.trans (div_le_div_of_nonneg_right hF hgap.le)

/-- The full mixed column array is the actual concatenation of the two right
parities. Its domain has dimension `h+l`, represented by the finite sum. -/
def mixedRight {n h l : ℕ}
    (P : Matrix (Fin n ⊕ Fin n) (Fin h) ℝ)
    (Q : Matrix (Fin n ⊕ Fin n) (Fin l) ℝ) : Matrix (Fin n) (Fin h ⊕ Fin l) ℝ :=
  Matrix.fromCols (right P) (right Q)

private theorem gram_half_diag {k : ℕ} (d : Fin k → ℝ) :
    (1 / 2 : ℝ) • ((1 : Matrix (Fin k) (Fin k) ℝ) + diagonal d) =
      diagonal (fun i => (1 + d i) / 2) := by
  rw [← Matrix.diagonal_one, Matrix.diagonal_add, ← Matrix.diagonal_smul]
  congr 1
  funext i
  change (1 / 2 : ℝ) * (1 + d i) = _
  ring

/-- The raw left Gram of positive columns has the positive diagonal model. -/
theorem positive_left_gram_deviation {n k : ℕ}
    (C : Matrix (Fin n) (Fin n) ℝ) (α η : ℝ)
    (Q : Matrix (Fin n ⊕ Fin n) (Fin k) ℝ) (a : Fin k → ℝ)
    (hα : 0 < α) (hη : 0 ≤ η) (ha : ∀ i, α ≤ a i) (hQ : Qᵀ * Q = 1)
    (hE : ‖massShift C α * Q - Q * diagonal a‖ ≤ η) :
    ‖(left Q)ᵀ * left Q - diagonal (fun i => (1 + α / a i) / 2)‖ ≤ η / (2 * α) := by
  rw [left_gram, hQ, ← gram_half_diag, ← smul_sub]
  have he : 1 + compression Q Q - (1 + diagonal (fun i => α / a i)) =
      compression Q Q - diagonal (fun i => α / a i) := by abel
  rw [he, norm_smul]
  norm_num [Real.norm_eq_abs]
  rw [mul_comm (2 : ℝ) α, div_mul_eq_div_div]
  exact (mul_le_mul_of_nonneg_left
    (positive_deviation_norm C α η Q a hα hη ha hQ hE) (by norm_num)).trans_eq (by ring)

/-- The raw right Gram of positive columns has the negative diagonal model. -/
theorem positive_right_gram_deviation {n k : ℕ}
    (C : Matrix (Fin n) (Fin n) ℝ) (α η : ℝ)
    (Q : Matrix (Fin n ⊕ Fin n) (Fin k) ℝ) (a : Fin k → ℝ)
    (hα : 0 < α) (hη : 0 ≤ η) (ha : ∀ i, α ≤ a i) (hQ : Qᵀ * Q = 1)
    (hE : ‖massShift C α * Q - Q * diagonal a‖ ≤ η) :
    ‖(right Q)ᵀ * right Q - diagonal (fun i => (1 - α / a i) / 2)‖ ≤ η / (2 * α) := by
  simp only [sub_eq_add_neg (1 : ℝ)]
  rw [right_gram, hQ, ← gram_half_diag, ← smul_sub, ← Matrix.diagonal_neg]
  have he : 1 - compression Q Q - (1 + -diagonal (fun i => α / a i)) =
      -(compression Q Q - diagonal (fun i => α / a i)) := by abel
  rw [he, norm_smul, norm_neg]
  norm_num [Real.norm_eq_abs]
  rw [mul_comm (2 : ℝ) α, div_mul_eq_div_div]
  exact (mul_le_mul_of_nonneg_left
    (positive_deviation_norm C α η Q a hα hη ha hQ hE) (by norm_num)).trans_eq (by ring)

/-- The raw right Gram of negative columns has the positive diagonal model. -/
theorem negative_right_gram_deviation {n k : ℕ}
    (C : Matrix (Fin n) (Fin n) ℝ) (α η : ℝ)
    (Q : Matrix (Fin n ⊕ Fin n) (Fin k) ℝ) (b : Fin k → ℝ)
    (hα : 0 < α) (hη : 0 ≤ η) (hb : ∀ i, α ≤ b i) (hQ : Qᵀ * Q = 1)
    (hE : ‖massShift C α * Q - Q * diagonal (fun i => -b i)‖ ≤ η) :
    ‖(right Q)ᵀ * right Q - diagonal (fun i => (1 + α / b i) / 2)‖ ≤ η / (2 * α) := by
  rw [right_gram, hQ, ← gram_half_diag, ← smul_sub]
  have he : 1 - compression Q Q - (1 + diagonal (fun i => α / b i)) =
      -(compression Q Q + diagonal (fun i => α / b i)) := by abel
  rw [he, norm_smul, norm_neg]
  norm_num [Real.norm_eq_abs]
  rw [mul_comm (2 : ℝ) α, div_mul_eq_div_div]
  exact (mul_le_mul_of_nonneg_left
    (negative_deviation_norm C α η Q b hα hη hb hQ hE) (by norm_num)).trans_eq (by ring)

private theorem norm_fromBlocks_diagonal_le {h l : ℕ}
    (A : Matrix (Fin h) (Fin h) ℝ) (B : Matrix (Fin l) (Fin l) ℝ) {c : ℝ}
    (hc : 0 ≤ c) (hA : ‖A‖ ≤ c) (hB : ‖B‖ ≤ c) :
    ‖fromBlocks A 0 0 B‖ ≤ c := by
  rw [Matrix.cstar_norm_def]
  apply ContinuousLinearMap.opNorm_le_bound _ hc
  intro z
  let x : EuclideanSpace ℝ (Fin h) := WithLp.toLp 2 (fun i => z (Sum.inl i))
  let y : EuclideanSpace ℝ (Fin l) := WithLp.toLp 2 (fun j => z (Sum.inr j))
  have hz : ‖z‖ ^ 2 = ‖x‖ ^ 2 + ‖y‖ ^ 2 := by
    simp [EuclideanSpace.norm_sq_eq, Fintype.sum_sum_type, x, y]
  have hw : ‖Matrix.toEuclideanCLM (n := Fin h ⊕ Fin l) (𝕜 := ℝ) (fromBlocks A 0 0 B) z‖ ^ 2 =
      ‖Matrix.toEuclideanCLM (n := Fin h) (𝕜 := ℝ) A x‖ ^ 2 + ‖Matrix.toEuclideanCLM (n := Fin l) (𝕜 := ℝ) B y‖ ^ 2 := by
    simp [EuclideanSpace.norm_sq_eq, Fintype.sum_sum_type, Matrix.ofLp_toEuclideanCLM,
      Matrix.fromBlocks_mulVec, x, y, Function.comp_def]
  have hx : ‖Matrix.toEuclideanCLM (n := Fin h) (𝕜 := ℝ) A x‖ ≤ c * ‖x‖ :=
    ((Matrix.toEuclideanCLM (n := Fin h) (𝕜 := ℝ) A).le_opNorm x).trans (mul_le_mul_of_nonneg_right hA (norm_nonneg _))
  have hy : ‖Matrix.toEuclideanCLM (n := Fin l) (𝕜 := ℝ) B y‖ ≤ c * ‖y‖ :=
    ((Matrix.toEuclideanCLM (n := Fin l) (𝕜 := ℝ) B).le_opNorm y).trans (mul_le_mul_of_nonneg_right hB (norm_nonneg _))
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hc (norm_nonneg _))).1
  rw [hw, mul_pow, hz, mul_add, ← mul_pow, ← mul_pow]
  exact add_le_add
    ((sq_le_sq₀ (norm_nonneg _) (mul_nonneg hc (norm_nonneg _))).2 hx)
    ((sq_le_sq₀ (norm_nonneg _) (mul_nonneg hc (norm_nonneg _))).2 hy)

private theorem norm_fromBlocks_offdiag_le {h l : ℕ} (A : Matrix (Fin h) (Fin l) ℝ) :
    ‖fromBlocks 0 A Aᵀ 0‖ ≤ ‖A‖ := by
  let F := fromBlocks 0 A Aᵀ 0
  have h := Matrix.l2_opNorm_conjTranspose_mul_self F
  rw [Matrix.conjTranspose_eq_transpose_of_trivial] at h
  have he : Fᵀ * F = fromBlocks (A * Aᵀ) 0 0 (Aᵀ * A) := by
    simp [F, Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply]
  rw [he] at h
  have hprod := norm_fromBlocks_diagonal_le (A * Aᵀ) (Aᵀ * A)
    (mul_nonneg (norm_nonneg A) (norm_nonneg A))
    (by simpa only [norm_transpose] using Matrix.l2_opNorm_mul A Aᵀ)
    (by simpa only [norm_transpose] using Matrix.l2_opNorm_mul Aᵀ A)
  change ‖F‖ ≤ ‖A‖
  nlinarith [norm_nonneg F, norm_nonneg A]

/-- The diagonal-block errors and the mixed cross Gram give the total error
of the raw right Gram, with columns grouped high before low. -/
theorem mixedRight_gram_deviation {n h l : ℕ}
    (C : Matrix (Fin n) (Fin n) ℝ) (α η : ℝ)
    (P : Matrix (Fin n ⊕ Fin n) (Fin h) ℝ)
    (Q : Matrix (Fin n ⊕ Fin n) (Fin l) ℝ)
    (a : Fin h → ℝ) (b : Fin l → ℝ) (alo bhi gap : ℝ)
    (hα : 0 < α) (hη : 0 ≤ η) (hP : Pᵀ * P = 1) (hQ : Qᵀ * Q = 1)
    (hPQ : Pᵀ * Q = 0) (hgap : 0 < gap) (hsep : gap ≤ alo - bhi)
    (ha : ∀ i, alo ≤ a i) (hb : ∀ j, b j ≤ bhi)
    (haα : ∀ i, α ≤ a i) (hbα : ∀ j, α ≤ b j)
    (hEP : ‖massShift C α * P - P * diagonal a‖ ≤ η)
    (hEQ : ‖massShift C α * Q - Q * diagonal (fun j => -b j)‖ ≤ η) :
    ‖(mixedRight P Q)ᵀ * mixedRight P Q -
      diagonal (Sum.elim (fun i => (1 - α / a i) / 2) (fun j => (1 + α / b j) / 2))‖ ≤
        η / (2 * α) + η / gap := by
  let dP := fun i => (1 - α / a i) / 2
  let dQ := fun j => (1 + α / b j) / 2
  let F := (right P)ᵀ * right P - diagonal dP
  let G := (right Q)ᵀ * right Q - diagonal dQ
  let K := (right P)ᵀ * right Q
  have hK : ‖K‖ ≤ η / gap := by
    dsimp only [K]
    rw [right_cross_gram P Q hPQ, norm_smul]
    norm_num [Real.norm_eq_abs]
    rw [← show (1 / 2 : ℝ) * ((2 * η) / gap) = η / gap by ring]
    exact mul_le_mul_of_nonneg_left
      (mixed_compression_norm C α η P Q a b alo bhi gap hη hP hQ hPQ
        hgap hsep ha hb hEP hEQ) (by norm_num)
  have hF := positive_right_gram_deviation C α η P a hα hη haα hP hEP
  have hG := negative_right_gram_deviation C α η Q b hα hη hbα hQ hEQ
  have he : (mixedRight P Q)ᵀ * mixedRight P Q - diagonal (Sum.elim dP dQ) =
      fromBlocks F 0 0 G + fromBlocks 0 K Kᵀ 0 := by
    rw [mixedRight, Matrix.transpose_fromCols, Matrix.fromRows_mul_fromCols,
      ← Matrix.fromBlocks_diagonal, Matrix.fromBlocks_add]
    ext (i | i) (j | j) <;> simp [F, G, K, Matrix.transpose_mul, Matrix.diagonal_apply]
  rw [he]
  exact (norm_add_le _ _).trans (add_le_add
    (norm_fromBlocks_diagonal_le F G (by positivity) hF hG)
    ((norm_fromBlocks_offdiag_le K).trans hK))

/-- An unchanged selection from one common extraction witness. -/
def columns {m : Type*} {r k : ℕ} (W : Matrix m (Fin r) ℝ) (e : Fin k → Fin r) :=
  W.submatrix id e

/-- Cross orthogonality is inherited from the common witness. -/
theorem columns_cross_gram {m : Type*} [Fintype m] {r h l : ℕ}
    (W : Matrix m (Fin r) ℝ) (hW : Wᵀ * W = 1)
    (e : Fin h → Fin r) (f : Fin l → Fin r) :
    (columns W e)ᵀ * columns W f = (1 : Matrix (Fin r) (Fin r) ℝ).submatrix e f := by
  ext i j
  change (Wᵀ * W) (e i) (f j) = (1 : Matrix (Fin r) (Fin r) ℝ) (e i) (f j)
  rw [hW]

theorem columns_orthonormal {m : Type*} [Fintype m] {r k : ℕ}
    (W : Matrix m (Fin r) ℝ) (hW : Wᵀ * W = 1) (e : Fin k ↪ Fin r) :
    (columns W e)ᵀ * columns W e = 1 := by
  rw [columns_cross_gram W hW, Matrix.submatrix_one e e.injective]

theorem columns_cross_zero {m : Type*} [Fintype m] {r h l : ℕ}
    (W : Matrix m (Fin r) ℝ) (hW : Wᵀ * W = 1)
    (e : Fin h → Fin r) (f : Fin l → Fin r) (hef : ∀ i j, e i ≠ f j) :
    (columns W e)ᵀ * columns W f = 0 := by
  rw [columns_cross_gram W hW]
  ext i j
  simp [hef i j]

/-- Restricting columns is a contraction for the induced Euclidean norm. -/
theorem columns_norm_le {m : Type*} [Fintype m] [DecidableEq m] {r k : ℕ}
    (R : Matrix m (Fin r) ℝ) (e : Fin k ↪ Fin r) : ‖columns R e‖ ≤ ‖R‖ := by
  let V : Matrix (Fin r) (Fin k) ℝ := columns 1 e
  have hV : Vᵀ * V = 1 := columns_orthonormal 1 (by simp) e
  have hnV := norm_le_one_of_orthonormal V hV
  have heq : columns R e = R * V := by
    simpa only [V, columns, Equiv.coe_refl, Function.id_comp] using
      (Matrix.mul_submatrix_one (Equiv.refl (Fin r)) e R).symm
  rw [heq]
  exact (Matrix.l2_opNorm_mul R V).trans (by nlinarith [norm_nonneg R])

/-- The residual of selected assigned-label columns is the selection of the
actual full residual, rather than an assumed output certificate. -/
theorem residual_columns {m : Type*} [Fintype m] [DecidableEq m] {r k : ℕ}
    (T : Matrix m m ℝ) (W : Matrix m (Fin r) ℝ) (labels : Fin r → ℝ) (e : Fin k → Fin r) :
    T * columns W e - columns W e * diagonal (labels ∘ e) =
      columns (T * W - W * diagonal labels) e := by
  let V : Matrix (Fin r) (Fin k) ℝ := columns 1 e
  have heq (R : Matrix m (Fin r) ℝ) : columns R e = R * V := by
    simpa only [V, columns, Equiv.coe_refl, Function.id_comp] using
      (Matrix.mul_submatrix_one (Equiv.refl (Fin r)) e R).symm
  have hdiag : diagonal labels * V = V * diagonal (labels ∘ e) := by
    ext i j
    simp only [Matrix.diagonal_mul, Matrix.mul_diagonal]
    by_cases hi : i = e j
    · subst i; simp [V, columns, Matrix.submatrix_apply]; ring
    · simp [V, columns, hi]
  rw [heq, heq, Matrix.sub_mul]
  simp only [Matrix.mul_assoc, hdiag]

/-- Coordinate restriction is a contraction; this is the actual Euclidean
operator norm, without any nonempty-domain assumption. -/
theorem parity_norm_le {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Q : Matrix (Fin n ⊕ Fin n) ι ℝ) : ‖left Q‖ ≤ ‖Q‖ ∧ ‖right Q‖ ≤ ‖Q‖ := by
  let L : Matrix (Fin n) (Fin n ⊕ Fin n) ℝ := Matrix.fromCols 1 0
  let R : Matrix (Fin n) (Fin n ⊕ Fin n) ℝ := Matrix.fromCols 0 1
  have hL : L * Lᵀ = 1 := by
    simp [L, Matrix.transpose_fromCols, Matrix.fromCols_mul_fromRows]
  have hR : R * Rᵀ = 1 := by
    simp [R, Matrix.transpose_fromCols, Matrix.fromCols_mul_fromRows]
  have hnL : ‖L‖ ≤ 1 := by
    rw [← norm_transpose L]
    exact norm_le_one_of_orthonormal Lᵀ (by simpa using hL)
  have hnR : ‖R‖ ≤ 1 := by
    rw [← norm_transpose R]
    exact norm_le_one_of_orthonormal Rᵀ (by simpa using hR)
  have hleft : left Q = L * Q := by
    conv_rhs => rw [← Matrix.fromRows_toRows Q]
    simp only [L, Matrix.fromCols_mul_fromRows, Matrix.one_mul, Matrix.zero_mul,
      add_zero, left]
  have hright : right Q = R * Q := by
    conv_rhs => rw [← Matrix.fromRows_toRows Q]
    simp only [R, Matrix.fromCols_mul_fromRows, Matrix.one_mul, Matrix.zero_mul,
      zero_add, right]
  constructor
  · rw [hleft]
    exact (Matrix.l2_opNorm_mul L Q).trans (by nlinarith [norm_nonneg Q])
  · rw [hright]
    exact (Matrix.l2_opNorm_mul R Q).trans (by nlinarith [norm_nonneg Q])

/-- Distinct signed columns from one extraction have a bounded mixed right
array before any scaling or polar correction. -/
theorem mixedRight_norm_le_one {n h l : ℕ}
    (P : Matrix (Fin n ⊕ Fin n) (Fin h) ℝ)
    (Q : Matrix (Fin n ⊕ Fin n) (Fin l) ℝ)
    (hP : Pᵀ * P = 1) (hQ : Qᵀ * Q = 1) (hPQ : Pᵀ * Q = 0) :
    ‖mixedRight P Q‖ ≤ 1 := by
  have hQP : Qᵀ * P = 0 := by
    have ht := congrArg Matrix.transpose hPQ
    simpa only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_zero] using ht
  have hfull : (Matrix.fromCols P Q)ᵀ * Matrix.fromCols P Q = 1 := by
    rw [Matrix.transpose_fromCols, Matrix.fromRows_mul_fromCols, hP, hQ, hPQ, hQP,
      Matrix.fromBlocks_one]
  have heq : mixedRight P Q = right (Matrix.fromCols P Q) := by rfl
  rw [heq]
  exact (parity_norm_le _).2.trans (norm_le_one_of_orthonormal _ hfull)

end
end NumStability.Matrix.Bipartite.MassParityGrams
