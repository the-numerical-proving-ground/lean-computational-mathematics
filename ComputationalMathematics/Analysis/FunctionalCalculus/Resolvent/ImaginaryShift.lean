import Mathlib.Analysis.CStarAlgebra.Matrix
import ComputationalMathematics.Analysis.FunctionalCalculus.Resolvent.HermitianShift
import Mathlib.LinearAlgebra.Matrix.Trace

/-! # Imaginary shifts of Hermitian matrices -/

open Matrix WithLp
open scoped Matrix.Norms.L2Operator

namespace NumStability

namespace MatrixResolvent

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The shift whose inverse has positive imaginary part when `η > 0`. -/
def imaginaryShift (A : Matrix n n ℂ) (shift η : ℝ) : Matrix n n ℂ :=
  A - ((shift : ℂ) + (η : ℂ) * Complex.I) • 1

omit [Fintype n] [DecidableEq n] in
/-- A real symmetric matrix is Hermitian after entrywise complexification. -/
theorem isHermitian_map_ofReal {A : Matrix n n ℝ} (hA : A.IsSymm) :
    (A.map Complex.ofReal).IsHermitian := by
  ext i j
  simpa [Matrix.conjTranspose_apply, Complex.star_def] using
    congrArg Complex.ofReal (hA.apply i j)

/-- The inverse of an imaginary shift of a symmetric matrix is complex symmetric. -/
theorem isSymm_inv_imaginaryShift {A : Matrix n n ℂ} (hA : A.IsSymm) (shift η : ℝ) :
    ((imaginaryShift A shift η)⁻¹).IsSymm := by
  change Matrix.transpose ((imaginaryShift A shift η)⁻¹) = _
  rw [Matrix.transpose_nonsing_inv, imaginaryShift, Matrix.transpose_sub,
    Matrix.transpose_smul, Matrix.transpose_one, hA]

/-- The diagonal denominator in the spectral decomposition of an imaginary shift. -/
private def denominator (μ shift η : ℝ) : ℂ :=
  (μ : ℂ) - ((shift : ℂ) + (η : ℂ) * Complex.I)

private lemma denominator_im (μ shift η : ℝ) : (denominator μ shift η).im = -η := by
  simp [denominator, Complex.mul_im]

private lemma denominator_ne_zero (μ shift : ℝ) {η : ℝ} (hη : 0 < η) :
    denominator μ shift η ≠ 0 := by
  intro h
  have him := congrArg Complex.im h
  rw [denominator_im, Complex.zero_im] at him
  linarith

private lemma shift_diagonalization {A : Matrix n n ℂ} (hA : A.IsHermitian) (shift η : ℝ) :
    imaginaryShift A shift η =
      Unitary.conjStarAlgAut ℂ _ hA.eigenvectorUnitary
        (diagonal fun i => denominator (hA.eigenvalues i) shift η) := by
  let E := Unitary.conjStarAlgAut ℂ _ hA.eigenvectorUnitary
  change imaginaryShift A shift η = E _
  have hA' : A = E (diagonal fun i => (hA.eigenvalues i : ℂ)) := hA.spectral_theorem
  unfold imaginaryShift denominator
  conv_lhs => rw [hA']
  rw [← map_one E, ← map_smul E, ← map_sub, Matrix.smul_one_eq_diagonal, Matrix.diagonal_sub]

private lemma shift_mul_diagonal_inverse {A : Matrix n n ℂ} (hA : A.IsHermitian) (shift : ℝ)
    {η : ℝ} (hη : 0 < η) :
    imaginaryShift A shift η *
      Unitary.conjStarAlgAut ℂ _ hA.eigenvectorUnitary
        (diagonal fun i => (denominator (hA.eigenvalues i) shift η)⁻¹) = 1 := by
  rw [shift_diagonalization hA, ← map_mul, diagonal_mul_diagonal]
  simp_rw [mul_inv_cancel₀ (denominator_ne_zero _ _ hη)]
  rw [diagonal_one, map_one]

/-- A Hermitian matrix with a nonreal shift is invertible. -/
theorem isUnit_imaginaryShift {A : Matrix n n ℂ} (hA : A.IsHermitian) (shift : ℝ)
    {η : ℝ} (hη : 0 < η) : IsUnit (imaginaryShift A shift η) := by
  apply isUnit_sub_smul_one hA
  simpa [Complex.mul_im] using hη.ne'

/-- An imaginary-shift resolvent multiplies an eigenvector by the scalar inverse shift. -/
theorem inv_imaginaryShift_mulVec_of_eigenvector {A : Matrix n n ℂ} (hA : A.IsHermitian)
    {v : n → ℂ} {μ shift η : ℝ} (hη : 0 < η)
    (hv : A *ᵥ v = (μ : ℂ) • v) :
    (imaginaryShift A shift η)⁻¹ *ᵥ v =
      ((μ : ℂ) - ((shift : ℂ) + (η : ℂ) * Complex.I))⁻¹ • v := by
  let K := imaginaryShift A shift η
  have hKv : K *ᵥ v = denominator μ shift η • v := by
    simp only [K, imaginaryShift, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, hv,
      denominator, sub_smul]
  have hinv : K⁻¹ * K = 1 :=
    Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).1 (isUnit_imaginaryShift hA shift hη))
  have h : v = denominator μ shift η • (K⁻¹ *ᵥ v) := by
    calc
      v = K⁻¹ *ᵥ K *ᵥ v := by rw [Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec]
      _ = denominator μ shift η • (K⁻¹ *ᵥ v) := by rw [hKv, Matrix.mulVec_smul]
  change K⁻¹ *ᵥ v = (denominator μ shift η)⁻¹ • v
  conv_rhs => rw [h, smul_smul, inv_mul_cancel₀ (denominator_ne_zero μ shift hη), one_smul]

private lemma inverse_diagonalization {A : Matrix n n ℂ} (hA : A.IsHermitian) (shift : ℝ)
    {η : ℝ} (hη : 0 < η) :
    (imaginaryShift A shift η)⁻¹ =
      Unitary.conjStarAlgAut ℂ _ hA.eigenvectorUnitary
        (diagonal fun i => (denominator (hA.eigenvalues i) shift η)⁻¹) :=
  Matrix.inv_eq_right_inv (shift_mul_diagonal_inverse hA shift hη)

set_option backward.isDefEq.respectTransparency false in
private lemma norm_conj_diagonal (U : unitary (Matrix n n ℂ)) (d : n → ℂ) :
    ‖Unitary.conjStarAlgAut ℂ _ U (diagonal d)‖ = ‖d‖ := by
  rw [Unitary.conjStarAlgAut_apply, ← Unitary.coe_star, CStarRing.norm_mul_coe_unitary,
    CStarRing.norm_coe_unitary_mul, Matrix.l2_opNorm_diagonal]

/-- The Euclidean operator norm of the resolvent is at most the reciprocal shift height. -/
theorem norm_inv_imaginaryShift_le {A : Matrix n n ℂ} (hA : A.IsHermitian) (shift : ℝ)
    {η : ℝ} (hη : 0 < η) : ‖(imaginaryShift A shift η)⁻¹‖ ≤ η⁻¹ := by
  rw [inverse_diagonalization hA shift hη, norm_conj_diagonal]
  refine (pi_norm_le_iff_of_nonneg (inv_nonneg.mpr hη.le)).2 fun i => ?_
  rw [norm_inv]
  apply inv_anti₀ hη
  simpa [denominator_im, abs_of_pos hη] using
    Complex.abs_im_le_norm (denominator (hA.eigenvalues i) shift η)

/-- The positive imaginary-part identity for the inverse of an imaginary shift. -/
theorem imaginaryPart_inv_imaginaryShift {A : Matrix n n ℂ} (hA : A.IsHermitian) (shift : ℝ)
    {η : ℝ} (hη : 0 < η) :
    let G := (imaginaryShift A shift η)⁻¹
    (2 * Complex.I : ℂ)⁻¹ • (G - Gᴴ) = (η : ℂ) • (Gᴴ * G) := by
  let K := imaginaryShift A shift η
  let G := K⁻¹
  change (2 * Complex.I : ℂ)⁻¹ • (G - Gᴴ) = (η : ℂ) • (Gᴴ * G)
  have hK := isUnit_imaginaryShift hA shift hη
  have hKG : K * G = 1 := K.mul_nonsing_inv ((Matrix.isUnit_iff_isUnit_det _).1 hK)
  have hGK : Gᴴ * Kᴴ = 1 := by
    have h := congrArg Matrix.conjTranspose hKG
    simpa only [Matrix.conjTranspose_mul, Matrix.conjTranspose_one] using h
  have hshift : Kᴴ - K = (2 * Complex.I * (η : ℂ)) • (1 : Matrix n n ℂ) := by
    change (imaginaryShift A shift η)ᴴ - imaginaryShift A shift η = _
    rw [imaginaryShift, Matrix.conjTranspose_sub, Matrix.conjTranspose_smul, hA,
      Matrix.conjTranspose_one, sub_sub_sub_cancel_left, ← sub_smul]
    congr 1
    simp only [Complex.star_def, map_add, map_mul, Complex.conj_ofReal, Complex.conj_I]
    ring
  rw [show G - Gᴴ = Gᴴ * (Kᴴ - K) * G by
    rw [Matrix.mul_sub, Matrix.sub_mul, hGK, Matrix.one_mul, Matrix.mul_assoc Gᴴ K G,
      hKG, Matrix.mul_one], hshift, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
    smul_smul, inv_mul_cancel_left₀ (mul_ne_zero two_ne_zero Complex.I_ne_zero)]

private lemma inverse_denominator_im (μ shift η : ℝ) :
    ((denominator μ shift η)⁻¹).im = η / ((μ - shift)^2 + η^2) := by
  rw [Complex.inv_im, denominator_im, neg_neg, Complex.normSq_apply]
  have hre : (denominator μ shift η).re = μ - shift := by
    simp [denominator, Complex.mul_re]
  rw [hre, denominator_im]
  congr 1
  ring

/-- Size and phase of the target resolvent coefficient within one shift height. -/
theorem inv_imaginaryShift_scalar_bounds {μ shift η : ℝ} (hη : 0 < η)
    (hnear : |shift - μ| ≤ η) :
    let d := ((μ : ℂ) - ((shift : ℂ) + (η : ℂ) * Complex.I))⁻¹
    (2 * η)⁻¹ ≤ d.im ∧ d.im ≤ η⁻¹ ∧ ‖d‖ ≤ Real.sqrt 2 * d.im := by
  let t := denominator μ shift η
  have hnorm : Complex.normSq t = (μ - shift)^2 + η^2 := by
    have hre : t.re = μ - shift := by simp [t, denominator, Complex.mul_re]
    rw [Complex.normSq_apply, hre, show t.im = -η from denominator_im μ shift η]
    ring
  have hηsq : 0 < Complex.normSq t := Complex.normSq_pos.mpr (denominator_ne_zero μ shift hη)
  have hμsq : (μ - shift)^2 ≤ η^2 := by
    rw [show μ - shift = -(shift - μ) by ring, neg_sq, ← sq_abs (shift - μ)]
    exact (sq_le_sq₀ (abs_nonneg _) hη.le).2 hnear
  change (2 * η)⁻¹ ≤ (t⁻¹).im ∧ (t⁻¹).im ≤ η⁻¹ ∧ ‖t⁻¹‖ ≤ Real.sqrt 2 * (t⁻¹).im
  rw [Complex.inv_im, show t.im = -η from denominator_im μ shift η, neg_neg]
  constructor
  · rw [inv_eq_one_div (2 * η), div_le_div_iff₀ (by positivity) hηsq, hnorm]
    nlinarith
  constructor
  · rw [inv_eq_one_div η, div_le_div_iff₀ hηsq hη, hnorm]
    nlinarith [sq_nonneg (μ - shift)]
  · rw [norm_inv, ← mul_div_assoc, inv_eq_one_div ‖t‖, div_le_div_iff₀
      (norm_pos_iff.2 (denominator_ne_zero μ shift hη)) hηsq, ← Complex.sq_norm, one_mul]
    have hn : ‖t‖ ≤ Real.sqrt 2 * η := by
      apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
      rw [Complex.sq_norm, hnorm, mul_pow, Real.sq_sqrt (by norm_num : 0 ≤ (2 : ℝ))]
      linarith
    nlinarith [mul_le_mul_of_nonneg_right hn (norm_nonneg t)]

/-- Each diagonal imaginary score is a nonnegative weighted sum of scalar Poisson kernels. -/
theorem inv_imaginaryShift_diagonal_im_eq_sum {A : Matrix n n ℂ} (hA : A.IsHermitian)
    (shift : ℝ) {η : ℝ} (hη : 0 < η) (r : n) :
    ((imaginaryShift A shift η)⁻¹ r r).im =
      ∑ i, Complex.normSq (hA.eigenvectorUnitary r i) *
        (η / ((hA.eigenvalues i - shift)^2 + η^2)) := by
  rw [inverse_diagonalization hA shift hη, Unitary.conjStarAlgAut_apply,
    Matrix.mul_apply, Complex.im_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.mul_diagonal, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply]
  have hmul (u d : ℂ) : u * d * star u = (Complex.normSq u : ℂ) * d := by
    rw [mul_right_comm, Complex.star_def, Complex.mul_conj]
  rw [hmul, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero,
    inverse_denominator_im]

/-- Some diagonal imaginary score is at least `1 / (2 n η)` when an eigenvalue
lies within the shift height of the real center. -/
theorem exists_inv_imaginaryShift_diagonal_im_ge {A : Matrix n n ℂ}
    (hA : A.IsHermitian) (shift : ℝ) {η : ℝ} (hη : 0 < η) (j : n)
    (hnear : |shift - hA.eigenvalues j| ≤ η) :
    ∃ r, (2 * (Fintype.card n : ℝ) * η)⁻¹ ≤ ((imaginaryShift A shift η)⁻¹ r r).im := by
  let G := (imaginaryShift A shift η)⁻¹
  let d : n → ℂ := fun i => (denominator (hA.eigenvalues i) shift η)⁻¹
  have htrace : G.trace = ∑ i, d i := by
    change ((imaginaryShift A shift η)⁻¹).trace = _
    rw [inverse_diagonalization hA shift hη, Unitary.conjStarAlgAut_apply]
    change ((↑hA.eigenvectorUnitary : Matrix n n ℂ) * diagonal d *
      star (↑hA.eigenvectorUnitary : Matrix n n ℂ)).trace = _
    rw [Matrix.trace_mul_cycle, Unitary.coe_star_mul_self, Matrix.one_mul,
      Matrix.trace_diagonal]
  have himtrace : ∑ r, (G r r).im = ∑ i, (d i).im := by
    simpa only [Matrix.trace, Matrix.diag_apply, Complex.im_sum] using congrArg Complex.im htrace
  have hdiag : ∀ i, (d i).im = η / ((hA.eigenvalues i - shift)^2 + η^2) :=
    fun i => inverse_denominator_im _ _ _
  have hterm : (2 * η)⁻¹ ≤ (d j).im := by
    rw [hdiag]
    have hpos : 0 < (hA.eigenvalues j - shift)^2 + η^2 := by positivity
    have hsq : (hA.eigenvalues j - shift)^2 ≤ η^2 := by
      have h := (sq_le_sq₀ (abs_nonneg _) hη.le).2 hnear
      rw [sq_abs] at h
      linarith [show (hA.eigenvalues j - shift)^2 = (shift - hA.eigenvalues j)^2 by ring]
    rw [inv_eq_one_div, div_le_div_iff₀ (by positivity) hpos]
    nlinarith
  have hsum : (2 * η)⁻¹ ≤ ∑ r, (G r r).im := by
    rw [himtrace]
    refine hterm.trans (Finset.single_le_sum (f := fun i => (d i).im) (fun i _ => ?_) (Finset.mem_univ j))
    change 0 ≤ (d i).im
    rw [hdiag]
    positivity
  haveI : Nonempty n := ⟨j⟩
  have hcard : 0 < (Fintype.card n : ℝ) := by exact_mod_cast Fintype.card_pos
  have hconst : ∑ _ : n, (2 * (Fintype.card n : ℝ) * η)⁻¹ = (2 * η)⁻¹ := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    field_simp
  obtain ⟨r, _, hr⟩ := Finset.exists_le_of_sum_le Finset.univ_nonempty (hconst.symm ▸ hsum)
  exact ⟨r, hr⟩

/-- The orthogonal projection onto the complement of a chosen Hermitian eigenbasis vector. -/
noncomputable def eigenvectorComplement {A : Matrix n n ℂ} (hA : A.IsHermitian) (j : n) :
    Matrix n n ℂ :=
  Unitary.conjStarAlgAut ℂ _ hA.eigenvectorUnitary (diagonal fun i => if i = j then 0 else 1)

/-- In standard coordinates the complementary projection is `I - v vᴴ`. -/
theorem eigenvectorComplement_eq_sub_vecMulVec {A : Matrix n n ℂ} (hA : A.IsHermitian)
    (j : n) :
    let v : n → ℂ := hA.eigenvectorBasis j
    eigenvectorComplement hA j = 1 - Matrix.vecMulVec v (star v) := by
  let v : n → ℂ := hA.eigenvectorBasis j
  let U := hA.eigenvectorUnitary
  let E := Unitary.conjStarAlgAut ℂ _ U
  have hdiag : diagonal (fun i => if i = j then (0 : ℂ) else 1) = 1 - Matrix.single j j 1 := by
    rw [← Matrix.diagonal_single, ← Matrix.diagonal_one, Matrix.diagonal_sub]
    congr 1
    funext i
    by_cases hi : i = j <;> simp [Pi.single_apply, hi]
  have hsingle : E (Matrix.single j j 1) = Matrix.vecMulVec v (star v) := by
    rw [Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose]
    ext i k
    rw [Matrix.mul_assoc, Matrix.mul_apply, Finset.sum_eq_single j]
    · rw [Matrix.single_mul_apply_same, Matrix.vecMulVec_apply]
      simp [U, v, Matrix.conjTranspose_apply]
    · intro l _ hl
      rw [Matrix.single_mul_apply_of_ne 1 _ _ _ _ hl, mul_zero]
    · simp
  change E _ = _
  rw [hdiag, map_sub, map_one, hsingle]

/-- The complement is independent of the normalized eigenvector chosen for a simple eigenvalue. -/
theorem eigenvectorComplement_eq_of_unit_eigenvector {A : Matrix n n ℂ} (hA : A.IsHermitian)
    (j : n) (u : EuclideanSpace ℂ n) (hu : ‖u‖ = 1)
    (heig : A *ᵥ u.ofLp = (hA.eigenvalues j : ℂ) • u.ofLp)
    (hsep : ∀ i ≠ j, hA.eigenvalues i ≠ hA.eigenvalues j) :
    eigenvectorComplement hA j = 1 - Matrix.vecMulVec u.ofLp (star u.ofLp) := by
  let U := hA.eigenvectorUnitary
  let V : Matrix n n ℂ := U
  let D := diagonal fun i => (hA.eigenvalues i : ℂ)
  let v : n → ℂ := hA.eigenvectorBasis j
  let w := star V *ᵥ u.ofLp
  have hV : star V * A * V = D := by
    simpa only [U, V, D, Unitary.conjStarAlgAut_star_apply] using
      hA.conjStarAlgAut_star_eigenvectorUnitary
  have hVstarV : star V * V = 1 := Unitary.coe_star_mul_self U
  have hVVstar : V * star V = 1 := Unitary.coe_mul_star_self U
  have hcomm : D * star V = star V * A := by
    rw [← hV, Matrix.mul_assoc (star V * A), hVVstar, Matrix.mul_one]
  have hdiag : D *ᵥ w = (hA.eigenvalues j : ℂ) • w := by
    rw [show w = star V *ᵥ u.ofLp from rfl, Matrix.mulVec_mulVec, hcomm,
      ← Matrix.mulVec_mulVec, heig, Matrix.mulVec_smul]
  have hwzero (i : n) (hi : i ≠ j) : w i = 0 := by
    have h := congrFun hdiag i
    simp only [D, Matrix.mulVec_diagonal, Pi.smul_apply, smul_eq_mul] at h
    have hprod : ((hA.eigenvalues i : ℂ) - (hA.eigenvalues j : ℂ)) * w i = 0 := by
      rw [sub_mul, sub_eq_zero.mpr h]
    exact (mul_eq_zero.mp hprod).resolve_left (sub_ne_zero.mpr (by exact_mod_cast hsep i hi))
  have hw : w = w j • (Pi.single j (1 : ℂ) : n → ℂ) := by
    funext i
    by_cases hi : i = j
    · simp [hi]
    · simp [hi, hwzero i hi]
  have hvu : u.ofLp = w j • v := by
    calc
      u.ofLp = V *ᵥ w := by rw [show w = star V *ᵥ u.ofLp from rfl, Matrix.mulVec_mulVec,
        hVVstar, Matrix.one_mulVec]
      _ = w j • v := by
        nth_rw 1 [hw]
        rw [Matrix.mulVec_smul, hA.eigenvectorUnitary_mulVec]
  have hc : ‖w j‖ = 1 := by
    have h := congrArg (fun x => ‖toLp 2 x‖) hvu
    change ‖u‖ = ‖toLp 2 (w j • v)‖ at h
    rw [WithLp.toLp_smul, norm_smul] at h
    change ‖u‖ = ‖w j‖ * ‖hA.eigenvectorBasis j‖ at h
    rw [hu, hA.eigenvectorBasis.orthonormal.1 j, mul_one] at h
    exact h.symm
  have hconj : w j * star (w j) = 1 := by
    rw [Complex.star_def, Complex.mul_conj, ← Complex.sq_norm, hc]
    norm_num
  rw [eigenvectorComplement_eq_sub_vecMulVec, hvu]
  congr 1
  ext i k
  simp only [Matrix.vecMulVec_apply, Pi.smul_apply, smul_eq_mul, Pi.star_apply, StarMul.star_mul]
  calc
    v i * star (v k) = (w j * star (w j)) * (v i * star (v k)) := by rw [hconj, one_mul]
    _ = (w j * v i) * (star (v k) * star (w j)) := by ring

private lemma norm_inv_denominator_le {μ shift η Δ : ℝ} (hΔ : 0 < Δ) (hηgap : η ≤ Δ / 2)
    (hnear : |shift - μ| ≤ η) (μ' : ℝ) (hgap : Δ ≤ |μ' - μ|) :
    ‖(denominator μ' shift η)⁻¹‖ ≤ 2 / Δ := by
  have hnorm : Δ / 2 ≤ ‖denominator μ' shift η‖ := by
    have hadd : μ' - μ = (μ' - shift) + (shift - μ) := by ring
    have htri := abs_add_le (μ' - shift) (shift - μ)
    rw [← hadd] at htri
    have hre : (denominator μ' shift η).re = μ' - shift := by
      simp [denominator, Complex.mul_re]
    have h := Complex.abs_re_le_norm (denominator μ' shift η)
    rw [hre] at h
    linarith
  rw [norm_inv, ← inv_div]
  exact inv_anti₀ (by positivity) hnorm

/-- The complex resolvent and its Hermitian imaginary part restricted to the complement
of the target eigenvector. The bounds express the additional filtering by the imaginary part. -/
theorem norm_eigenvectorComplement_mul_inv_imaginaryShift_le {A : Matrix n n ℂ}
    (hA : A.IsHermitian) (j : n) {shift η Δ : ℝ} (hη : 0 < η) (hΔ : 0 < Δ)
    (hηgap : η ≤ Δ / 2) (hnear : |shift - hA.eigenvalues j| ≤ η)
    (hgap : ∀ i ≠ j, Δ ≤ |hA.eigenvalues i - hA.eigenvalues j|) :
    let G := (imaginaryShift A shift η)⁻¹
    let P := eigenvectorComplement hA j
    ‖P * G‖ ≤ 2 / Δ ∧ ‖P * ((2 * Complex.I : ℂ)⁻¹ • (G - Gᴴ))‖ ≤ 4 * η / Δ^2 := by
  let G := (imaginaryShift A shift η)⁻¹
  let P := eigenvectorComplement hA j
  let E := Unitary.conjStarAlgAut ℂ _ hA.eigenvectorUnitary
  let d : n → ℂ := fun i => (denominator (hA.eigenvalues i) shift η)⁻¹
  let p : n → ℂ := fun i => if i = j then 0 else 1
  have hG : G = E (diagonal d) := inverse_diagonalization hA shift hη
  have hGstar : Gᴴ = E (diagonal fun i => star (d i)) := by
    change star G = _
    rw [hG, ← map_star]
    congr 1
    exact Matrix.diagonal_conjTranspose d
  have hP : P = E (diagonal p) := rfl
  have hbound (i : n) (hi : i ≠ j) : ‖d i‖ ≤ 2 / Δ :=
    norm_inv_denominator_le hΔ hηgap hnear _ (hgap i hi)
  change ‖P * G‖ ≤ _ ∧ ‖P * ((2 * Complex.I : ℂ)⁻¹ • (G - Gᴴ))‖ ≤ _
  constructor
  · rw [hP, hG, ← map_mul, Matrix.diagonal_mul_diagonal, norm_conj_diagonal]
    refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
    by_cases hi : i = j
    · simpa [p, hi] using (show 0 ≤ 2 / Δ by positivity)
    · simpa [p, hi] using hbound i hi
  · rw [show (2 * Complex.I : ℂ)⁻¹ • (G - Gᴴ) = (η : ℂ) • (Gᴴ * G) from
      imaginaryPart_inv_imaginaryShift hA shift hη]
    rw [hP, hGstar, hG, Matrix.mul_smul, ← map_mul, ← map_mul,
      Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal, norm_smul, norm_conj_diagonal,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos hη]
    calc
      _ ≤ η * (2 / Δ)^2 := by
        refine mul_le_mul_of_nonneg_left ((pi_norm_le_iff_of_nonneg (sq_nonneg _)).2
          fun i => ?_) hη.le
        by_cases hi : i = j
        · simpa [p, hi] using (sq_nonneg (2 / Δ))
        · simp only [p, hi, if_false, one_mul, norm_mul, norm_star, ← pow_two]
          exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).2 (hbound i hi)
      _ = 4 * η / Δ^2 := by ring

end MatrixResolvent

end NumStability
