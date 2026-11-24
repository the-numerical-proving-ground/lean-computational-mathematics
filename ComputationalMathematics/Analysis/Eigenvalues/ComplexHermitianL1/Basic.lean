import ComputationalMathematics.Analysis.Eigenvalues.ComplexHermitianL1.Defs
import Mathlib.Analysis.InnerProductSpace.Trace
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Tactic

namespace NumStability.ComplexHermitianL1

open Matrix Unitary
open scoped BigOperators ComplexOrder
noncomputable section

private def basis {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsHermitian) :=
  (Matrix.isHermitian_iff_isSymmetric.mp hA).eigenvectorBasis finrank_euclideanSpace_fin

private theorem eig_antitone {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsHermitian) :
    Antitone (complexOrderedEigenvalue hA) :=
  (Matrix.isHermitian_iff_isSymmetric.mp hA).eigenvalues_antitone finrank_euclideanSpace_fin

private def rayleigh {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (x : EuclideanSpace ℂ (Fin n)) : ℝ := Complex.re (inner ℂ x (A.toEuclideanLin x))

private theorem rayleigh_eq_sum {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsHermitian)
    (x : EuclideanSpace ℂ (Fin n)) :
    rayleigh A x = ∑ a, complexOrderedEigenvalue hA a * ‖(basis hA).repr x a‖ ^ 2 := by
  let b := basis hA
  let T := A.toEuclideanLin
  have he : inner ℂ x (T x) = ∑ a : Fin n, inner ℂ x (b a) * inner ℂ (b a) (T x) :=
    (OrthonormalBasis.sum_inner_mul_inner b x (T x)).symm
  change Complex.re (inner ℂ x (T x)) = _
  rw [he]
  change Complex.reCLM (∑ a : Fin n, _) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  have hcoord := (Matrix.isHermitian_iff_isSymmetric.mp hA).eigenvectorBasis_apply_self_apply
    finrank_euclideanSpace_fin x i
  change b.repr (T x) i = (complexOrderedEigenvalue hA i : ℂ) * b.repr x i at hcoord
  rw [← b.repr_apply_apply, hcoord, ← inner_conj_symm, ← b.repr_apply_apply]
  rw [mul_left_comm, mul_comm ((starRingEnd ℂ) _), Complex.mul_conj, Complex.normSq_eq_norm_sq]
  simp [pow_two, Complex.mul_re, b]

private def lead {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsHermitian) (i : Fin n) :
    Submodule ℂ (EuclideanSpace ℂ (Fin n)) :=
  Submodule.span ℂ (⇑(basis hA) '' (↑(Finset.Iic i) : Set (Fin n)))

private def trail {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsHermitian) (i : Fin n) :
    Submodule ℂ (EuclideanSpace ℂ (Fin n)) :=
  Submodule.span ℂ (⇑(basis hA) '' (↑(Finset.Ici i) : Set (Fin n)))

private theorem hermitian_repr_eq_zero_of_mem_span {n : ℕ}
    (b : OrthonormalBasis (Fin n) ℂ (EuclideanSpace ℂ (Fin n)))
    (s : Set (Fin n)) {x : EuclideanSpace ℂ (Fin n)}
    (hx : x ∈ Submodule.span ℂ (b '' s)) {j : Fin n} (hj : j ∉ s) :
    b.repr x j = 0 := by
  rw [OrthonormalBasis.repr_apply_apply]
  refine Submodule.span_induction (p := fun y _ => inner ℂ (b j) y = 0) ?_ ?_ ?_ ?_ hx
  · rintro y ⟨l, hl, rfl⟩
    have hjl : j ≠ l := by rintro rfl; exact hj hl
    rw [orthonormal_iff_ite.mp b.orthonormal j l]
    simp [hjl]
  · change inner ℂ (b j) 0 = 0
    rw [inner_zero_right]
  · intro u v _ _ ihu ihv
    rw [inner_add_right, ihu, ihv, add_zero]
  · intro a u _ ih
    rw [inner_smul_right, ih, mul_zero]

private theorem hermitian_sum_repr_sq {n : ℕ}
    (b : OrthonormalBasis (Fin n) ℂ (EuclideanSpace ℂ (Fin n)))
    (x : EuclideanSpace ℂ (Fin n)) :
    ∑ j : Fin n, ‖b.repr x j‖ ^ 2 = ‖x‖ ^ 2 := by
  simpa [OrthonormalBasis.repr_apply_apply] using b.sum_sq_norm_inner_right x

/-- Every vector in the leading subspace has Rayleigh form at least the
`i`-th ordered eigenvalue times its squared norm. -/
private theorem eig_mul_norm_sq_le_rayleigh_of_mem_lead
    {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsHermitian)
    (i : Fin n) {x : EuclideanSpace ℂ (Fin n)}
    (hx : x ∈ lead hA i) :
    complexOrderedEigenvalue hA i * ‖x‖ ^ 2 ≤ rayleigh A x := by
  rw [rayleigh_eq_sum hA]
  let b := basis hA
  have hzero : ∀ j : Fin n, ¬ (j ≤ i) → b.repr x j = 0 := by
    intro j hji
    exact hermitian_repr_eq_zero_of_mem_span b _ hx (by simpa using hji)
  have hterm : ∀ j : Fin n,
      complexOrderedEigenvalue hA i * ‖b.repr x j‖ ^ 2 ≤
        complexOrderedEigenvalue hA j * ‖b.repr x j‖ ^ 2 := by
    intro j
    by_cases hji : j ≤ i
    · exact mul_le_mul_of_nonneg_right
        (eig_antitone hA hji) (sq_nonneg _)
    · rw [hzero j hji]
      simp
  calc
    complexOrderedEigenvalue hA i * ‖x‖ ^ 2 =
        complexOrderedEigenvalue hA i * ∑ j : Fin n, ‖b.repr x j‖ ^ 2 := by
      rw [hermitian_sum_repr_sq]
    _ = ∑ j : Fin n,
        complexOrderedEigenvalue hA i * ‖b.repr x j‖ ^ 2 := by
      rw [Finset.mul_sum]
    _ ≤ ∑ j : Fin n,
        complexOrderedEigenvalue hA j * ‖b.repr x j‖ ^ 2 :=
      Finset.sum_le_sum (fun j _ => hterm j)

/-- Every vector in the trailing subspace has Rayleigh form at most the
`i`-th ordered eigenvalue times its squared norm. -/
private theorem rayleigh_le_eig_mul_norm_sq_of_mem_trail
    {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsHermitian)
    (i : Fin n) {x : EuclideanSpace ℂ (Fin n)}
    (hx : x ∈ trail hA i) :
    rayleigh A x ≤ complexOrderedEigenvalue hA i * ‖x‖ ^ 2 := by
  rw [rayleigh_eq_sum hA]
  let b := basis hA
  have hzero : ∀ j : Fin n, ¬ (i ≤ j) → b.repr x j = 0 := by
    intro j hij
    exact hermitian_repr_eq_zero_of_mem_span b _ hx (by simpa using hij)
  have hterm : ∀ j : Fin n,
      complexOrderedEigenvalue hA j * ‖b.repr x j‖ ^ 2 ≤
        complexOrderedEigenvalue hA i * ‖b.repr x j‖ ^ 2 := by
    intro j
    by_cases hij : i ≤ j
    · exact mul_le_mul_of_nonneg_right
        (eig_antitone hA hij) (sq_nonneg _)
    · rw [hzero j hij]
      simp
  calc
    ∑ j : Fin n,
        complexOrderedEigenvalue hA j * ‖b.repr x j‖ ^ 2 ≤
      ∑ j : Fin n,
        complexOrderedEigenvalue hA i * ‖b.repr x j‖ ^ 2 :=
      Finset.sum_le_sum (fun j _ => hterm j)
    _ = complexOrderedEigenvalue hA i *
        ∑ j : Fin n, ‖b.repr x j‖ ^ 2 := by
      rw [Finset.mul_sum]
    _ = complexOrderedEigenvalue hA i * ‖x‖ ^ 2 := by
      rw [hermitian_sum_repr_sq]

private theorem finrank_span_orthonormalBasis_image_finset {n : ℕ}
    (b : OrthonormalBasis (Fin n) ℂ (EuclideanSpace ℂ (Fin n)))
    (s : Finset (Fin n)) :
    Module.finrank ℂ
        (Submodule.span ℂ (⇑b '' (↑s : Set (Fin n)))) = s.card := by
  classical
  have hli : LinearIndependent ℂ (fun k : {j // j ∈ s} => b (k : Fin n)) :=
    (b.orthonormal.comp (fun k : {j // j ∈ s} => (k : Fin n))
      Subtype.val_injective).linearIndependent
  have hrange : Set.range (fun k : {j // j ∈ s} => b (k : Fin n)) =
      ⇑b '' (↑s : Set (Fin n)) := by
    ext y
    constructor
    · rintro ⟨⟨l, hl⟩, rfl⟩
      exact ⟨l, Finset.mem_coe.mpr hl, rfl⟩
    · rintro ⟨l, hl, rfl⟩
      exact ⟨⟨l, Finset.mem_coe.mp hl⟩, rfl⟩
  rw [← hrange, finrank_span_eq_card hli]
  exact Fintype.card_coe s

private theorem finrank_lead {n : ℕ}
    {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsHermitian) (i : Fin n) :
    Module.finrank ℂ (lead hA i) = i.val + 1 := by
  rw [lead,
    finrank_span_orthonormalBasis_image_finset, Fin.card_Iic]

private theorem finrank_trail {n : ℕ}
    {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsHermitian) (i : Fin n) :
    Module.finrank ℂ (trail hA i) = n - i.val := by
  rw [trail,
    finrank_span_orthonormalBasis_image_finset, Fin.card_Ici]


private theorem rayleigh_le_of_psd_sub {n : ℕ} {A H : Matrix (Fin n) (Fin n) ℂ}
    (h : (H - A).PosSemidef) (x : EuclideanSpace ℂ (Fin n)) :
    rayleigh A x ≤ rayleigh H x := by
  have h0 : 0 ≤ rayleigh (H - A) x := by
    rw [rayleigh, EuclideanSpace.inner_eq_star_dotProduct, Matrix.toLpLin_apply]
    simpa only [WithLp.ofLp_toLp, dotProduct_comm] using h.re_dotProduct_nonneg x.ofLp
  have hsub : rayleigh (H - A) x = rayleigh H x - rayleigh A x := by
    simp only [rayleigh, map_sub, LinearMap.sub_apply, inner_sub_right, Complex.sub_re]
  rwa [hsub, sub_nonneg] at h0

private theorem eig_le_of_psd_sub {n : ℕ} {A H : Matrix (Fin n) (Fin n) ℂ}
    (hA : A.IsHermitian) (hH : H.IsHermitian) (h : (H - A).PosSemidef) (i : Fin n) :
    complexOrderedEigenvalue hA i ≤ complexOrderedEigenvalue hH i := by
  let E := lead hA i
  let W := trail hH i
  have hdim : Module.finrank ℂ (EuclideanSpace ℂ (Fin n)) <
      Module.finrank ℂ E + Module.finrank ℂ W := by
    rw [finrank_euclideanSpace_fin, finrank_lead, finrank_trail]
    have hi := i.isLt
    omega
  have hinf : E ⊓ W ≠ ⊥ := by
    intro hinf
    have hdisjoint : Disjoint E W := by rw [disjoint_iff_inf_le, hinf]
    exact (not_le_of_gt hdim) (Submodule.finrank_add_finrank_le_of_disjoint hdisjoint)
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hinf
  have hAx := eig_mul_norm_sq_le_rayleigh_of_mem_lead hA i hx.1
  have hHx := rayleigh_le_eig_mul_norm_sq_of_mem_trail hH i hx.2
  exact le_of_mul_le_mul_right
    (hAx.trans ((rayleigh_le_of_psd_sub h x).trans hHx)) (by positivity)

private theorem sum_eig_eq_trace_re {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ}
    (hA : A.IsHermitian) : (∑ i, complexOrderedEigenvalue hA i) = A.trace.re := by
  have h := (Matrix.isHermitian_iff_isSymmetric.mp hA).trace_eq_sum_eigenvalues
    finrank_euclideanSpace_fin
  change LinearMap.trace ℂ _ A.toEuclideanLin = ↑(∑ i, complexOrderedEigenvalue hA i) at h
  rw [LinearMap.trace_eq_matrix_trace ℂ (EuclideanSpace.basisFun (Fin n) ℂ).toBasis,
    Matrix.toEuclideanLin_eq_toLin_orthonormal, LinearMap.toMatrix_toLin] at h
  simpa using (congrArg Complex.re h).symm

private theorem trace_bound {n : ℕ} {A C H : Matrix (Fin n) (Fin n) ℂ}
    (hA : A.IsHermitian) (hC : C.IsHermitian) (hH : H.IsHermitian)
    (hAH : (H - A).PosSemidef) (hCH : (H - C).PosSemidef) :
    (∑ i, |complexOrderedEigenvalue hA i - complexOrderedEigenvalue hC i|) ≤ Complex.re (2 * H.trace - A.trace - C.trace) := by
  calc
    _ ≤ ∑ i, (2 * complexOrderedEigenvalue hH i - complexOrderedEigenvalue hA i - complexOrderedEigenvalue hC i) := by
      apply Finset.sum_le_sum
      intro i _
      have hAi := eig_le_of_psd_sub hA hH hAH i
      have hCi := eig_le_of_psd_sub hC hH hCH i
      rw [abs_le]
      constructor <;> linarith
    _ = _ := by
      rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
        sum_eig_eq_trace_re hH, sum_eig_eq_trace_re hA, sum_eig_eq_trace_re hC]
      simp [Complex.mul_re]

private theorem cfc_psd {n : ℕ} {M : Matrix (Fin n) (Fin n) ℂ}
    (hM : M.IsHermitian) (f : ℝ → ℝ) (hf : ∀ x, 0 ≤ f x) :
    (hM.cfc f).PosSemidef := by
  rw [Matrix.IsHermitian.cfc, conjStarAlgAut_apply]
  exact (Matrix.posSemidef_diagonal_iff.mpr (fun _ => by simp [hf])).mul_mul_conjTranspose_same _

private theorem trace_cfc_re {n : ℕ} {M : Matrix (Fin n) (Fin n) ℂ}
    (hM : M.IsHermitian) (f : ℝ → ℝ) :
    (hM.cfc f).trace.re = ∑ i, f (hM.eigenvalues i) := by
  rw [Matrix.IsHermitian.cfc, conjStarAlgAut_apply, Matrix.trace_mul_cycle,
    Unitary.coe_star_mul_self, one_mul, Matrix.trace_diagonal]
  simp [Function.comp_def]

private theorem parts_sub {n : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} (hM : M.IsHermitian) :
    hM.cfc (fun x => max x 0) - hM.cfc (fun x => max (-x) 0) = M := by
  conv_rhs => rw [hM.spectral_theorem]
  rw [Matrix.IsHermitian.cfc, Matrix.IsHermitian.cfc, ← map_sub, Matrix.diagonal_sub]
  apply congrArg (conjStarAlgAut ℂ _ hM.eigenvectorUnitary)
  apply congrArg Matrix.diagonal
  funext i
  change (↑(max (hM.eigenvalues i) 0) : ℂ) - ↑(max (-(hM.eigenvalues i)) 0) = ↑(hM.eigenvalues i)
  rw [← Complex.ofReal_sub]
  congr 1
  by_cases hi : 0 ≤ hM.eigenvalues i
  · simp [max_eq_left hi, max_eq_right (neg_nonpos.mpr hi)]
  · have hi' := le_of_not_ge hi
    simp [max_eq_right hi', max_eq_left (neg_nonneg.mpr hi')]

private theorem gram_eigenvalue_multiset {n : ℕ} {M : Matrix (Fin n) (Fin n) ℂ}
    (hM : M.IsHermitian) :
    Multiset.map (fun i => (Matrix.isHermitian_conjTranspose_mul_self M).eigenvalues i)
      (Finset.univ : Finset (Fin n)).val =
    Multiset.map (fun i => hM.eigenvalues i ^ 2) (Finset.univ : Finset (Fin n)).val := by
  let g := (conjStarAlgAut ℂ (Matrix (Fin n) (Fin n) ℂ)) hM.eigenvectorUnitary
  have hgram : M.conjTranspose * M =
      g (Matrix.diagonal (fun i => ((hM.eigenvalues i ^ 2 : ℝ) : ℂ))) := by
    rw [hM.eq, ← pow_two]
    nth_rw 1 [hM.spectral_theorem]
    change (g (Matrix.diagonal (RCLike.ofReal ∘ hM.eigenvalues))) ^ 2 = _
    rw [← map_pow, pow_two, Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    simp [pow_two]
  have hchar : (M.conjTranspose * M).charpoly =
      ∏ i, (Polynomial.X - Polynomial.C ((hM.eigenvalues i ^ 2 : ℝ) : ℂ)) := by
    rw [hgram]
    dsimp only [g]
    rw [conjStarAlgAut_apply, Matrix.charpoly_mul_comm, ← mul_assoc,
      Unitary.coe_star_mul_self, one_mul, Matrix.charpoly_diagonal]
  have hroots := (Matrix.isHermitian_conjTranspose_mul_self M).roots_charpoly_eq_eigenvalues
  have hprod : (∏ i : Fin n, (Polynomial.X - Polynomial.C ((hM.eigenvalues i ^ 2 : ℝ) : ℂ))) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun i _ => Polynomial.X_sub_C_ne_zero _)
  rw [hchar, Polynomial.roots_prod _ _ hprod] at hroots
  simp_rw [Polynomial.roots_X_sub_C] at hroots
  rw [Multiset.bind_singleton] at hroots
  have he := congrArg (Multiset.map Complex.re) hroots
  simpa only [Multiset.map_map, Function.comp_def, Complex.ofReal_re] using he.symm

private theorem nuclear_eq_abs {n : ℕ} {M : Matrix (Fin n) (Fin n) ℂ}
    (hM : M.IsHermitian) :
    complexNuclearNorm M = ∑ i, |hM.eigenvalues i| := by
  rw [complexNuclearNorm, trace_cfc_re]
  have h := congrArg (fun l : Multiset ℝ => (l.map Real.sqrt).sum)
    (gram_eigenvalue_multiset hM)
  simpa [Multiset.map_map, Function.comp_def, Real.sqrt_sq_eq_abs,
    Finset.sum_eq_multiset_sum] using h

/-- Ordered Hermitian eigenvalue perturbation with the exact common upper
bound and nuclear-norm trace identity, including complex Hermitian matrices. -/
theorem ordered_perturbation_trace {n : ℕ} (A C : Matrix (Fin n) (Fin n) ℂ)
    (hA : A.IsHermitian) (hC : C.IsHermitian) :
  let dp := (hA.sub hC).cfc (fun x : ℝ => max x 0)
  let dm := (hA.sub hC).cfc (fun x : ℝ => max (-x) 0)
  let H := C + dp
  A - C = dp - dm ∧ dp.PosSemidef ∧ dm.PosSemidef ∧ H = A + dm ∧
  (H - A).PosSemidef ∧ (H - C).PosSemidef ∧
    (∑ i, |complexOrderedEigenvalue hA i - complexOrderedEigenvalue hC i|) ≤
      Complex.re (2 * H.trace - A.trace - C.trace) ∧
    2 * H.trace - A.trace - C.trace = (complexNuclearNorm (A - C) : ℂ) := by
  let hM := hA.sub hC
  let dp := hM.cfc (fun x => max x 0)
  let dm := hM.cfc (fun x => max (-x) 0)
  let H := C + dp
  have hparts : dp - dm = A - C := parts_sub hM
  have hdecomp : H = A + dm := by
    dsimp only [H]
    calc
      C + dp = C + (dp - dm) + dm := by abel
      _ = A + dm := by rw [hparts]; abel
  have hdp : dp.PosSemidef := cfc_psd hM _ (fun _ => le_max_right _ _)
  have hdm : dm.PosSemidef := cfc_psd hM _ (fun _ => le_max_right _ _)
  have hHA : (H - A).PosSemidef := by
    rw [hdecomp]
    simpa only [add_sub_cancel_left] using hdm
  have hHC : (H - C).PosSemidef := by
    dsimp only [H]
    simpa only [add_sub_cancel_left] using hdp
  have hbound := trace_bound hA hC (hC.add hdp.isHermitian) hHA hHC
  refine ⟨hparts.symm, hdp, hdm, hdecomp, hHA, hHC, hbound, ?_⟩
  let T := 2 * H.trace - A.trace - C.trace
  change T = (complexNuclearNorm (A - C) : ℂ)
  have hAtrace : A.trace.im = 0 := by
    rw [hA.trace_eq_sum_eigenvalues]
    simp
  have hCtrace : C.trace.im = 0 := by
    rw [hC.trace_eq_sum_eigenvalues]
    simp
  have hHtrace : H.trace.im = 0 := by
    have hH : H.IsHermitian := hC.add hdp.isHermitian
    rw [hH.trace_eq_sum_eigenvalues]
    simp
  apply Complex.ext
  · change (2 * H.trace - A.trace - C.trace).re = complexNuclearNorm (A - C)
    rw [nuclear_eq_abs hM]
    have ht : H.trace = A.trace + dm.trace := by rw [hdecomp, Matrix.trace_add]
    have ht' : H.trace = C.trace + dp.trace := Matrix.trace_add _ _
    have hre := congrArg Complex.re ht
    have hre' := congrArg Complex.re ht'
    simp only [Complex.add_re] at hre hre'
    have h2 : (2 : ℂ).re = 2 ∧ (2 : ℂ).im = 0 := by norm_num
    simp only [Complex.sub_re, Complex.mul_re, h2.1, h2.2, zero_mul, sub_zero]
    calc
      _ = dp.trace.re + dm.trace.re := by linarith only [hre, hre']
      _ = ∑ i, |hM.eigenvalues i| := by
        rw [trace_cfc_re, trace_cfc_re, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro i _
        change max (hM.eigenvalues i) 0 + max (-hM.eigenvalues i) 0 = |hM.eigenvalues i|
        by_cases hi : 0 ≤ hM.eigenvalues i
        · simp [max_eq_left hi, max_eq_right (neg_nonpos.mpr hi), abs_of_nonneg hi]
        · have hi' := lt_of_not_ge hi
          simp [max_eq_right hi'.le, max_eq_left (neg_nonneg.mpr hi'.le), abs_of_neg hi']

  · change (2 * H.trace - A.trace - C.trace).im = 0
    simp [Complex.mul_im, hAtrace, hCtrace, hHtrace]

end
end NumStability.ComplexHermitianL1
