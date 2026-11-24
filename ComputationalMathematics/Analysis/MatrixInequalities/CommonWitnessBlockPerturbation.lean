import ComputationalMathematics.Analysis.MatrixInequalities.PositiveSylvesterNuclear
import ComputationalMathematics.Analysis.MatrixInequalities.ThinPolar.Basic

/-! Exact common-witness block replacement from actual polar residuals.
The complement is represented by its orthogonal projector, so no complement
basis or matching choice is introduced. -/

namespace NumStability.CommonWitnessBlockPerturbation
noncomputable section
open Matrix MatrixPolar
open scoped BigOperators Matrix.Norms.L2Operator

/-- Actual projector onto the orthogonal complement of a thin column family. -/
def complementProjector {n k : ℕ} (Q : Matrix (Fin n) (Fin k) ℝ) :
    Matrix (Fin n) (Fin n) ℝ := 1-Q*Q.transpose

/-- Literal block replacement: selected block S, zero cross blocks, old complement. -/
def blockReplacement {n k : ℕ} (B : Matrix (Fin n) (Fin n) ℝ)
    (Q P : Matrix (Fin n) (Fin k) ℝ) (S : Matrix (Fin k) (Fin k) ℝ) :=
  Q*S*P.transpose+complementProjector Q*B*complementProjector P

theorem complementProjector_mul_thin {n k : ℕ} (Q : Matrix (Fin n) (Fin k) ℝ)
    (hQ : Q.transpose*Q=1) : complementProjector Q*Q=0 := by
  simp [complementProjector, Matrix.sub_mul, Matrix.mul_assoc, hQ]

theorem thin_transpose_mul_complementProjector {n k : ℕ} (Q : Matrix (Fin n) (Fin k) ℝ)
    (hQ : Q.transpose*Q=1) : Q.transpose*complementProjector Q=0 := by
  simp [complementProjector, Matrix.mul_sub, ← Matrix.mul_assoc, hQ]

theorem complementProjector_transpose {n k : ℕ} (Q : Matrix (Fin n) (Fin k) ℝ) :
    (complementProjector Q).transpose=complementProjector Q := by
  simp [complementProjector, Matrix.transpose_mul]

theorem operatorNorm_complementProjector_le_one {n k : ℕ} (Q : Matrix (Fin n) (Fin k) ℝ)
    (hQ : Q.transpose*Q=1) : realMatrixOperatorNorm (complementProjector Q)≤1 := by
  let E := complementProjector Q
  have hE : E*E=E := by
    dsimp [E, complementProjector]
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one]
    have hprod : Q*Q.transpose*(Q*Q.transpose)=Q*Q.transpose := by
      simp [Matrix.mul_assoc, ← Matrix.mul_assoc Q.transpose Q Q.transpose, hQ]
    rw [hprod]
    abel
  apply realMatrixOperatorNorm_le_of_rectOpNorm2Le _ (by norm_num)
  intro x
  have hs : IsSymmetricFiniteMatrix E := by
    intro i j
    exact congrFun (congrFun (complementProjector_transpose Q) j) i
  have hi : ∀ i j, finiteMatMul E E i j=E i j := by
    intro i j
    exact congrFun (congrFun hE i) j
  simpa only [one_mul, finiteVecNorm2, vecNorm2, finiteVecNorm2Sq, vecNorm2Sq,
    finiteMatVec, rectMatMulVec] using
    finiteVecNorm2_finiteMatVec_le_of_symmetric_idempotent E hs hi x

/-- The replacement has both selected paired equations, with the SAME S. -/
theorem blockReplacement_paired {n k : ℕ} (B : Matrix (Fin n) (Fin n) ℝ)
    (Q P : Matrix (Fin n) (Fin k) ℝ) (S : Matrix (Fin k) (Fin k) ℝ)
    (hQ : Q.transpose*Q=1) (hP : P.transpose*P=1) (hS : S.transpose=S) :
    blockReplacement B Q P S*P=Q*S ∧ (blockReplacement B Q P S).transpose*Q=P*S := by
  constructor
  · simp only [blockReplacement, Matrix.add_mul, Matrix.mul_assoc]
    rw [hP, complementProjector_mul_thin P hP]
    simp
  · simp only [blockReplacement, Matrix.transpose_add, Matrix.transpose_mul,
      Matrix.transpose_transpose, complementProjector_transpose, hS,
      Matrix.add_mul, Matrix.mul_assoc]
    rw [hQ, complementProjector_mul_thin Q hQ]
    simp

/-- The two cross blocks are literally zero. -/
theorem blockReplacement_cross_blocks_zero {n k : ℕ} (B : Matrix (Fin n) (Fin n) ℝ)
    (Q P : Matrix (Fin n) (Fin k) ℝ) (S : Matrix (Fin k) (Fin k) ℝ)
    (hQ : Q.transpose*Q=1) (hP : P.transpose*P=1) :
    complementProjector Q*blockReplacement B Q P S*P=0 ∧
      Q.transpose*blockReplacement B Q P S*complementProjector P=0 := by
  constructor
  · have hp : blockReplacement B Q P S*P=Q*S := by
      simp [blockReplacement, Matrix.add_mul, Matrix.mul_assoc, hP,
        complementProjector_mul_thin P hP]
    rw [Matrix.mul_assoc, hp, ← Matrix.mul_assoc, complementProjector_mul_thin Q hQ]
    simp
  · have hq : Q.transpose*blockReplacement B Q P S=S*P.transpose := by
      simp [blockReplacement, Matrix.mul_add, ← Matrix.mul_assoc, hQ,
        thin_transpose_mul_complementProjector Q hQ]
    rw [hq, Matrix.mul_assoc, thin_transpose_mul_complementProjector P hP]
    simp

/-- The complementary block is retained exactly. -/
theorem blockReplacement_complement_unchanged {n k : ℕ} (B : Matrix (Fin n) (Fin n) ℝ)
    (Q P : Matrix (Fin n) (Fin k) ℝ) (S : Matrix (Fin k) (Fin k) ℝ)
    (hQ : Q.transpose*Q=1) (hP : P.transpose*P=1) :
    complementProjector Q*blockReplacement B Q P S*complementProjector P=
      complementProjector Q*B*complementProjector P := by
  have hi : ∀ (U : Matrix (Fin n) (Fin k) ℝ), U.transpose*U=1 →
      complementProjector U*complementProjector U=complementProjector U := by
    intro U hU
    dsimp [complementProjector]
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one]
    have hprod : U*U.transpose*(U*U.transpose)=U*U.transpose := by
      simp [Matrix.mul_assoc, ← Matrix.mul_assoc U.transpose U U.transpose, hU]
    rw [hprod]
    abel
  simp only [blockReplacement, Matrix.mul_add, Matrix.add_mul]
  have hz : complementProjector Q*(Q*S*P.transpose)*complementProjector P=0 := by
    simp [← Matrix.mul_assoc,complementProjector_mul_thin Q hQ]
  rw [hz,zero_add]
  calc
    _ = (complementProjector Q*complementProjector Q)*B*
        (complementProjector P*complementProjector P) := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [hi Q hQ,hi P hP]

/-- Actual residual algebra gives the nuclear Sylvester equation. -/
theorem residual_sylvester_identity {n k : ℕ} (B : Matrix (Fin n) (Fin n) ℝ)
    (Q P X Y : Matrix (Fin n) (Fin k) ℝ) (HX HY S : Matrix (Fin k) (Fin k) ℝ)
    (hQ : Q.transpose*Q=1) (hP : P.transpose*P=1)
    (hX : X=Q*HX) (hY : Y=P*HY) (hHX : HX.transpose=HX) (hHY : HY.transpose=HY) (hS : S.transpose=S) :
    HX*(Q.transpose*B*P-S)+(Q.transpose*B*P-S)*HY =
      Q.transpose*(B*Y-X*S)+(B.transpose*X-Y*S).transpose*P := by
  rw [hX,hY]
  simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.transpose_sub, Matrix.transpose_mul,
    Matrix.transpose_transpose, hHX, hHY, hS]
  simp only [Matrix.mul_assoc]
  simp only [← Matrix.mul_assoc, hQ, hP, Matrix.mul_one, Matrix.one_mul]
  abel


/-- Convert the retained polar quadratic floor to the actual Hermitian spectrum. -/
theorem spectrum_lower_of_quadratic_lower {k : ℕ} (H : Matrix (Fin k) (Fin k) ℝ)
    (hH : H.IsHermitian) (a : ℝ)
    (hfloor : ∀ x : Fin k → ℝ, a*vecNorm2Sq x≤finiteQuadraticForm H x) :
    spectrum ℝ H ⊆ Set.Ici a := by
  intro t ht
  rw [hH.spectrum_real_eq_range_eigenvalues] at ht
  obtain ⟨j,rfl⟩ := ht
  let v := hH.eigenvectorBasis j
  have hv : vecNorm2Sq (fun i => v i)=1 := by
    have hn := hH.eigenvectorBasis.orthonormal.norm_eq_one j
    have he : ‖v‖=vecNorm2 (fun i => v i) := by
      simp [EuclideanSpace.norm_eq, vecNorm2, vecNorm2Sq, Real.norm_eq_abs, sq_abs]
    rw [he] at hn
    rw [← vecNorm2_sq, hn]
    norm_num
  have hHv : finiteMatVec H (fun i => v i)=fun i => hH.eigenvalues j*v i := by
    simpa only [finiteMatVec, Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul]
      using hH.mulVec_eigenvectorBasis j
  have hquad : finiteQuadraticForm H (fun i => v i)=hH.eigenvalues j := by
    unfold finiteQuadraticForm
    rw [hHv]
    calc
      _ = hH.eigenvalues j*vecNorm2Sq (fun i => v i) := by
        unfold vecNorm2Sq
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ = _ := by rw [hv, mul_one]
  have hf := hfloor (fun i => v i)
  simpa [hv,hquad] using hf

private theorem hermitian_of_transpose_eq {k : ℕ} (H : Matrix (Fin k) (Fin k) ℝ)
    (h : H.transpose=H) : H.IsHermitian := by
  simpa only [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] using h

private theorem nuclearNorm_neg {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) :
    realMatrixNuclearNorm (-A)=realMatrixNuclearNorm A := by
  simpa only [neg_one_smul, abs_neg, abs_one, one_mul] using realMatrixNuclearNorm_smul (-1) A

/-- Derived leading-block residual bound; the right side is the actual R,T pair. -/
theorem leading_block_nuclear_le {n k : ℕ} (B : Matrix (Fin n) (Fin n) ℝ)
    (Q P X Y : Matrix (Fin n) (Fin k) ℝ) (HX HY S : Matrix (Fin k) (Fin k) ℝ)
    (hQ : Q.transpose*Q=1) (hP : P.transpose*P=1)
    (hX : X=Q*HX) (hY : Y=P*HY) (hHX : HX.transpose=HX) (hHY : HY.transpose=HY)
    (hS : S.transpose=S) (a b : ℝ) (ha : 0<a) (hb : 0<b)
    (hfloorX : ∀ x, a*vecNorm2Sq x≤finiteQuadraticForm HX x)
    (hfloorY : ∀ x, b*vecNorm2Sq x≤finiteQuadraticForm HY x) :
    realMatrixNuclearNorm (Q.transpose*B*P-S) ≤
      (realMatrixNuclearNorm (B*Y-X*S)+realMatrixNuclearNorm (B.transpose*X-Y*S))/(a+b) := by
  have h := PositiveSylvesterNuclear.norm_le_of_spectral_floors HX HY
    (Q.transpose*B*P-S) (Q.transpose*(B*Y-X*S)+(B.transpose*X-Y*S).transpose*P)
    a b (hermitian_of_transpose_eq HX hHX) (hermitian_of_transpose_eq HY hHY) ha hb
    (spectrum_lower_of_quadratic_lower HX (hermitian_of_transpose_eq HX hHX) a hfloorX)
    (spectrum_lower_of_quadratic_lower HY (hermitian_of_transpose_eq HY hHY) b hfloorY)
    (residual_sylvester_identity B Q P X Y HX HY S hQ hP hX hY hHX hHY hS)
  apply h.trans
  apply div_le_div_of_nonneg_right _ (add_pos ha hb).le
  apply (realMatrixNuclearNorm_add_le _ _).trans
  apply add_le_add
  · exact (realMatrixNuclearNorm_rectMatMul_left_le _ _).trans
      (mul_le_of_le_one_left (realMatrixNuclearNorm_nonneg _)
        (by simpa only [finiteTranspose, Matrix.transpose_apply] using
          (realMatrixOperatorNorm_finiteTranspose Q).le.trans (operatorNorm_thin_le_one Q hQ)))
  · apply (realMatrixNuclearNorm_rectMatMul_right_le _ _).trans
    change realMatrixNuclearNorm (finiteTranspose (B.transpose*X-Y*S))*realMatrixOperatorNorm P ≤ _
    rw [realMatrixNuclearNorm_finiteTranspose]
    exact mul_le_of_le_one_right (realMatrixNuclearNorm_nonneg _) (operatorNorm_thin_le_one P hP)

/-- The change is exactly the sum of three changed blocks, without choosing bases. -/
theorem blockReplacement_sub_decomposition {n k : ℕ} (B : Matrix (Fin n) (Fin n) ℝ)
    (Q P : Matrix (Fin n) (Fin k) ℝ) (S : Matrix (Fin k) (Fin k) ℝ) :
    blockReplacement B Q P S-B = -(Q*(Q.transpose*B*P-S)*P.transpose+
      complementProjector Q*B*P*P.transpose+Q*Q.transpose*B*complementProjector P) := by
  simp only [blockReplacement, complementProjector, Matrix.mul_sub, Matrix.sub_mul,
    Matrix.one_mul, Matrix.mul_one, Matrix.mul_assoc]
  abel

/-- The lower off-diagonal block is determined by the actual first residual. -/
theorem left_cross_residual {n k : ℕ} (B : Matrix (Fin n) (Fin n) ℝ)
    (Q P X Y : Matrix (Fin n) (Fin k) ℝ) (HX HY : Matrix (Fin k) (Fin k) ℝ)
    (S : Matrix (Fin k) (Fin k) ℝ) (hQ : Q.transpose*Q=1)
    (hX : X=Q*HX) (hY : Y=P*HY) (hInv : HY*HY⁻¹=1) :
    complementProjector Q*B*P = complementProjector Q*(B*Y-X*S)*HY⁻¹ := by
  rw [hX,hY,Matrix.mul_sub,Matrix.sub_mul]
  have hz : complementProjector Q*(Q*HX*S)*HY⁻¹=0 := by
    simp [← Matrix.mul_assoc, complementProjector_mul_thin Q hQ]
  rw [hz,sub_zero]
  simp [Matrix.mul_assoc,hInv]

/-- The upper off-diagonal block is determined by the actual second residual. -/
theorem right_cross_residual {n k : ℕ} (B : Matrix (Fin n) (Fin n) ℝ)
    (Q P X Y : Matrix (Fin n) (Fin k) ℝ) (HX HY : Matrix (Fin k) (Fin k) ℝ)
    (S : Matrix (Fin k) (Fin k) ℝ) (hP : P.transpose*P=1)
    (hX : X=Q*HX) (hY : Y=P*HY) (hHX : HX.transpose=HX)
    (hInv : HX⁻¹*HX=1) :
    Q.transpose*B*complementProjector P=HX⁻¹*(B.transpose*X-Y*S).transpose*complementProjector P := by
  rw [hX,hY]
  simp only [Matrix.transpose_sub,Matrix.transpose_mul,Matrix.transpose_transpose,hHX,
    Matrix.mul_sub,Matrix.sub_mul]
  have hz : HX⁻¹*(S.transpose*(HY.transpose*P.transpose))*complementProjector P=0 := by
    simp [Matrix.mul_assoc,thin_transpose_mul_complementProjector P hP]
  rw [hz,sub_zero]
  simp [← Matrix.mul_assoc,hInv]

private theorem operatorNorm_thin_transpose_le_one {n k : ℕ}
    (Q : Matrix (Fin n) (Fin k) ℝ) (hQ : Q.transpose*Q=1) :
    realMatrixOperatorNorm Q.transpose≤1 :=
  (realMatrixOperatorNorm_finiteTranspose Q).le.trans (operatorNorm_thin_le_one Q hQ)

private theorem nuclear_sandwich_le {l m n p : ℕ}
    (L : Matrix (Fin l) (Fin m) ℝ) (A : Matrix (Fin m) (Fin n) ℝ)
    (R : Matrix (Fin n) (Fin p) ℝ) (hL : realMatrixOperatorNorm L≤1)
    (hR : realMatrixOperatorNorm R≤1) :
    realMatrixNuclearNorm (L*A*R)≤realMatrixNuclearNorm A := by
  apply (realMatrixNuclearNorm_rectMatMul_both_le L A R).trans
  calc
    _ ≤ realMatrixNuclearNorm A*realMatrixOperatorNorm R :=
      mul_le_mul_of_nonneg_right (mul_le_of_le_one_left (realMatrixNuclearNorm_nonneg A) hL) (norm_nonneg _)
    _ ≤ _ := mul_le_of_le_one_right (realMatrixNuclearNorm_nonneg A) hR

/-- Explicit three-block nuclear budget from actual residuals and actual inverse norms. -/
theorem blockReplacement_nuclear_le {n k : ℕ} (B : Matrix (Fin n) (Fin n) ℝ)
    (Q P X Y : Matrix (Fin n) (Fin k) ℝ) (HX HY S : Matrix (Fin k) (Fin k) ℝ)
    (hQ : Q.transpose*Q=1) (hP : P.transpose*P=1)
    (hX : X=Q*HX) (hY : Y=P*HY) (hHX : HX.transpose=HX) (hHY : HY.transpose=HY)
    (hS : S.transpose=S) (a b cX cY : ℝ) (ha : 0<a) (hb : 0<b)
    (hfloorX : ∀ x, a*vecNorm2Sq x≤finiteQuadraticForm HX x)
    (hfloorY : ∀ x, b*vecNorm2Sq x≤finiteQuadraticForm HY x)
    (hInvX : HX⁻¹*HX=1) (hInvY : HY*HY⁻¹=1)
    (hInvNormX : realMatrixOperatorNorm HX⁻¹≤cX)
    (hInvNormY : realMatrixOperatorNorm HY⁻¹≤cY) :
    realMatrixNuclearNorm (blockReplacement B Q P S-B) ≤
      (realMatrixNuclearNorm (B*Y-X*S)+realMatrixNuclearNorm (B.transpose*X-Y*S))/(a+b)+
      realMatrixNuclearNorm (B*Y-X*S)*cY+cX*realMatrixNuclearNorm (B.transpose*X-Y*S) := by
  let R := B*Y-X*S
  let T := B.transpose*X-Y*S
  have hD := leading_block_nuclear_le B Q P X Y HX HY S hQ hP hX hY hHX hHY hS a b ha hb hfloorX hfloorY
  have hleading : realMatrixNuclearNorm (Q*(Q.transpose*B*P-S)*P.transpose)≤
      (realMatrixNuclearNorm R+realMatrixNuclearNorm T)/(a+b) :=
    (nuclear_sandwich_le _ _ _ (operatorNorm_thin_le_one Q hQ)
      (operatorNorm_thin_transpose_le_one P hP)).trans hD
  have hleft : realMatrixNuclearNorm (complementProjector Q*B*P*P.transpose)≤realMatrixNuclearNorm R*cY := by
    rw [left_cross_residual B Q P X Y HX HY S hQ hX hY hInvY]
    have he : complementProjector Q*R*HY⁻¹*P.transpose=
        complementProjector Q*(R*HY⁻¹)*P.transpose := by simp only [Matrix.mul_assoc]
    change realMatrixNuclearNorm (complementProjector Q*R*HY⁻¹*P.transpose)≤_
    rw [he]
    exact (nuclear_sandwich_le _ _ _ (operatorNorm_complementProjector_le_one Q hQ)
      (operatorNorm_thin_transpose_le_one P hP)).trans
      ((realMatrixNuclearNorm_rectMatMul_right_le R HY⁻¹).trans
        (mul_le_mul_of_nonneg_left hInvNormY (realMatrixNuclearNorm_nonneg R)))
  have hright : realMatrixNuclearNorm (Q*Q.transpose*B*complementProjector P)≤cX*realMatrixNuclearNorm T := by
    rw [Matrix.mul_assoc Q Q.transpose B,Matrix.mul_assoc Q (Q.transpose*B),
      right_cross_residual B Q P X Y HX HY S hP hX hY hHX hInvX]
    have he : Q*(HX⁻¹*T.transpose*complementProjector P)=Q*(HX⁻¹*T.transpose)*complementProjector P := by
      simp only [Matrix.mul_assoc]
    change realMatrixNuclearNorm (Q*(HX⁻¹*T.transpose*complementProjector P))≤_
    rw [he]
    apply (nuclear_sandwich_le _ _ _ (operatorNorm_thin_le_one Q hQ)
      (operatorNorm_complementProjector_le_one P hP)).trans
    have ht : realMatrixNuclearNorm T.transpose=realMatrixNuclearNorm T := realMatrixNuclearNorm_finiteTranspose T
    exact (realMatrixNuclearNorm_rectMatMul_left_le HX⁻¹ T.transpose).trans
      (by rw [ht]; exact mul_le_mul_of_nonneg_right hInvNormX (realMatrixNuclearNorm_nonneg T))
  rw [blockReplacement_sub_decomposition,nuclearNorm_neg]
  exact (realMatrixNuclearNorm_add_le _ _).trans (add_le_add
    ((realMatrixNuclearNorm_add_le _ _).trans (add_le_add hleading hleft)) hright)


/-- Positive quadratic floors imply the genuine matrix inverse identities,
including the empty matrix, rather than treating an inverse as a formal symbol. -/
theorem inverse_identities_of_quadratic_lower {k : ℕ}
    (H : Matrix (Fin k) (Fin k) ℝ) (hH : H.transpose=H) (a : ℝ) (ha : 0<a)
    (hfloor : ∀ x, a*vecNorm2Sq x≤finiteQuadraticForm H x) :
    H⁻¹*H=1 ∧ H*H⁻¹=1 := by
  have hs := spectrum_lower_of_quadratic_lower H (hermitian_of_transpose_eq H hH) a hfloor
  have hz : (0:ℝ)∉spectrum ℝ H := by
    intro ht
    have ht' := hs ht
    exact (not_le_of_gt ha) ht'
  have hu : IsUnit H := spectrum.isUnit_of_zero_notMem ℝ hz
  have hd : IsUnit H.det := (Matrix.isUnit_iff_isUnit_det H).mp hu
  exact ⟨Matrix.nonsing_inv_mul H hd,Matrix.mul_nonsing_inv H hd⟩

/-- Source polar floors and inverse bounds give the explicit dimension-free
three-block constant. R and T here are the literal two residual matrices. -/
theorem blockReplacement_polar_nuclear_le {n k : ℕ} (B : Matrix (Fin n) (Fin n) ℝ)
    (Q P X Y : Matrix (Fin n) (Fin k) ℝ) (HX HY S : Matrix (Fin k) (Fin k) ℝ)
    (hQ : Q.transpose*Q=1) (hP : P.transpose*P=1)
    (hX : X=Q*HX) (hY : Y=P*HY) (hHX : HX.transpose=HX) (hHY : HY.transpose=HY)
    (hS : S.transpose=S)
    (hfloorX : ∀ x, (Real.sqrt 2)⁻¹*vecNorm2Sq x≤finiteQuadraticForm HX x)
    (hfloorY : ∀ x, (Real.sqrt 2)⁻¹*vecNorm2Sq x≤finiteQuadraticForm HY x)
    (hInvNormX : realMatrixOperatorNorm HX⁻¹≤Real.sqrt 2)
    (hInvNormY : realMatrixOperatorNorm HY⁻¹≤Real.sqrt 2) :
    realMatrixNuclearNorm (blockReplacement B Q P S-B) ≤
      3*(realMatrixNuclearNorm (B*Y-X*S)+realMatrixNuclearNorm (B.transpose*X-Y*S)) := by
  have hsqrt : 0<Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hfloor : 0<(Real.sqrt 2)⁻¹ := inv_pos.mpr hsqrt
  have hIX := inverse_identities_of_quadratic_lower HX hHX _ hfloor hfloorX
  have hIY := inverse_identities_of_quadratic_lower HY hHY _ hfloor hfloorY
  have h := blockReplacement_nuclear_le B Q P X Y HX HY S hQ hP hX hY hHX hHY hS
    _ _ _ _ hfloor hfloor hfloorX hfloorY hIX.1 hIY.2 hInvNormX hInvNormY
  apply h.trans
  let r := realMatrixNuclearNorm (B*Y-X*S)
  let t := realMatrixNuclearNorm (B.transpose*X-Y*S)
  have hr : 0≤r := realMatrixNuclearNorm_nonneg _
  have ht : 0≤t := realMatrixNuclearNorm_nonneg _
  change (r+t)/((Real.sqrt 2)⁻¹+(Real.sqrt 2)⁻¹)+r*Real.sqrt 2+Real.sqrt 2*t≤3*(r+t)
  have he : (r+t)/((Real.sqrt 2)⁻¹+(Real.sqrt 2)⁻¹)+r*Real.sqrt 2+Real.sqrt 2*t=
      (3*Real.sqrt 2/2)*(r+t) := by
    field_simp
    ring
  rw [he]
  apply mul_le_mul_of_nonneg_right _ (add_nonneg hr ht)
  have hsq := Real.sq_sqrt (show (0:ℝ)≤2 by norm_num)
  nlinarith

/-- Actual retained thin-polar witnesses produce a single exact block replacement
with the same prescribed S in both paired equations and the nuclear residual budget. -/
theorem exists_blockReplacement_of_gram_bounds {n k : ℕ}
    (B : Matrix (Fin n) (Fin n) ℝ) (X Y : Matrix (Fin n) (Fin k) ℝ)
    (S : Matrix (Fin k) (Fin k) ℝ) (hS : S.transpose=S) (hkn : k≤n)
    (θX θY : ℝ) (hθX : 0≤θX) (hθY : 0≤θY) (hθXhalf : θX≤1/2) (hθYhalf : θY≤1/2)
    (hGramX : realMatrixOperatorNorm (X.transpose*X-1)≤θX)
    (hGramY : realMatrixOperatorNorm (Y.transpose*Y-1)≤θY) :
    ∃ Q P : Matrix (Fin n) (Fin k) ℝ,
      Q.transpose*Q=1 ∧ P.transpose*P=1 ∧
      X=Q*(show Matrix (Fin k) (Fin k) ℝ from rectRightGramPolarH X) ∧
      Y=P*(show Matrix (Fin k) (Fin k) ℝ from rectRightGramPolarH Y) ∧
      realMatrixOperatorNorm (X-Q)≤θX ∧ realMatrixOperatorNorm (Y-P)≤θY ∧
      blockReplacement B Q P S*P=Q*S ∧ (blockReplacement B Q P S).transpose*Q=P*S ∧
      realMatrixNuclearNorm (blockReplacement B Q P S-B) ≤
        3*(realMatrixNuclearNorm (B*Y-X*S)+realMatrixNuclearNorm (B.transpose*X-Y*S)) := by
  obtain ⟨Q,hX,hQ,hHX,_,_,hXQ,_⟩ :=
    MatrixPolar.exists_polarCompletion_of_gram_bound X hkn hθX hGramX
  obtain ⟨P,hY,hP,hHY,_,_,hYP,_⟩ :=
    MatrixPolar.exists_polarCompletion_of_gram_bound Y hkn hθY hGramY
  have hfX := MatrixPolar.polarH_lower_and_inverse_of_gram_bound X hθX hθXhalf hGramX
  have hfY := MatrixPolar.polarH_lower_and_inverse_of_gram_bound Y hθY hθYhalf hGramY
  have hpaired := blockReplacement_paired B Q P S hQ hP hS
  exact ⟨Q,P,hQ,hP,hX,hY,hXQ,hYP,hpaired.1,hpaired.2,
    blockReplacement_polar_nuclear_le B Q P X Y (rectRightGramPolarH X) (rectRightGramPolarH Y) S
      hQ hP hX hY hHX hHY hS hfX.1 hfY.1 hfX.2 hfY.2⟩

end
end NumStability.CommonWitnessBlockPerturbation
