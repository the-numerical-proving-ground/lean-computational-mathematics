import ComputationalMathematics.Analysis.InnerProductSpace.OrthonormalBasis.PrescribedSlots
import ComputationalMathematics.Analysis.SingularValues.FullRealSVD.Basic
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.Tactic

/-!
# Exact selected/complementary singular blocks

Selected pairs are retained at injective prescribed slots. An ordered complement
is formed in the original ambient indices, and the actual complementary block
is decomposed using the full canonical ascending SVD. The combined list is not
asserted to be globally ordered, nor are prescribed slots identified as true
singular ranks. No nuclear matching or clipping estimate occurs here.
-/

namespace NumStability.CommonWitnessBlocks

open scoped BigOperators RealInnerProductSpace
noncomputable section
open Classical

def complementSet {n k} (I : Fin k ↪ Fin n) : Finset (Fin n) :=
  (Finset.univ.map I)ᶜ

theorem complementSet_card {n k} (I : Fin k ↪ Fin n) :
    (complementSet I).card = n-k := by simp [complementSet, Finset.card_compl]

/-- Increasing enumeration of every unused ambient slot. -/
def orderedComplement {n k} (I : Fin k ↪ Fin n) : Fin (n-k) ↪o Fin n :=
  (complementSet I).orderEmbOfFin (complementSet_card I)

theorem orderedComplement_disjoint {n k} (I : Fin k ↪ Fin n) (i : Fin k) (j : Fin (n-k)) :
    I i ≠ orderedComplement I j := by
  have hj := Finset.orderEmbOfFin_mem (complementSet I) (complementSet_card I) j
  simp only [complementSet, Finset.mem_compl, Finset.mem_map, Finset.mem_univ, true_and,
    not_exists] at hj
  exact hj i

theorem orderedComplement_surjective_compl {n k} (I : Fin k ↪ Fin n) (i : Fin n)
    (hi : ¬ ∃ j, I j=i) : ∃ j, orderedComplement I j=i := by
  have hm : i ∈ complementSet I := by simpa [complementSet] using hi
  let x : complementSet I := ⟨i,hm⟩
  refine ⟨((complementSet I).orderIsoOfFin (complementSet_card I)).symm x, ?_⟩
  exact congrArg Subtype.val (((complementSet I).orderIsoOfFin (complementSet_card I)).apply_symm_apply x)

/-- Exact selected/complement partition, preserving the original slot labels. -/
def slotEquiv {n k} (I : Fin k ↪ Fin n) : (Fin k ⊕ Fin (n-k)) ≃ Fin n :=
  Equiv.ofBijective (Sum.elim I (orderedComplement I)) (by
    constructor
    · intro x y h
      cases x with
      | inl i => cases y with
        | inl j => exact congrArg Sum.inl (I.injective h)
        | inr j => exact False.elim (orderedComplement_disjoint I i j h)
      | inr i => cases y with
        | inl j => exact False.elim (orderedComplement_disjoint I j i h.symm)
        | inr j => exact congrArg Sum.inr ((orderedComplement I).injective h)
    · intro i
      by_cases hi : ∃ j, I j=i
      · obtain ⟨j,hj⟩ := hi; exact ⟨Sum.inl j,hj⟩
      · obtain ⟨j,hj⟩ := orderedComplement_surjective_compl I i hi
        exact ⟨Sum.inr j,hj⟩)

@[simp] theorem slotEquiv_inl {n k} (I : Fin k ↪ Fin n) (i : Fin k) :
    slotEquiv I (Sum.inl i)=I i := rfl

@[simp] theorem slotEquiv_inr {n k} (I : Fin k ↪ Fin n) (i : Fin (n-k)) :
    slotEquiv I (Sum.inr i)=orderedComplement I i := rfl

/-- The combined selected and complementary labels. Global monotonicity is a
separate question; only the complementary list will be sorted. -/
def combinedValues {n k} (I : Fin k ↪ Fin n) (s : Fin k → ℝ) (t : Fin (n-k) → ℝ) :
    Fin n → ℝ := fun i => Sum.elim s t ((slotEquiv I).symm i)

@[simp] theorem combinedValues_selected {n k} (I : Fin k ↪ Fin n)
    (s : Fin k → ℝ) (t : Fin (n-k) → ℝ) (j : Fin k) :
    combinedValues I s t (I j)=s j := by
  change Sum.elim s t ((slotEquiv I).symm (slotEquiv I (Sum.inl j)))=s j
  simp only [Equiv.symm_apply_apply, Sum.elim_inl]

@[simp] theorem combinedValues_complement {n k} (I : Fin k ↪ Fin n)
    (s : Fin k → ℝ) (t : Fin (n-k) → ℝ) (j : Fin (n-k)) :
    combinedValues I s t (orderedComplement I j)=t j := by
  change Sum.elim s t ((slotEquiv I).symm (slotEquiv I (Sum.inr j)))=t j
  simp only [Equiv.symm_apply_apply, Sum.elim_inr]

theorem combinedValues_nonneg {n k} (I : Fin k ↪ Fin n)
    (s : Fin k → ℝ) (t : Fin (n-k) → ℝ) (hs : ∀j, 0≤s j) (ht : ∀j, 0≤t j) :
    ∀i, 0≤combinedValues I s t i := by
  intro i
  unfold combinedValues
  cases (slotEquiv I).symm i with
  | inl j => exact hs j
  | inr j => exact ht j

/-- Genuine Gram identity gives the Euclidean orthonormal input for the
retained prescribed-slot extension. -/
theorem columns_orthonormal {n k} (Q : Matrix (Fin n) (Fin k) ℝ)
    (hQ : Q.transpose*Q=1) :
    Orthonormal ℝ (fun j => (WithLp.toLp 2 (fun i => Q i j) : EuclideanSpace ℝ (Fin n))) := by
  rw [orthonormal_iff_ite]
  intro i j
  have h := congrFun (congrFun hQ i) j
  simpa [PiLp.inner_apply, real_inner_eq_re_inner, RCLike.inner_apply,
    Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply, mul_comm] using h

/-- Gram identity is preserved when columns are reindexed by a bijection. -/
theorem gram_reindex {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
    [DecidableEq β] [DecidableEq γ] (A : Matrix α β ℝ) (e : γ ≃ β)
    (hA : A.transpose*A=1) : (A.submatrix id e).transpose*(A.submatrix id e)=1 := by
  rw [Matrix.transpose_submatrix]
  rw [← Matrix.submatrix_mul _ _ e id e Function.bijective_id]
  rw [hA, Matrix.submatrix_one_equiv]

/-- The split column matrix of a full basis remains orthogonal in both
directions. -/
theorem split_basis_orthogonal {n k} (I : Fin k ↪ Fin n)
    (U : OrthonormalBasis (Fin n) ℝ (EuclideanSpace ℝ (Fin n))) :
    let Q := (orthonormalBasisMatrix U).submatrix id I
    let Qperp := (orthonormalBasisMatrix U).submatrix id (orderedComplement I)
    (Matrix.fromCols Q Qperp).transpose*Matrix.fromCols Q Qperp=1 ∧
      Matrix.fromCols Q Qperp*(Matrix.fromCols Q Qperp).transpose=1 := by
  dsimp only
  have he : Matrix.fromCols ((orthonormalBasisMatrix U).submatrix id I)
      ((orthonormalBasisMatrix U).submatrix id (orderedComplement I)) =
      (orthonormalBasisMatrix U).submatrix id (slotEquiv I) := by
    ext i j; cases j <;> rfl
  constructor
  · rw [he]
    exact gram_reindex _ _ (orthonormalBasisMatrix_transpose_mul_self U)
  · rw [he, Matrix.transpose_submatrix, Matrix.submatrix_mul_equiv,
      Matrix.submatrix_id_id, orthonormalBasisMatrix_mul_transpose]

/-- Extract the exact four Gram blocks of an orthogonal split family. -/
theorem split_gram_blocks {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
    [DecidableEq β] [DecidableEq γ] (Q : Matrix α β ℝ) (Qc : Matrix α γ ℝ)
    (h : (Matrix.fromCols Q Qc).transpose*Matrix.fromCols Q Qc=1) :
    Q.transpose*Q=1 ∧ Q.transpose*Qc=0 ∧ Qc.transpose*Q=0 ∧ Qc.transpose*Qc=1 := by
  rw [Matrix.transpose_fromCols, Matrix.fromRows_mul_fromCols] at h
  refine ⟨?_,?_,?_,?_⟩
  · have hh := congrArg Matrix.toBlocks₁₁ h
    simpa [Matrix.toBlocks₁₁, Matrix.one_apply] using hh
  · simpa using congrArg Matrix.toBlocks₁₂ h
  · simpa using congrArg Matrix.toBlocks₂₁ h
  · have hh := congrArg Matrix.toBlocks₂₂ h
    simpa [Matrix.toBlocks₂₂, Matrix.one_apply] using hh

/-- Orthogonal rotation of only the complementary columns preserves all Gram
blocks, including zero-sized complementary blocks. -/
theorem rotate_complement_gram {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
    [DecidableEq β] [DecidableEq γ] (Q : Matrix α β ℝ) (Qc : Matrix α γ ℝ)
    (W : Matrix γ γ ℝ) (h : (Matrix.fromCols Q Qc).transpose*Matrix.fromCols Q Qc=1)
    (hW : W.transpose*W=1) :
    (Matrix.fromCols Q (Qc*W)).transpose*Matrix.fromCols Q (Qc*W)=1 := by
  obtain ⟨hQ,hcross,hcross',hQc⟩ := split_gram_blocks Q Qc h
  have hc : Q.transpose*(Qc*W)=0 := by rw [← Matrix.mul_assoc,hcross,Matrix.zero_mul]
  have hc' : (Qc*W).transpose*Q=0 := by rw [Matrix.transpose_mul,Matrix.mul_assoc,hcross',Matrix.mul_zero]
  have hcc : (Qc*W).transpose*(Qc*W)=1 := by
    calc
      _ = W.transpose*(Qc.transpose*Qc)*W := by simp only [Matrix.transpose_mul,Matrix.mul_assoc]
      _ = 1 := by rw [hQc,Matrix.mul_one,hW]
  rw [Matrix.transpose_fromCols,Matrix.fromRows_mul_fromCols,hQ,hc,hc',hcc,Matrix.fromBlocks_one]

/-- Both exact selected-column identities force both cross blocks to vanish.
The remaining block is the actual compression `Qcᵀ B Pc`. -/
theorem exact_split {n k h} (B : Matrix (Fin n) (Fin n) ℝ)
    (Q P : Matrix (Fin n) (Fin k) ℝ) (Qc Pc : Matrix (Fin n) (Fin h) ℝ)
    (s : Fin k → ℝ)
    (hL : (Matrix.fromCols Q Qc).transpose*Matrix.fromCols Q Qc=1)
    (hLrow : Matrix.fromCols Q Qc*(Matrix.fromCols Q Qc).transpose=1)
    (hR : (Matrix.fromCols P Pc).transpose*Matrix.fromCols P Pc=1)
    (hRrow : Matrix.fromCols P Pc*(Matrix.fromCols P Pc).transpose=1)
    (hBP : B*P=Q*Matrix.diagonal s) (hBTQ : B.transpose*Q=P*Matrix.diagonal s) :
    B=Q*Matrix.diagonal s*P.transpose+Qc*(Qc.transpose*B*Pc)*Pc.transpose := by
  obtain ⟨hQ,hQcross,hQcross',_hQc⟩ := split_gram_blocks Q Qc hL
  obtain ⟨_hP,hPcross,_hPcross',_hPc⟩ := split_gram_blocks P Pc hR
  have hQB : Q.transpose*B=Matrix.diagonal s*P.transpose := by
    have hh := congrArg Matrix.transpose hBTQ
    simpa only [Matrix.transpose_mul,Matrix.transpose_transpose,Matrix.diagonal_transpose] using hh
  have h11 : Q.transpose*B*P=Matrix.diagonal s := by
    rw [Matrix.mul_assoc,hBP,←Matrix.mul_assoc,hQ,Matrix.one_mul]
  have h12 : Q.transpose*B*Pc=0 := by rw [hQB,Matrix.mul_assoc,hPcross,Matrix.mul_zero]
  have h21 : Qc.transpose*B*P=0 := by
    rw [Matrix.mul_assoc,hBP,←Matrix.mul_assoc,hQcross',Matrix.zero_mul]
  have hcomp : (Matrix.fromCols Q Qc).transpose*B*Matrix.fromCols P Pc =
      Matrix.fromBlocks (Matrix.diagonal s) 0 0 (Qc.transpose*B*Pc) := by
    rw [Matrix.transpose_fromCols,Matrix.fromRows_mul,Matrix.fromRows_mul_fromCols,h11,h12,h21]
  calc
    B=1*B*1 := by simp
    _=(Matrix.fromCols Q Qc*(Matrix.fromCols Q Qc).transpose)*B*
        (Matrix.fromCols P Pc*(Matrix.fromCols P Pc).transpose) := by rw [hLrow,hRrow]
    _=Matrix.fromCols Q Qc*((Matrix.fromCols Q Qc).transpose*B*Matrix.fromCols P Pc)*
        (Matrix.fromCols P Pc).transpose := by simp only [Matrix.mul_assoc]
    _=Q*Matrix.diagonal s*P.transpose+Qc*(Qc.transpose*B*Pc)*Pc.transpose := by
      rw [hcomp]
      simp only [Matrix.fromCols_mul_fromBlocks,Matrix.mul_zero,zero_add,
        add_zero,Matrix.transpose_fromCols,Matrix.fromCols_mul_fromRows]

/-- Exact diagonal assembly on a selected/complementary sum index. -/
theorem fromCols_diagonal {n k h} (Q P : Matrix (Fin n) (Fin k) ℝ)
    (Qc Pc : Matrix (Fin n) (Fin h) ℝ) (s : Fin k → ℝ) (t : Fin h → ℝ) :
    Matrix.fromCols Q Qc*Matrix.diagonal (Sum.elim s t)*(Matrix.fromCols P Pc).transpose =
      Q*Matrix.diagonal s*P.transpose+Qc*Matrix.diagonal t*Pc.transpose := by
  have hd : Matrix.diagonal (Sum.elim s t) =
      Matrix.fromBlocks (Matrix.diagonal s) 0 0 (Matrix.diagonal t) := by
    ext (i|i) (j|j) <;> simp [Matrix.diagonal]
  simp only [hd,Matrix.fromCols_mul_fromBlocks,Matrix.mul_zero,zero_add,
    add_zero,Matrix.transpose_fromCols,Matrix.fromCols_mul_fromRows]

/-- Reindexing the complete factorization also reindexes its diagonal labels. -/
theorem reindex_factorization {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
    [DecidableEq β] [DecidableEq γ] (L R : Matrix α β ℝ) (v : β → ℝ) (e : γ ≃ β) :
    L.submatrix id e*Matrix.diagonal (fun i => v (e i))*(R.submatrix id e).transpose =
      L*Matrix.diagonal v*R.transpose := by
  change (L.submatrix id e*Matrix.diagonal (v ∘ e))*(R.submatrix id e).transpose = _
  rw [←Matrix.submatrix_diagonal_equiv v e,Matrix.transpose_submatrix,
    Matrix.submatrix_mul_equiv,Matrix.submatrix_mul_equiv,Matrix.submatrix_id_id]

/-- A complementary-column block of an actual full orthonormal basis. -/
def complementColumns {n k} (I : Fin k ↪ Fin n)
    (U : OrthonormalBasis (Fin n) ℝ (EuclideanSpace ℝ (Fin n))) :
    Matrix (Fin n) (Fin (n-k)) ℝ :=
  (orthonormalBasisMatrix U).submatrix id (orderedComplement I)

/-- Exact block SVD at prescribed positions. Only the complementary values are
sorted. The combined nonnegative diagonal need not be globally sorted, so `I`
is not claimed to be the true rank list of `B`. Empty selected families and
empty complements are handled by the same construction. -/
theorem exists_block_svd {n k} (B : Matrix (Fin n) (Fin n) ℝ)
    (Q P : Matrix (Fin n) (Fin k) ℝ) (I : Fin k ↪ Fin n) (s : Fin k → ℝ)
    (hs : ∀j, 0≤s j) (hQ : Q.transpose*Q=1) (hP : P.transpose*P=1)
    (hBP : B*P=Q*Matrix.diagonal s) (hBTQ : B.transpose*Q=P*Matrix.diagonal s) :
    ∃ (U₀ V₀ : OrthonormalBasis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)))
      (U V : Matrix (Fin n) (Fin n) ℝ) (t : Fin (n-k) → ℝ),
      (orthonormalBasisMatrix U₀).submatrix id I=Q ∧
      (orthonormalBasisMatrix V₀).submatrix id I=P ∧
      t=ascendingRealSpectrum ((complementColumns I U₀).transpose*B*complementColumns I V₀) ∧
      Monotone t ∧ (∀j, 0≤t j) ∧
      (∀i, 0≤combinedValues I s t i) ∧
      U.transpose*U=1 ∧ U*U.transpose=1 ∧ V.transpose*V=1 ∧ V*V.transpose=1 ∧
      U.submatrix id I=Q ∧ V.submatrix id I=P ∧
      B=U*Matrix.diagonal (combinedValues I s t)*V.transpose := by
  obtain ⟨U₀,hU₀⟩ := exists_orthonormalBasis_extending_fin_embedding I _ (columns_orthonormal Q hQ)
  obtain ⟨V₀,hV₀⟩ := exists_orthonormalBasis_extending_fin_embedding I _ (columns_orthonormal P hP)
  have hUQ : (orthonormalBasisMatrix U₀).submatrix id I=Q := by
    ext i j
    change U₀ (I j) i=Q i j
    rw [hU₀ j]
  have hVP : (orthonormalBasisMatrix V₀).submatrix id I=P := by
    ext i j
    change V₀ (I j) i=P i j
    rw [hV₀ j]
  let Qc := complementColumns I U₀
  let Pc := complementColumns I V₀
  have hL : (Matrix.fromCols Q Qc).transpose*Matrix.fromCols Q Qc=1 ∧
      Matrix.fromCols Q Qc*(Matrix.fromCols Q Qc).transpose=1 := by
    simpa only [hUQ] using split_basis_orthogonal I U₀
  have hR : (Matrix.fromCols P Pc).transpose*Matrix.fromCols P Pc=1 ∧
      Matrix.fromCols P Pc*(Matrix.fromCols P Pc).transpose=1 := by
    simpa only [hVP] using split_basis_orthogonal I V₀
  let C₀ := Qc.transpose*B*Pc
  obtain ⟨Uc,Vc,htm,ht0,hC₀⟩ := exists_orthonormalBases_ascendingRealSpectrum C₀
  let t := ascendingRealSpectrum C₀
  let A := orthonormalBasisMatrix Uc
  let D := orthonormalBasisMatrix Vc
  let L := Matrix.fromCols Q (Qc*A)
  let R := Matrix.fromCols P (Pc*D)
  let U := L.submatrix id (slotEquiv I).symm
  let V := R.submatrix id (slotEquiv I).symm
  have hLG : L.transpose*L=1 := rotate_complement_gram Q Qc A hL.1
    (orthonormalBasisMatrix_transpose_mul_self Uc)
  have hRG : R.transpose*R=1 := rotate_complement_gram P Pc D hR.1
    (orthonormalBasisMatrix_transpose_mul_self Vc)
  have hUG : U.transpose*U=1 := gram_reindex L (slotEquiv I).symm hLG
  have hVG : V.transpose*V=1 := gram_reindex R (slotEquiv I).symm hRG
  have hUI : U.submatrix id I=Q := by
    ext i j
    change Matrix.fromCols Q (Qc*A) i ((slotEquiv I).symm (slotEquiv I (Sum.inl j)))=Q i j
    rw [Equiv.symm_apply_apply]
    rfl
  have hVI : V.submatrix id I=P := by
    ext i j
    change Matrix.fromCols P (Pc*D) i ((slotEquiv I).symm (slotEquiv I (Sum.inl j)))=P i j
    rw [Equiv.symm_apply_apply]
    rfl
  refine ⟨U₀,V₀,U,V,t,hUQ,hVP,rfl,htm,ht0,combinedValues_nonneg I s t hs ht0,
    hUG,mul_eq_one_comm.mp hUG,hVG,mul_eq_one_comm.mp hVG,hUI,hVI,?_⟩
  have hsplit := exact_split B Q P Qc Pc s hL.1 hL.2 hR.1 hR.2 hBP hBTQ
  change B=L.submatrix id (slotEquiv I).symm*
    Matrix.diagonal (fun i => Sum.elim s t ((slotEquiv I).symm i))*(R.submatrix id (slotEquiv I).symm).transpose
  rw [reindex_factorization]
  dsimp only [L,R]
  rw [fromCols_diagonal]
  rw [hsplit]
  congr 1
  change Qc*C₀*Pc.transpose=(Qc*A)*Matrix.diagonal t*(Pc*D).transpose
  rw [hC₀]
  simp only [A,D,t,Matrix.transpose_mul,Matrix.mul_assoc]

end
end NumStability.CommonWitnessBlocks
