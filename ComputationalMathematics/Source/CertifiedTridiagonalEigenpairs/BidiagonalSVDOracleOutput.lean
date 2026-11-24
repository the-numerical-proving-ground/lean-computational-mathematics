import ComputationalMathematics.Source.CertifiedTridiagonalEigenpairs.BidiagonalSVDOracleParities
import ComputationalMathematics.Source.CertifiedTridiagonalEigenpairs.BidiagonalSVDRoundedOutput

/-!
# Output of the nontrivial bidiagonal SVD branch

The original requests supply the order of both parity arrays and the final
labels. Normalization acts directly on the auxiliary-precision words.
-/

open Matrix NumStability.Matrix.Bipartite NumStability.Matrix.Bipartite.MassParityGrams
open scoped Matrix.Norms.L2Operator

namespace NumStability.CertifiedTridiagonalEigenpairs.BidiagonalSVDRequest

open FloatingPointFormat.UnboundedBinary NormalizedGram

noncomputable section

/-- The returned labels and both arrays have the output precision. -/
structure NativeSVDTriplets (n k p : ℕ) (hp : 2 ≤ p) where
  leftWords : Fin k → Fin n → Word p hp
  rightWords : Fin k → Fin n → Word p hp
  labels : Fin k → Word p hp

variable {n k p : ℕ} {hp : 2 ≤ p}

def NativeSVDTriplets.leftMatrix (out : NativeSVDTriplets n k p hp) :
    Matrix (Fin n) (Fin k) ℝ := fun i j => (out.leftWords j i).value

def NativeSVDTriplets.rightMatrix (out : NativeSVDTriplets n k p hp) :
    Matrix (Fin n) (Fin k) ℝ := fun i j => (out.rightWords j i).value

/-- Source guarantees for the actual returned words, before constructing
the common nearby SVD witness. -/
structure ReturnedTripletAccuracy (B : Matrix (Fin n) (Fin n) ℝ)
    (I : Fin k → Fin n) (out : NativeSVDTriplets n k p hp) : Prop where
  labels_nonnegative : ∀ j, 0 ≤ (out.labels j).value
  labels_monotone : Monotone fun j => (out.labels j).value
  value_error : ∀ j, |(out.labels j).value - ascendingRealSpectrum B (I j)| <
    16 * unitRoundoff p * ‖B‖
  left_norm : ∀ j, |columnNorm out.leftMatrix j - 1| ≤ 2 * unitRoundoff p
  right_norm : ∀ j, |columnNorm out.rightMatrix j - 1| ≤ 2 * unitRoundoff p
  left_pairs : ∀ i j, i ≠ j → |(out.leftMatrixᵀ * out.leftMatrix) i j| ≤ 6 * unitRoundoff p
  right_pairs : ∀ i j, i ≠ j → |(out.rightMatrixᵀ * out.rightMatrix) i j| ≤ 6 * unitRoundoff p
  left_gram : ‖out.leftMatrixᵀ * out.leftMatrix - 1‖ < 7 * Real.sqrt k * unitRoundoff p
  right_gram : ‖out.rightMatrixᵀ * out.rightMatrix - 1‖ < 7 * Real.sqrt k * unitRoundoff p
  dimension_budget : 7 * Real.sqrt k * unitRoundoff p ≤ 7 / 128
  left_residual : ∀ j, vecNorm2 (fun i => (B * out.rightMatrix -
      out.leftMatrix * diagonal (fun j => (out.labels j).value)) i j) ≤
    160 * unitRoundoff p * ‖B‖
  right_residual : ∀ j, vecNorm2 (fun i => (Bᵀ * out.leftMatrix -
      out.rightMatrix * diagonal (fun j => (out.labels j).value)) i j) ≤
    160 * unitRoundoff p * ‖B‖

/-- Final vector normalizations, nearest-even value roundings and exact
exponent shifts on the labels. -/
def finishNative (leftRaw rightRaw : Fin k → Fin n → AuxWord k p)
    (s : Fin k → ℝ) (scaleExponent : ℤ)
    (hL : ∀ j, Word.euclidean (leftRaw j) ≠ 0)
    (hR : ∀ j, Word.euclidean (rightRaw j) ≠ 0) : NativeSVDTriplets n k p hp :=
  ⟨fun j => Word.normalizeTo p hp (leftRaw j) (hL j),
    fun j => Word.normalizeTo p hp (rightRaw j) (hR j),
    fun j => (Word.round p hp (s j)).scale scaleExponent⟩

private abbrev col {m ι : Type*} (X : Matrix m ι ℝ) (j : ι) : EuclideanSpace ℝ m :=
  WithLp.toLp 2 (fun i => X i j)

private theorem normalized_col {m ι : Type*} [Fintype m] [Fintype ι] [DecidableEq ι]
    (X : Matrix m ι ℝ) (j : ι) :
    col (normalizeColumns X) j = ‖col X j‖⁻¹ • col X j := by
  ext i
  simp [col, normalizeColumns, columnNorm, Matrix.mul_diagonal, mul_comm]

private theorem vecNorm2_eq_norm (x : Fin n → ℝ) :
    vecNorm2 x = ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin n))‖ := by
  simp [vecNorm2, vecNorm2Sq, EuclideanSpace.norm_eq, Real.norm_eq_abs, sq_abs]

private theorem matrix_residual_col (B : Matrix (Fin n) (Fin n) ℝ)
    (U V : Matrix (Fin n) (Fin k) ℝ) (μ : Fin k → ℝ) (j : Fin k) :
    col (B * V - U * diagonal μ) j =
      B.toEuclideanLin (col V j) - μ j • col U j := by
  ext i
  simp only [col, Matrix.toLpLin_apply, Matrix.sub_apply, Matrix.mul_diagonal,
    PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
  simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, mul_comm]

private theorem svd_precision_budgets (k p : ℕ) :
    0 < svdAlpha k p ∧ svdAlpha k p ≤ unitRoundoff p ∧
    (64 * unitRoundoff (svdAuxiliaryPrecision k p)) / svdAlpha k p = unitRoundoff p / 16 := by
  have hα : 0 < svdAlpha k p := by
    rw [svdAlpha_eq_unitRoundoff]
    exact unitRoundoff_pos _
  have hκ : (1 : ℝ) ≤ svdKappa k := by
    unfold svdKappa
    exact_mod_cast (Nat.one_le_pow (Nat.clog 2 k) 2 (by decide))
  refine ⟨hα, div_le_self (unitRoundoff_pos _).le hκ, ?_⟩
  have hκ₀ : (svdKappa k : ℝ) ≠ 0 := by linarith
  rw [svd_unitRoundoff_auxiliary_eq, svdAlpha]
  field_simp [(unitRoundoff_pos p).ne', hκ₀]
  ring

/-- Analyze final normalization and rounding from the native parity words of
one signed witness. The grouping is only used in the proof of the raw Grams. -/
theorem finishNative_accuracy {r h l : ℕ} (hp : 2 ≤ p) (hn : 2 ≤ n)
    (hk : 1 ≤ k) (hkn : k ≤ n) (hguard : precisionGuard n p) (I : Fin k → Fin n)
    (B C : Matrix (Fin n) (Fin n) ℝ) (scaleExponent : ℤ)
    (hB : B = (2 : ℝ) ^ scaleExponent • C) (hscale : (2 : ℝ) ^ scaleExponent < 8 * ‖B‖)
    (hC : ‖C‖ ≤ 1 / 2) (s : Fin k → ℝ) (cut : ℝ)
    (hsMono : Monotone s) (hs₀ : ∀ j, 0 ≤ s j) (hsMax : ∀ j, s j ≤ 3 / 4)
    (hs : ∀ j, |s j - ascendingRealSpectrum C (I j)| ≤
      unitRoundoff (svdAuxiliaryPrecision k p) / 64)
    (hcut : svdAlpha k p ≤ cut) (hcutu : cut ≤ 2 * unitRoundoff p)
    (e : Fin h ⊕ Fin l ≃ Fin k)
    (hHigh : ∀ j, cut + svdAlpha k p ≤ s (e (.inl j)))
    (hLow : ∀ j, s (e (.inr j)) ≤ cut)
    (W : Matrix (Fin n ⊕ Fin n) (Fin r) ℝ) (d : Fin r → ℝ)
    (eP : Fin k ↪ Fin r) (eL : Fin l ↪ Fin r)
    (hdP : ∀ j, d (eP j) = massMagnitude (svdAlpha k p) (s j))
    (hdL : ∀ j, d (eL j) = -massMagnitude (svdAlpha k p) (s (e (.inr j))))
    (hW : Wᵀ * W = 1)
    (hE : ‖massShift C (svdAlpha k p) * W - W * diagonal d‖ ≤
      64 * unitRoundoff (svdAuxiliaryPrecision k p))
    (leftRaw rightRaw : Fin k → Fin n → AuxWord k p)
    (hLRaw : ∀ j, ‖Word.euclidean (leftRaw j) -
      col (left W) (eP j)‖ ≤ 4 * unitRoundoff (svdAuxiliaryPrecision k p))
    (hRRaw : ∀ j, ‖Word.euclidean (rightRaw j) -
      col (mixedRight (columns W (eP ∘ e ∘ Sum.inl)) (columns W eL)) (e.symm j)‖ ≤
      4 * unitRoundoff (svdAuxiliaryPrecision k p)) :
    ∃ (hL : ∀ j, Word.euclidean (leftRaw j) ≠ 0)
      (hR : ∀ j, Word.euclidean (rightRaw j) ≠ 0),
      ReturnedTripletAccuracy B I (finishNative (hp := hp) leftRaw rightRaw s scaleExponent hL hR) := by
  let u := unitRoundoff p
  let ε := unitRoundoff (svdAuxiliaryPrecision k p)
  let α := svdAlpha k p
  let η := 64 * ε
  let pG := e.toEmbedding.trans eP
  let pH : Fin h ↪ Fin r := ⟨eP ∘ e ∘ Sum.inl, eP.injective.comp (e.injective.comp Sum.inl_injective)⟩
  let X := left (W.submatrix id eP)
  let Yg := mixedRight (columns W pH) (columns W eL)
  let Y := Yg.submatrix id e.symm
  let dX := fun j => (1 + α / massMagnitude α (s j)) / 2
  let dYg := Sum.elim (fun i => (1 - α / massMagnitude α (s (e (.inl i)))) / 2)
    (fun i => (1 + α / massMagnitude α (s (e (.inr i)))) / 2)
  let dY := dYg ∘ e.symm
  have hα := svd_precision_budgets k p
  have hu : 0 < u := unitRoundoff_pos _
  have hη : 0 ≤ η := mul_nonneg (by norm_num) (unitRoundoff_pos _).le
  obtain ⟨hdX, hdYg, hX, hY⟩ :=
    parity_raw_gram_budgets C α η cut u W d eP pH eL s
      (s ∘ e ∘ Sum.inl) (s ∘ e ∘ Sum.inr) hα.1 hη hcut hu hα.2.2
      hHigh (fun j => hs₀ _) hLow hW hdP (fun j => hdP _) hdL hE
  have hdY (j : Fin k) : (1 / 4 : ℝ) ≤ dY j := hdYg (e.symm j)
  have hX' : ‖Xᵀ * X - diagonal dX‖ ≤ u / 8 := hX.trans (by linarith)
  have hY' : ‖Yᵀ * Y - diagonal dY‖ ≤ u / 8 :=
    (parity_gram_deviation_reindex Yg dYg e.symm).trans_le hY.le
  obtain ⟨hx, _, xnorm, xpairs, _, xgram, hdim⟩ :=
    svd_computed_parity_array hp hn hk hkn hguard X dX leftRaw hdX hX' hLRaw
  obtain ⟨hy, _, ynorm, ypairs, _, ygram, _⟩ :=
    svd_computed_parity_array hp hn hk hkn hguard Y dY rightRaw hdY hY' hRRaw
  have hu' := (svd_normalization_roundoff_budget (k := k) hn hguard).2.1
  have hExact := svd_normalized_residuals_of_witness C W d pG eL (s ∘ e)
    hα.1 hα.2.1 hu' hη hα.2.2 hcut hcutu hHigh (fun j => hs₀ _) hLow
    (fun j => hsMax _) hW (fun j => hdP _) hdL hE
  have hExact' (j : Fin k) :
      ‖C.toEuclideanLin (‖col Y j‖⁻¹ • col Y j) -
        s j • (‖col X j‖⁻¹ • col X j)‖ ≤ 15 * u ∧
      ‖Cᵀ.toEuclideanLin (‖col X j‖⁻¹ • col X j) -
        s j • (‖col Y j‖⁻¹ • col Y j)‖ ≤ 15 * u := by
    have h := hExact (e.symm j)
    change ‖C.toEuclideanLin (col (normalizeColumns Yg) (e.symm j)) -
        s (e (e.symm j)) • col (normalizeColumns (X.submatrix id e)) (e.symm j)‖ ≤ 15 * u ∧
      ‖Cᵀ.toEuclideanLin (col (normalizeColumns (X.submatrix id e)) (e.symm j)) -
        s (e (e.symm j)) • col (normalizeColumns Yg) (e.symm j)‖ ≤ 15 * u at h
    simp only [normalized_col, col, Matrix.submatrix_apply, id_eq, Equiv.apply_symm_apply] at h
    exact h
  have hXnorm := (parity_normalized_gram_budgets X dX u hu' hdX hX').1
  have hYnorm := (parity_normalized_gram_budgets Y dY u hu' hdY hY').1
  let out := finishNative (hp := hp) leftRaw rightRaw s scaleExponent hx hy
  let R := (2 : ℝ) ^ scaleExponent
  have hR : 0 < R := by unfold R; positivity
  have hlabel (j : Fin k) : (out.labels j).value = R * roundToEven p hp (s j) := by
    simp only [out, finishNative, Word.value_scale, Word.value_round, R]
  have hμ := svd_rounded_labels hp s hsMono hs₀ hsMax
  have hres (j : Fin k) :
      ‖B.toEuclideanLin (col out.rightMatrix j) - (out.labels j).value • col out.leftMatrix j‖ ≤
        160 * u * ‖B‖ ∧
      ‖Bᵀ.toEuclideanLin (col out.leftMatrix j) - (out.labels j).value • col out.rightMatrix j‖ ≤
        160 * u * ‖B‖ := by
    obtain ⟨_, _, _, _, hL, hR', _⟩ := svd_computed_pair_residuals hp hn hguard B C
      (col X j) (col Y j) (leftRaw j) (rightRaw j) hR hB hscale hC (hs₀ j) (hsMax j)
      (hs j) (hXnorm j) (hYnorm j) (hLRaw j) (hRRaw j) (hExact' j).1 (hExact' j).2
    rw [hlabel]
    exact ⟨hL, hR'⟩
  refine ⟨hx, hy, ?_⟩
  change ReturnedTripletAccuracy B I out
  refine ⟨?_, ?_, ?_, xnorm, ynorm, xpairs, ypairs, xgram, ygram, hdim, ?_, ?_⟩
  · intro j
    rw [hlabel]
    exact mul_nonneg hR.le (hμ.2 j).1
  · intro i j hij
    simp only [hlabel]
    exact mul_le_mul_of_nonneg_left (hμ.1 hij) hR.le
  · intro j
    rw [hlabel]
    exact svd_rescaled_indexed_label_error hp B C (I j) hB hR hscale hC (hs₀ j) (hs j)
  · intro j
    rw [vecNorm2_eq_norm]
    change ‖col (B * out.rightMatrix - out.leftMatrix * diagonal (fun j => (out.labels j).value)) j‖ ≤ _
    rw [matrix_residual_col]
    exact (hres j).1
  · intro j
    rw [vecNorm2_eq_norm]
    change ‖col (Bᵀ * out.leftMatrix - out.rightMatrix * diagonal (fun j => (out.labels j).value)) j‖ ≤ _
    rw [matrix_residual_col]
    exact (hres j).2

namespace TridiagonalCall

/-- Finish the actual auxiliary output at the prescribed final precision. -/
def finish (call : TridiagonalCall n k p) (out : call.NativeParities)
    (hL : ∀ j, Word.euclidean ((out.left.get j).get) ≠ 0)
    (hR : ∀ j, Word.euclidean ((out.right.get j).get) ≠ 0) :
    NativeSVDTriplets (n + 1) k p hp :=
  finishNative (fun j => (out.left.get j).get) (fun j => (out.right.get j).get) call.label
    call.preprocessing.scaleExponent hL hR

/-- Every successful auxiliary solve yields native output triplets with
the source's norm, orthogonality, residual and label guarantees. -/
theorem solve_finish_accuracy (call : TridiagonalCall n k p) (hp : 2 ≤ p)
    (upper : Bool) (B C : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (hB : B = (2 : ℝ) ^ call.preprocessing.scaleExponent • C)
    (hscale : (2 : ℝ) ^ call.preprocessing.scaleExponent < 8 * ‖B‖)
    (hC : bidiagonalSupport upper C) (hCnorm : ‖C‖ ≤ 1 / 2)
    (hcall : call.matrix = (bidiagonalMassShift upper C (svdAlpha k p)).submatrix
      (bidiagonalRefinementCoord (by omega)) (bidiagonalRefinementCoord (by omega)))
    (hsMono : Monotone call.label) (hs₀ : ∀ j, 0 ≤ call.label j)
    (hsMax : ∀ j, call.label j ≤ 3 / 4)
    (hs : ∀ j, |call.label j - ascendingRealSpectrum C (call.slots j)| ≤
      unitRoundoff (svdAuxiliaryPrecision k p) / 64)
    (cut : ℝ) (hcut : svdAlpha k p ≤ cut) (hcutu : cut ≤ 2 * unitRoundoff p)
    (hHigh : ∀ j, call.low j = false → cut + svdAlpha k p ≤ call.label j)
    (hLow : ∀ j, call.low j = true → call.label j ≤ cut)
    (hn : 2 ≤ n + 1) (hk : 1 ≤ k) (hguard : precisionGuard (n + 1) p)
    (bits : ℕ → GateBits (edgeCount n) call.oneBasedRanks) (out : call.NativeParities)
    (hrun : call.solveParities upper hk hguard bits = some out) :
    ∃ (hL : ∀ j, Word.euclidean ((out.left.get j).get) ≠ 0)
      (hR : ∀ j, Word.euclidean ((out.right.get j).get) ≠ 0),
      ReturnedTripletAccuracy B call.slots (call.finish (hp := hp) out hL hR) := by
  have hkn : k ≤ n + 1 := by
    simpa using Fintype.card_le_of_injective call.slots call.slots.injective
  obtain ⟨W, hW, hE, hx, hy⟩ :=
    call.solveParities_witness upper C hC hcall hCnorm hp hs hk hguard bits out hrun
  let Yg := mixedRight (columns W (call.positiveSlot ∘ call.group.symm ∘ Sum.inl))
    (columns W call.lowSlot)
  have hY (i : Fin (n + 1)) (j : Fin k) : Yg i (call.group j) = call.rightExact W i j := by
    have h := call.rightSlot_group (call.group j)
    rw [call.group.symm_apply_apply] at h
    generalize hg : call.group j = t at h ⊢
    cases t
    · rw [rightExact, Matrix.submatrix_apply, h]
      rfl
    · rw [rightExact, Matrix.submatrix_apply, h]
      rfl
  have hy' (j : Fin k) : ‖Word.euclidean ((out.right.get j).get) -
      col Yg (call.group j)‖ ≤ 4 * unitRoundoff (svdAuxiliaryPrecision k p) := by
    have he : col Yg (call.group j) = WithLp.toLp 2 ((call.rightExact W).col j) := by
      ext i
      exact hY i j
    rw [he]
    exact hy j
  exact finishNative_accuracy hp hn hk hkn hguard call.slots B C
    call.preprocessing.scaleExponent hB hscale hCnorm call.label cut hsMono hs₀ hsMax hs hcut hcutu
    call.group.symm
    (fun j => hHigh _ (Bool.eq_false_iff.mpr (call.highOriginalSlot j).property))
    (fun j => hLow _ (call.lowOriginalSlot j).property)
    W call.proofLabels call.positiveSlot call.lowSlot call.proofLabels_positiveSlot
    call.proofLabels_lowSlot hW hE (fun j => (out.left.get j).get) (fun j => (out.right.get j).get) hx hy'


private theorem cachedLabel_order (upper : Bool) (a : Fin (n + 1) → Word p hp)
    (b : Fin n → Word p hp) (I : Fin k → Fin (n + 1))
    (cmp : EmptyBinScan.Comparison (svdLabelPrecision k p) (svdLabelPrecision_ge_two k p))
    (hn : 2 ≤ n + 1) (hk : 1 ≤ k) (hguard : precisionGuard (n + 1) p)
    (hI : StrictMono I) (call : TridiagonalCall n k p)
    (hcall : prepareTridiagonalCall upper a b I cmp hn hk hguard hI = some call)
    {r : ℤ} (hr : normalizationExponent a b = some r) :
    Monotone call.label ∧ (∀ j, 0 ≤ call.label j) := by
  simp only [prepareTridiagonalCall] at hcall
  obtain ⟨pre, hlen, hpre, rfl⟩ := Option.pmap_eq_some_iff.mp hcall
  simp only [preprocessBidiagonal, hr, Option.map_some, Option.some.injEq] at hpre
  subst pre
  let C := storedBidiagonalWord upper (fun i => (a i).scale (-r)) (fun i => (b i).scale (-r))
  obtain ⟨_, hnonneg, hsort, _, _, _⟩ := bidiagonalCachedLabels_spec (by omega) upper C I hI
    (scaledBidiagonal_support upper a b r) (scaledBidiagonal_bounds upper a b hr).1
  change Monotone (fun j : Fin k => ((bidiagonalCachedLabels (by omega) upper C I).get
      (Fin.cast hlen.symm j)).val) ∧
    (∀ j : Fin k, 0 ≤ ((bidiagonalCachedLabels (by omega) upper C I).get (Fin.cast hlen.symm j)).val)
  refine ⟨?_, fun j => hnonneg _ (List.get_mem _ _)⟩
  intro i j hij
  rcases lt_or_eq_of_le hij with hij | rfl
  · exact List.pairwise_iff_get.mp hsort _ _ (show Fin.cast hlen.symm i < Fin.cast hlen.symm j from hij)
  · rfl

private theorem cut_upper_budget (k p : ℕ) (hk : 1 ≤ k) :
    ((k : ℝ) + 1) * svdAlpha k p ≤ 2 * unitRoundoff p := by
  have hκ : (k : ℝ) ≤ svdKappa k := by exact_mod_cast le_svdKappa k
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hκ' : (0 : ℝ) < svdKappa k := by linarith
  rw [svdAlpha, ← mul_div_assoc]
  apply (div_le_iff₀ hκ').mpr
  have h := mul_le_mul_of_nonneg_right (show (k : ℝ) + 1 ≤ 2 * svdKappa k by linarith)
    (unitRoundoff_pos p).le
  nlinarith only [h]

private theorem singularValue_le_norm (C : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (i : Fin (n + 1)) :
    ascendingRealSpectrum C i ≤ ‖C‖ := by
  change ascendingRealSpectrum C i ≤ realMatrixOperatorNorm C
  rw [ascendingRealSpectrum, rectSingularValue_eq_canonical,
    realMatrixOperatorNorm_eq_complexMatrixOp2_realRectToCMatrix]
  exact complexMatrixSingularValue_le_complexMatrixOp2 _ _

/-- The nonzero stored bidiagonal path has the stated output accuracy for every
successful return of the one packed tridiagonal solve. -/
theorem prepared_solve_finish_accuracy (hp : 2 ≤ p) (upper : Bool)
    (a : Fin (n + 1) → Word p hp) (b : Fin n → Word p hp) (I : Fin k → Fin (n + 1))
    (cmp : EmptyBinScan.Comparison (svdLabelPrecision k p) (svdLabelPrecision_ge_two k p))
    (hn : 2 ≤ n + 1) (hk : 1 ≤ k) (hguard : precisionGuard (n + 1) p)
    (hI : StrictMono I) {r : ℤ} (hr : normalizationExponent a b = some r)
    (call : TridiagonalCall n k p)
    (hprep : prepareTridiagonalCall upper a b I cmp hn hk hguard hI = some call)
    (bits : ℕ → GateBits (edgeCount n) call.oneBasedRanks) (out : call.NativeParities)
    (hrun : call.solveParities upper hk hguard bits = some out) :
    ∃ (hL : ∀ j, Word.euclidean (out.left.get j).get ≠ 0)
      (hR : ∀ j, Word.euclidean (out.right.get j).get ≠ 0),
      ReturnedTripletAccuracy (storedBidiagonal upper a b) I (call.finish (hp := hp) out hL hR) := by
  obtain ⟨prepared, hprepared, hslots, hexp, hlabel, hfirst, hlast, hlower, hupper,
    hlow, _, hhigh, hmatrix⟩ := prepareTridiagonalCall_spec upper a b I cmp hn hk hguard hI hr
  have he : prepared = call := Option.some.inj (hprepared.symm.trans hprep)
  subst prepared
  let C := scaledBidiagonal upper a b r
  let B := storedBidiagonal upper a b
  let cut := call.preprocessing.cutExecution.result.state
  let R := (2 : ℝ) ^ r
  have hR : 0 < R := by dsimp [R]; positivity
  have hB : B = (2 : ℝ) ^ call.preprocessing.scaleExponent • C := by
    change B = (2 : ℝ) ^ call.preprocessing.scaleExponent • scaledBidiagonal upper a b r
    rw [hexp, scaledBidiagonal_eq, smul_smul, mul_inv_cancel₀ hR.ne', one_smul]
  obtain ⟨_, hCnorm, hscale⟩ := scaledBidiagonal_bounds upper a b hr
  obtain ⟨hmono, hnonneg⟩ := cachedLabel_order upper a b I cmp hn hk hguard hI call hprep hr
  have hα : 0 ≤ svdAlpha k p := (svd_precision_budgets k p).1.le
  have hcut : svdAlpha k p ≤ cut.lower.val := by
    rw [hlower]
    have h : (1 : ℝ) ≤ cut.j := by exact_mod_cast hfirst
    simpa only [one_mul] using mul_le_mul_of_nonneg_right h hα
  have hcut' : cut.lower.val ≤ 2 * unitRoundoff p := by
    rw [hlower]
    refine (mul_le_mul_of_nonneg_right ?_ hα).trans (cut_upper_budget k p hk)
    exact_mod_cast hlast
  have hends : cut.lower.val + svdAlpha k p = cut.upper.val := by
    rw [hlower, hupper, Nat.cast_add, Nat.cast_one, add_mul, one_mul]
  have hlabel' (j : Fin k) : |call.label j - ascendingRealSpectrum C (call.slots j)| ≤
      unitRoundoff (svdAuxiliaryPrecision k p) / 64 := by rw [hslots]; exact hlabel j
  have hsmall := (svd_normalization_roundoff_budget (k := k) hn hguard).2.2.2.1
  have hmax (j : Fin k) : call.label j ≤ 3 / 4 := by
    have hc : ‖C‖ ≤ 1 / 2 := hCnorm
    have hl : |call.label j - ascendingRealSpectrum C (I j)| ≤
      unitRoundoff (svdAuxiliaryPrecision k p) / 64 := hlabel j
    linarith only [(abs_le.mp hl).2, singularValue_le_norm C (I j), hc, hsmall]
  obtain ⟨hx, hy, hacc⟩ := call.solve_finish_accuracy hp upper B C hB
    (by rw [hexp]; exact hscale) (scaledBidiagonal_support upper a b r) hCnorm hmatrix
    hmono hnonneg hmax hlabel' cut.lower.val hcut hcut'
    (fun j hj => hends ▸ (hhigh j hj).1) (fun j hj => ((hlow j).mp hj).le)
    hn hk hguard bits out hrun
  refine ⟨hx, hy, ?_⟩
  rw [show (call.slots : Fin k → Fin (n + 1)) = I from funext hslots] at hacc
  exact hacc

end TridiagonalCall
end
end NumStability.CertifiedTridiagonalEigenpairs.BidiagonalSVDRequest
