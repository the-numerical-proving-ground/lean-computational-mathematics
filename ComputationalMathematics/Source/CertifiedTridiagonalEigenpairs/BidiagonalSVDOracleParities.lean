import ComputationalMathematics.Source.CertifiedTridiagonalEigenpairs.BidiagonalSVDOracle
import ComputationalMathematics.HDP.Matrix.ReindexSpectral
import ComputationalMathematics.Analysis.MatrixStructure.Bipartite.MassParityGrams

/-!
# The two parities from a single native oracle output

The tridiagonal solver returns columns in increasing requested rank. The
bidiagonal solver reads those same stored words in the original requested
singular-rank order and keeps the signed analysis labels in oracle order.
-/

open Matrix NumStability.Matrix.Bipartite
open scoped Matrix.Norms.L2Operator

namespace NumStability.CertifiedTridiagonalEigenpairs.BidiagonalSVDRequest

open FloatingPointFormat.UnboundedBinary NoisyRankCertificate WithLp

namespace TridiagonalCall

variable {n k p : ℕ}

/-- The native output type for precisely this tridiagonal request. -/
abbrev OracleOutput (call : TridiagonalCall n k p) :=
  NativeAcceptedEigenpairs (edgeCount n) (svdAuxiliaryPrecision k p)
    call.oneBasedRanks (auxiliaryPrecision_ge_two k p)

/-- The return array's ascending request scan agrees with the bidiagonal rank plan. -/
theorem requestedRankOrder_eq (call : TridiagonalCall n k p) :
    (requestedRankOrder call.oneBasedRanks_subset : Fin call.oneBasedRanks.card →
      Fin (edgeCount n + 1)) =
      call.orderedIndices ∘ Fin.cast call.oneBasedRanks_card := by
  apply (StrictMono.range_inj (requestedRankOrder call.oneBasedRanks_subset).strictMono
      (call.orderedIndices_strictMono.comp (fun _ _ h => h))).mp
  ext j
  rw [Set.mem_range, Set.mem_range, requestedRankOrder_covers]
  constructor
  · intro hj
    obtain ⟨i, hi, hval⟩ := Finset.mem_map.mp hj
    obtain ⟨t, _, ht⟩ := Finset.mem_map.mp hi
    refine ⟨Fin.cast call.oneBasedRanks_card.symm (outputIndex call.slots call.low t), ?_⟩
    apply Fin.ext
    change (orderedRanks call.slots call.low
      (Fin.cast call.oneBasedRanks_card
        (Fin.cast call.oneBasedRanks_card.symm (outputIndex call.slots call.low t)))).val = j.val
    rw [Fin.cast_cast, Fin.cast_eq_self, orderedRanks_outputIndex, ht]
    exact Nat.add_right_cancel hval
  · rintro ⟨i, rfl⟩
    exact call.orderedIndices_mem_oneBasedRanks _

/-- The corresponding column position in the native tridiagonal result. -/
def oracleSlot (call : TridiagonalCall n k p) : Column call.low ↪ Fin call.oneBasedRanks.card :=
  (outputIndex call.slots call.low).trans (finCongr call.oneBasedRanks_card.symm).toEmbedding

theorem oracleSlot_surjective (call : TridiagonalCall n k p) :
    Function.Surjective call.oracleSlot :=
  (finCongr call.oneBasedRanks_card.symm).surjective.comp
    (outputIndex_surjective call.slots call.low)

@[simp] theorem requestedRankOrder_oracleSlot (call : TridiagonalCall n k p) (j : Column call.low) :
    requestedRankOrder call.oneBasedRanks_subset (call.oracleSlot j) =
      call.orderedIndices (outputIndex call.slots call.low j) := by
  rw [call.requestedRankOrder_eq]
  change call.orderedIndices (Fin.cast call.oneBasedRanks_card
    (Fin.cast call.oneBasedRanks_card.symm (outputIndex call.slots call.low j))) = _
  rw [Fin.cast_cast, Fin.cast_eq_self]

/-- The positive output positions in original requested order. -/
def positiveSlot (call : TridiagonalCall n k p) : Fin k ↪ Fin call.oneBasedRanks.card :=
  (Function.Embedding.inl : Fin k ↪ Column call.low).trans call.oracleSlot

/-- The negative output positions, indexed by the low original slots. -/
def negativeSlot (call : TridiagonalCall n k p) :
    {j : Fin k // call.low j = true} ↪ Fin call.oneBasedRanks.card :=
  (Function.Embedding.inr : {j : Fin k // call.low j = true} ↪ Column call.low).trans call.oracleSlot

/-- The right output positions, in the same original requested order as the left. -/
def rightSlot (call : TridiagonalCall n k p) (j : Fin k) : Fin call.oneBasedRanks.card :=
  call.oracleSlot (rightColumn call.low j)

@[simp] theorem rightSlot_low (call : TridiagonalCall n k p) (j : Fin k) (h : call.low j = true) :
    call.rightSlot j = call.negativeSlot ⟨j, h⟩ := by
  unfold rightSlot
  rw [rightColumn_low j h]
  rfl

@[simp] theorem rightSlot_high (call : TridiagonalCall n k p) (j : Fin k) (h : call.low j = false) :
    call.rightSlot j = call.positiveSlot j := by
  unfold rightSlot
  rw [rightColumn_high j h]
  rfl

/-- Number of positive right-parity columns. -/
abbrev highCount (call : TridiagonalCall n k p) :=
  Fintype.card {j : Fin k // ¬ call.low j = true}

/-- Number of negative right-parity columns. -/
abbrev lowCount (call : TridiagonalCall n k p) :=
  Fintype.card {j : Fin k // call.low j = true}

noncomputable def highOriginalSlot (call : TridiagonalCall n k p) :
    Fin call.highCount ≃ {j : Fin k // ¬ call.low j = true} :=
  (Fintype.equivFin _).symm

noncomputable def lowOriginalSlot (call : TridiagonalCall n k p) :
    Fin call.lowCount ≃ {j : Fin k // call.low j = true} :=
  (Fintype.equivFin _).symm

/-- Translate between original request order and the high/low grouped proof arrays. -/
noncomputable def group (call : TridiagonalCall n k p) : Fin k ≃ Fin call.highCount ⊕ Fin call.lowCount :=
  ((Equiv.sumComm _ _).trans
    ((Equiv.sumCongr call.lowOriginalSlot call.highOriginalSlot).trans (Equiv.sumCompl _))).symm

@[simp] theorem group_symm_high (call : TridiagonalCall n k p) (j : Fin call.highCount) :
    call.group.symm (Sum.inl j) = (call.highOriginalSlot j).val :=
  rfl

@[simp] theorem group_symm_low (call : TridiagonalCall n k p) (j : Fin call.lowCount) :
    call.group.symm (Sum.inr j) = (call.lowOriginalSlot j).val :=
  rfl

noncomputable def highSlot (call : TridiagonalCall n k p) :
    Fin call.highCount ↪ Fin call.oneBasedRanks.card :=
  call.highOriginalSlot.toEmbedding.trans ((Function.Embedding.subtype _).trans call.positiveSlot)

noncomputable def lowSlot (call : TridiagonalCall n k p) :
    Fin call.lowCount ↪ Fin call.oneBasedRanks.card :=
  call.lowOriginalSlot.toEmbedding.trans call.negativeSlot

theorem rightSlot_group (call : TridiagonalCall n k p) (j : Fin call.highCount ⊕ Fin call.lowCount) :
    call.rightSlot (call.group.symm j) = Sum.elim call.highSlot call.lowSlot j := by
  cases j with
  | inl t =>
    have h : call.low (call.highOriginalSlot t).val = false :=
      Bool.eq_false_iff.mpr (call.highOriginalSlot t).property
    rw [group_symm_high, rightSlot_high _ _ h]
    rfl
  | inr t =>
    rw [group_symm_low, rightSlot_low _ _ (call.lowOriginalSlot t).property]
    rfl

/-- The physical reindexing includes the successor cast used by the packed call. -/
def parityRows (n : ℕ) (upper : Bool) :
    Fin (edgeCount n + 1) ≃ (Fin (n + 1) ⊕ Fin (n + 1)) :=
  (bidiagonalRefinementCoord (n := n + 1) (by omega)).trans (bidiagonalParityCoord upper (n + 1))

/-- Actual native left-parity words returned by the single solve. -/
def leftWords (call : TridiagonalCall n k p) (upper : Bool) (out : call.OracleOutput)
    (j : Fin k) (i : Fin (n + 1)) : AuxWord k p :=
  (out.pairs.get (call.positiveSlot j)).column.get ((parityRows n upper).symm (Sum.inl i))

/-- Actual native right-parity words from the same solve. -/
def rightWords (call : TridiagonalCall n k p) (upper : Bool) (out : call.OracleOutput)
    (j : Fin k) (i : Fin (n + 1)) : AuxWord k p :=
  (out.pairs.get (call.rightSlot j)).column.get ((parityRows n upper).symm (Sum.inr i))

/-- The native parity arrays retain their common tridiagonal output. -/
structure NativeParities (call : TridiagonalCall n k p) where
  oracle : call.OracleOutput
  left : Vector (Vector (AuxWord k p) (n + 1)) k
  right : Vector (Vector (AuxWord k p) (n + 1)) k

/-- Materialize both native parities in original requested order. Each column
position is looked up once for each selected parity column. -/
def extractParities (call : TridiagonalCall n k p) (upper : Bool)
    (out : call.OracleOutput) : call.NativeParities :=
  let rows := (parityRows n upper).symm
  let left := Vector.ofFn fun j =>
    let col := (out.pairs.get (call.positiveSlot j)).column
    Vector.ofFn fun i => col.get (rows (Sum.inl i))
  let right := Vector.ofFn fun j =>
    let col := (out.pairs.get (call.rightSlot j)).column
    Vector.ofFn fun i => col.get (rows (Sum.inr i))
  ⟨out, left, right⟩

/-- Call the tridiagonal solver once and copy the two parity arrays from its response. -/
noncomputable def solveParities (call : TridiagonalCall n k p) (upper : Bool)
    (hk : 1 ≤ k) (hguard : precisionGuard (n + 1) p)
    (bits : ℕ → GateBits (edgeCount n) call.oneBasedRanks) : Option call.NativeParities :=
  (call.solve hk hguard bits).map (call.extractParities upper)

theorem solveParities_native (call : TridiagonalCall n k p) (upper : Bool)
    (hk : 1 ≤ k) (hguard : precisionGuard (n + 1) p)
    (bits : ℕ → GateBits (edgeCount n) call.oneBasedRanks) (out : call.NativeParities)
    (hrun : call.solveParities upper hk hguard bits = some out) :
    call.solve hk hguard bits = some out.oracle ∧
      (∀ j i, (out.left.get j).get i = call.leftWords upper out.oracle j i) ∧
      (∀ j i, (out.right.get j).get i = call.rightWords upper out.oracle j i) := by
  obtain ⟨raw, hraw, rfl⟩ := Option.map_eq_some_iff.mp hrun
  have hget {m : ℕ} {β : Type} (f : Fin m → β) (i : Fin m) :
      (Vector.ofFn f).get i = f i := Vector.getElem_ofFn i.isLt
  refine ⟨hraw, ?_, ?_⟩
  · intro j i
    simp only [extractParities, leftWords, hget]
  · intro j i
    simp only [extractParities, rightWords, hget]

/-- The signed analysis labels in the actual native return array's order. -/
noncomputable def proofLabels (call : TridiagonalCall n k p) :
    Fin call.oneBasedRanks.card → ℝ :=
  assignedLabels call.slots call.low (svdAlpha k p) call.label ∘ Fin.cast call.oneBasedRanks_card

@[simp] theorem proofLabels_oracleSlot (call : TridiagonalCall n k p) (j : Column call.low) :
    call.proofLabels (call.oracleSlot j) = signedMass call.low (svdAlpha k p) call.label j := by
  change assignedLabels call.slots call.low (svdAlpha k p) call.label
    (Fin.cast call.oneBasedRanks_card
      (Fin.cast call.oneBasedRanks_card.symm (outputIndex call.slots call.low j))) = _
  rw [Fin.cast_cast, Fin.cast_eq_self, assignedLabels_outputIndex]

@[simp] theorem proofLabels_positiveSlot (call : TridiagonalCall n k p) (j : Fin k) :
    call.proofLabels (call.positiveSlot j) = massMagnitude (svdAlpha k p) (call.label j) :=
  call.proofLabels_oracleSlot (Sum.inl j)

@[simp] theorem proofLabels_highSlot (call : TridiagonalCall n k p) (j : Fin call.highCount) :
    call.proofLabels (call.highSlot j) =
      massMagnitude (svdAlpha k p) (call.label (call.highOriginalSlot j).val) :=
  call.proofLabels_oracleSlot (Sum.inl (call.highOriginalSlot j).val)

@[simp] theorem proofLabels_lowSlot (call : TridiagonalCall n k p) (j : Fin call.lowCount) :
    call.proofLabels (call.lowSlot j) =
      -massMagnitude (svdAlpha k p) (call.label (call.lowOriginalSlot j).val) :=
  call.proofLabels_oracleSlot (Sum.inr (call.lowOriginalSlot j))

/-- Exact left parity of the witness column used by the algorithm. -/
def leftExact (call : TridiagonalCall n k p)
    (W : Matrix (Fin (n + 1) ⊕ Fin (n + 1)) (Fin call.oneBasedRanks.card) ℝ) :
    Matrix (Fin (n + 1)) (Fin k) ℝ :=
  W.submatrix Sum.inl call.positiveSlot

/-- Exact right parity of the same witness, in original requested order. -/
def rightExact (call : TridiagonalCall n k p)
    (W : Matrix (Fin (n + 1) ⊕ Fin (n + 1)) (Fin call.oneBasedRanks.card) ℝ) :
    Matrix (Fin (n + 1)) (Fin k) ℝ :=
  W.submatrix Sum.inr call.rightSlot

/-- Restricting an L2 vector to the injectively indexed coordinates of one parity
can only decrease its norm. -/
private theorem restrict_norm_le {β γ : Type*} [Fintype β] [Fintype γ]
    (e : β ↪ γ) (x : EuclideanSpace ℝ γ) :
    ‖toLp 2 (fun i => x (e i))‖ ≤ ‖x‖ := by
  classical
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp only [EuclideanSpace.norm_sq_eq]
  calc
    _ = ∑ j ∈ (Finset.univ : Finset β).map e, ‖x j‖ ^ 2 :=
      (Finset.sum_map _ _ (fun j => ‖x j‖ ^ 2)).symm
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      fun _ _ _ => by positivity

/-- The output labels move by less than 17 auxiliary roundoffs when replaced
with the analysis labels at the original singular-rank slots. -/
theorem proofLabels_error (call : TridiagonalCall n k p) (upper : Bool)
    (C : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (hC : bidiagonalSupport upper C)
    (hcall : call.matrix = (bidiagonalMassShift upper C (svdAlpha k p)).submatrix
      (bidiagonalRefinementCoord (by omega)) (bidiagonalRefinementCoord (by omega)))
    (hCnorm : realMatrixOperatorNorm C ≤ 1 / 2) (hp : 2 ≤ p)
    (hs : ∀ j, |call.label j - ascendingRealSpectrum C (call.slots j)| ≤
      unitRoundoff (svdAuxiliaryPrecision k p) / 64)
    (out : call.OracleOutput)
    (haccuracy : ReturnedAccuracy (requestedRankOrder call.oneBasedRanks_subset)
      call.matrix call.matrix_isHermitian out.columns out.labels
      (unitRoundoff (svdAuxiliaryPrecision k p))) (j : Fin call.oneBasedRanks.card) :
    |out.labels j - call.proofLabels j| < 17 * unitRoundoff (svdAuxiliaryPrecision k p) := by
  let ε := unitRoundoff (svdAuxiliaryPrecision k p)
  have hε : 0 < ε := unitRoundoff_pos _
  obtain ⟨j, rfl⟩ := call.oracleSlot_surjective j
  have h := haccuracy.1 (call.oracleSlot j)
  rw [call.requestedRankOrder_oracleSlot, call.selectedEigenvalue upper C hC hcall] at h
  rw [call.proofLabels_oracleSlot]
  have hn : ‖call.matrix‖ ≤ 1 := (call.operatorNorm_le hp upper C hC hCnorm hcall).2.le
  have h' := (signedMass_error call.low (svdAlpha k p) hs j)
  rw [abs_sub_comm] at h'
  calc
    _ ≤ _ := abs_sub_le _ (signedMass call.low (svdAlpha k p) (ascendingRealSpectrum C ∘ call.slots) j) _
    _ ≤ 16 * ε * ‖call.matrix‖ + ε / 64 := add_le_add h h'
    _ ≤ 16 * ε + ε / 64 := by
      refine add_le_add ?_ le_rfl
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hn (show 0 ≤ 16 * ε by positivity)
    _ < _ := by linarith

private theorem reindexed_call_matrix (call : TridiagonalCall n k p) (upper : Bool)
    (C : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (hC : bidiagonalSupport upper C)
    (hcall : call.matrix = (bidiagonalMassShift upper C (svdAlpha k p)).submatrix
      (bidiagonalRefinementCoord (by omega)) (bidiagonalRefinementCoord (by omega))) :
    Matrix.reindex (parityRows n upper) (parityRows n upper) call.matrix =
      massShift C (svdAlpha k p) := by
  rw [hcall, bidiagonalMassShift_eq_reindexed upper C _ hC]
  ext i j
  change massShift C (svdAlpha k p) (parityRows n upper ((parityRows n upper).symm i))
    (parityRows n upper ((parityRows n upper).symm j)) = _
  rw [(parityRows n upper).apply_symm_apply i, (parityRows n upper).apply_symm_apply j]

/-- Every successful solve supplies one common exact witness for both native
parities. The assigned-label residual and both per-column storage errors are
measured for that witness in the original left/right coordinates. -/
theorem solve_parity_witness (call : TridiagonalCall n k p) (upper : Bool)
    (C : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (hC : bidiagonalSupport upper C)
    (hcall : call.matrix = (bidiagonalMassShift upper C (svdAlpha k p)).submatrix
      (bidiagonalRefinementCoord (by omega)) (bidiagonalRefinementCoord (by omega)))
    (hCnorm : realMatrixOperatorNorm C ≤ 1 / 2) (hp : 2 ≤ p)
    (hs : ∀ j, |call.label j - ascendingRealSpectrum C (call.slots j)| ≤
      unitRoundoff (svdAuxiliaryPrecision k p) / 64)
    (hk : 1 ≤ k) (hguard : precisionGuard (n + 1) p)
    (bits : ℕ → GateBits (edgeCount n) call.oneBasedRanks) (out : call.OracleOutput)
    (hrun : call.solve hk hguard bits = some out) :
    let ε := unitRoundoff (svdAuxiliaryPrecision k p)
    ∃ W : Matrix (Fin (n + 1) ⊕ Fin (n + 1)) (Fin call.oneBasedRanks.card) ℝ,
      Wᵀ * W = 1 ∧ ‖massShift C (svdAlpha k p) * W - W * Matrix.diagonal call.proofLabels‖ ≤ 64 * ε ∧
      (∀ j, ‖Word.euclidean (call.leftWords upper out j) -
        toLp 2 ((call.leftExact W).col j)‖ ≤ 4 * ε) ∧
      (∀ j, ‖Word.euclidean (call.rightWords upper out j) -
        toLp 2 ((call.rightExact W).col j)‖ ≤ 4 * ε) := by
  dsimp only
  let ε := unitRoundoff (svdAuxiliaryPrecision k p)
  have hε : 0 < ε := unitRoundoff_pos _
  let e := parityRows n upper
  let A := massShift C (svdAlpha k p)
  let D := Matrix.diagonal out.labels
  let Λ := Matrix.diagonal call.proofLabels
  have haccuracy := call.solve_accuracy hk hguard bits out hrun
  have herr := call.proofLabels_error upper C hC hcall hCnorm hp hs out haccuracy
  obtain ⟨B, _, V, hback, horth, _, hV⟩ := haccuracy.2.2.2.2.2
  let Z : Matrix (Fin (edgeCount n + 1)) (Fin call.oneBasedRanks.card) ℝ :=
    Matrix.of fun i j => V j i
  let W := Z.submatrix e.symm id
  let B' := Matrix.reindex e e B
  have hZ : Zᵀ * Z = 1 := by
    ext i j
    calc
      _ = (V j).ofLp ⬝ᵥ star (V i).ofLp := by
        rw [star_trivial, dotProduct_comm]
        rfl
      _ = inner ℝ (V i) (V j) := (EuclideanSpace.inner_eq_star_dotProduct (V i) (V j)).symm
      _ = if i = j then 1 else 0 := (orthonormal_iff_ite.mp horth) i j
      _ = _ := Matrix.one_apply.symm
  have hW : Wᵀ * W = 1 := by
    change (Z.submatrix e.symm id)ᵀ * Z.submatrix e.symm id = 1
    rw [transpose_submatrix, ← Matrix.submatrix_mul _ _ _ _ _ e.symm.bijective, hZ, submatrix_id_id]
  have heig : B * Z = Z * D := by
    ext i j
    have he := congrArg (fun z : EuclideanSpace ℝ (Fin (edgeCount n + 1)) => z i) (hV j).1
    rw [Matrix.mul_diagonal]
    simpa [Z, D, Matrix.mul_apply, Matrix.toLpLin_apply, Matrix.mulVec, dotProduct,
      PiLp.smul_apply, smul_eq_mul, mul_comm] using he
  have heig' : B' * W = W * D := by
    change B.submatrix e.symm e.symm * Z.submatrix e.symm id = Z.submatrix e.symm id * D
    rw [← Matrix.submatrix_mul _ _ _ _ _ e.symm.bijective, heig,
      Matrix.submatrix_mul _ _ _ _ _ Function.bijective_id, submatrix_id_id]
  have hnorm : ‖W‖ ≤ 1 := MassParityGrams.norm_le_one_of_orthonormal _ hW
  have hnormA : ‖call.matrix‖ ≤ 1 := (call.operatorNorm_le hp upper C hC hCnorm hcall).2.le
  have hBack : ‖A - B'‖ ≤ 24 * ε := by
    have heA : Matrix.reindex e e call.matrix = A := call.reindexed_call_matrix upper C hC hcall
    have heB : A - B' = Matrix.reindex e e (call.matrix - B) := by
      rw [← heA]
      rfl
    rw [heB, NumStability.HDP.Matrix.l2_opNorm_reindex, norm_sub_rev]
    exact hback.trans (by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hnormA (show 0 ≤ 24 * ε by positivity))
  have hD : ‖D - Λ‖ ≤ 17 * ε := by
    change ‖Matrix.diagonal out.labels - Matrix.diagonal call.proofLabels‖ ≤ 17 * ε
    rw [diagonal_sub, l2_opNorm_diagonal]
    exact (pi_norm_le_iff_of_nonneg (by positivity)).2 fun j =>
      (Real.norm_eq_abs _).trans_le (herr j).le
  refine ⟨W, hW, ?_, ?_, ?_⟩
  · change ‖A * W - W * Λ‖ ≤ 64 * ε
    have he : A * W - W * Λ = (A - B') * W + W * (D - Λ) := by
      rw [Matrix.sub_mul, Matrix.mul_sub, ← heig']
      abel
    rw [he]
    calc
      _ ≤ ‖(A - B') * W‖ + ‖W * (D - Λ)‖ := norm_add_le ..
      _ ≤ ‖A - B'‖ * ‖W‖ + ‖W‖ * ‖D - Λ‖ := add_le_add (Matrix.l2_opNorm_mul _ _) (Matrix.l2_opNorm_mul _ _)
      _ ≤ 24 * ε + 17 * ε := by
        exact add_le_add ((mul_le_of_le_one_right (norm_nonneg _) hnorm).trans hBack)
          ((mul_le_of_le_one_left (norm_nonneg _) hnorm).trans hD)
      _ ≤ _ := by linarith
  · intro j
    let ix := call.positiveSlot j
    let f : Fin (n + 1) ↪ Fin (edgeCount n + 1) :=
      Function.Embedding.inl.trans e.symm.toEmbedding
    change ‖toLp 2 (fun i => (toLp 2 (out.columns.col ix) - V ix) (f i))‖ ≤ 4 * ε
    exact (restrict_norm_le f _).trans (hV ix).2.2
  · intro j
    let ix := call.rightSlot j
    let f : Fin (n + 1) ↪ Fin (edgeCount n + 1) :=
      Function.Embedding.inr.trans e.symm.toEmbedding
    change ‖toLp 2 (fun i => (toLp 2 (out.columns.col ix) - V ix) (f i))‖ ≤ 4 * ε
    exact (restrict_norm_le f _).trans (hV ix).2.2

/-- The materialized native arrays preserve the common proof witness and
the per-column bounds of the single underlying solve. -/
theorem solveParities_witness (call : TridiagonalCall n k p) (upper : Bool)
    (C : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (hC : bidiagonalSupport upper C)
    (hcall : call.matrix = (bidiagonalMassShift upper C (svdAlpha k p)).submatrix
      (bidiagonalRefinementCoord (by omega)) (bidiagonalRefinementCoord (by omega)))
    (hCnorm : realMatrixOperatorNorm C ≤ 1 / 2) (hp : 2 ≤ p)
    (hs : ∀ j, |call.label j - ascendingRealSpectrum C (call.slots j)| ≤
      unitRoundoff (svdAuxiliaryPrecision k p) / 64)
    (hk : 1 ≤ k) (hguard : precisionGuard (n + 1) p)
    (bits : ℕ → GateBits (edgeCount n) call.oneBasedRanks) (out : call.NativeParities)
    (hrun : call.solveParities upper hk hguard bits = some out) :
    let ε := unitRoundoff (svdAuxiliaryPrecision k p)
    ∃ W : Matrix (Fin (n + 1) ⊕ Fin (n + 1)) (Fin call.oneBasedRanks.card) ℝ,
      Wᵀ * W = 1 ∧ ‖massShift C (svdAlpha k p) * W - W * Matrix.diagonal call.proofLabels‖ ≤ 64 * ε ∧
      (∀ j, ‖Word.euclidean (out.left.get j).get -
        toLp 2 ((call.leftExact W).col j)‖ ≤ 4 * ε) ∧
      (∀ j, ‖Word.euclidean (out.right.get j).get -
        toLp 2 ((call.rightExact W).col j)‖ ≤ 4 * ε) := by
  obtain ⟨hraw, hleft, hright⟩ := call.solveParities_native upper hk hguard bits out hrun
  obtain ⟨W, hW, he, hl, hr⟩ :=
    call.solve_parity_witness upper C hC hcall hCnorm hp hs hk hguard bits out.oracle hraw
  exact ⟨W, hW, he, fun j => (funext (hleft j)).symm ▸ hl j,
    fun j => (funext (hright j)).symm ▸ hr j⟩

end TridiagonalCall

end NumStability.CertifiedTridiagonalEigenpairs.BidiagonalSVDRequest
