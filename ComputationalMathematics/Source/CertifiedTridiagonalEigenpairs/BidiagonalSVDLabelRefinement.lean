import ComputationalMathematics.Analysis.FloatingPointArithmetic.UnboundedBinary.Widen
import ComputationalMathematics.Source.CertifiedTridiagonalEigenpairs.BidiagonalMassShift
import ComputationalMathematics.Source.CertifiedTridiagonalEigenpairs.BidiagonalSVDPrecision
import ComputationalMathematics.Source.CertifiedTridiagonalEigenpairs.IndexedRefinement.Proof

/-!
# Indexed scalar refinement of the unshifted bidiagonal dilation

The signed coefficients of the physical dilation widen exactly from the input
precision. A request at singular index `i` uses the scalar routine at
ascending eigenvalue index `n + i`, with the paper's auxiliary tolerance.
-/

open Matrix NumStability.Matrix.Bipartite

namespace NumStability.CertifiedTridiagonalEigenpairs

open FloatingPointFormat.UnboundedBinary ScalarWork

/-- The dimension-`2n` dilation written in the scalar routine's successor indexing. -/
def bidiagonalRefinementCoord {n : ℕ} (hn : 0 < n) : Fin (n + n - 1 + 1) ≃ Fin (n + n) :=
  finCongr (by omega)

/-- Scalar working precision for the cached singular values. -/
def svdLabelPrecision (k p : ℕ) : ℕ := svdAuxiliaryPrecision k p + 15

theorem svdLabelPrecision_ge_two (k p : ℕ) : 2 ≤ svdLabelPrecision k p := by
  unfold svdLabelPrecision
  omega

/-- The edge read follows the physical ordering of the two parity sets. -/
private def bidiagonalEdgeWord {p n : ℕ} {hp : 2 ≤ p} (upper : Bool)
    (C : Matrix (Fin n) (Fin n) (Word p hp)) (i : Fin (n + n)) : Word p hp :=
  let D := if upper then C else Cᵀ
  if i.val % 2 = 0 then D (interleaveHalf i) (interleaveHalf i)
  else if h : i.val / 2 + 1 < n then D (interleaveHalf i) ⟨i.val / 2 + 1, h⟩
  else .zero

private theorem bidiagonalEdgeWord_value {p n : ℕ} {hp : 2 ≤ p} (upper : Bool)
    (C : Matrix (Fin n) (Fin n) (Word p hp)) (i : Fin (n + n)) :
    (bidiagonalEdgeWord upper C i).value =
      upperGolubKahanOffdiag (if upper then (fun a b => (C a b).value)
        else (fun a b => (C b a).value)) i := by
  cases upper <;>
    simp only [bidiagonalEdgeWord, Bool.false_eq_true, if_false, ite_true,
      upperGolubKahanOffdiag, transpose_apply] <;>
    split_ifs <;> rfl

private theorem vector_get_ofFn {m : ℕ} {α : Type*} (f : Fin m → α) (i : Fin m) :
    (Vector.ofFn f).get i = f i := Vector.getElem_ofFn i.isLt

/-- The native diagonal is all zeros and the signed edges are copied exactly. -/
def bidiagonalRefinementEdges {p n : ℕ} {hp : 2 ≤ p} (hn : 0 < n) (k : ℕ) (upper : Bool)
    (C : Matrix (Fin n) (Fin n) (Word p hp)) :
    Fin (n + n - 1) → Word (svdLabelPrecision k p) (svdLabelPrecision_ge_two k p) :=
  let edges := Vector.ofFn (fun i : Fin (n + n - 1) =>
    (bidiagonalEdgeWord upper C (bidiagonalRefinementCoord hn i.castSucc)).widen
      (svdLabelPrecision_ge_two k p) (by unfold svdLabelPrecision svdAuxiliaryPrecision; omega))
  edges.get

private theorem bidiagonalMassShift_zero_eq {n : ℕ} (upper : Bool)
    (C : Matrix (Fin n) (Fin n) ℝ) :
    bidiagonalMassShift upper C 0 =
      zeroDiagonalTridiagonal (upperGolubKahanOffdiag (if upper then C else Cᵀ)) := by
  cases upper <;>
    simp [bidiagonalMassShift, upperGolubKahanMassShift, lowerGolubKahanMassShift,
      upperGolubKahan, lowerGolubKahan, upperMassDiagonal, lowerMassDiagonal, Function.comp_def]

/-- The actual native bands denote the same unshifted physical dilation. -/
theorem bidiagonalRefinement_matrix {p n : ℕ} {hp : 2 ≤ p} (hn : 0 < n) (k : ℕ)
    (upper : Bool) (C : Matrix (Fin n) (Fin n) (Word p hp)) :
    sturmTridiagonal (fun _ => (0 : ℝ))
        (fun i => (bidiagonalRefinementEdges hn k upper C i).value) =
      (bidiagonalMassShift upper (fun a b => (C a b).value) 0).submatrix
        (bidiagonalRefinementCoord hn) (bidiagonalRefinementCoord hn) := by
  rw [bidiagonalMassShift_zero_eq]
  let coord := bidiagonalRefinementCoord hn
  let e := fun i => (bidiagonalRefinementEdges hn k upper C i).value
  let D : Matrix (Fin n) (Fin n) ℝ := fun a b => (C a b).value
  let b := upperGolubKahanOffdiag (if upper then D else Dᵀ)
  have he (t : Fin (n + n - 1)) : e t = b (coord t.castSucc) := by
    dsimp only [e, b, D, bidiagonalRefinementEdges]
    rw [vector_get_ofFn, Word.value_widen]
    exact bidiagonalEdgeWord_value upper C _
  have hc (i : Fin (n + n - 1 + 1)) : (coord i).val = i.val := rfl
  ext i j
  change sturmTridiagonal (fun _ => 0) e i j = zeroDiagonalTridiagonal b (coord i) (coord j)
  by_cases hij : i = j
  · subst j
    rw [sturmTridiagonal_diagonal, zeroDiagonalTridiagonal_diag]
  · by_cases hu : i.val + 1 = j.val
    · let t : Fin (n + n - 1) := ⟨i.val, by have h := j.isLt; omega⟩
      have hi : t.castSucc = i := Fin.ext rfl
      have hj : t.succ = j := Fin.ext hu
      rw [← hi, ← hj, sturmTridiagonal_upper, he]
      simp [zeroDiagonalTridiagonal, hc]
    · by_cases hl : j.val + 1 = i.val
      · let t : Fin (n + n - 1) := ⟨j.val, by have h := i.isLt; omega⟩
        have hi : t.succ = i := Fin.ext hl
        have hj : t.castSucc = j := Fin.ext rfl
        rw [← hi, ← hj, sturmTridiagonal_lower, he]
        have hne : t.val ≠ t.val + 1 + 1 := by omega
        simp [zeroDiagonalTridiagonal, hc, hne]
      · rw [sturmTridiagonal_support _ _ i j hij hu hl]
        simp [zeroDiagonalTridiagonal, hc, Ne.symm hu, Ne.symm hl]

/-- Run the actual clipped-count refinement at the paper's precision and requested rank. -/
noncomputable def bidiagonalRefineLabel {p n : ℕ} {hp : 2 ≤ p} (hn : 0 < n) (k : ℕ)
    (upper : Bool) (C : Matrix (Fin n) (Fin n) (Word p hp)) (i : Fin n) :
    TridiagonalRefinementResult (svdLabelPrecision k p) (svdLabelPrecision_ge_two k p) :=
  tridiagonalRefinement (svdAuxiliaryPrecision k p + 7)
    ((bidiagonalRefinementCoord hn).symm (Fin.natAdd n i))
    (fun _ => .zero) (bidiagonalRefinementEdges hn k upper C)

private theorem orderedEigenvalue_castSubmatrix {m d : ℕ} (h : m = d)
    (A : Matrix (Fin d) (Fin d) ℝ) (hA : A.IsHermitian)
    (hB : (A.submatrix (finCongr h) (finCongr h)).IsHermitian) (i : Fin d) :
    hermitianOrderedEigenvalue hB ((finCongr h).symm i).rev = hermitianOrderedEigenvalue hA i.rev := by
  subst d
  simp [finCongr]

private theorem bidiagonalRefinement_edges_bound {p n : ℕ} {hp : 2 ≤ p} (hn : 0 < n) (k : ℕ)
    (upper : Bool) (C : Matrix (Fin n) (Fin n) (Word p hp))
    (hC : ∀ i j, |(C i j).value| ≤ 1 / 4) (i : Fin (n + n - 1)) :
    |(bidiagonalRefinementEdges hn k upper C i).value| ≤ 1 / 4 := by
  unfold bidiagonalRefinementEdges
  rw [vector_get_ofFn, Word.value_widen, bidiagonalEdgeWord_value]
  cases upper
  · exact upperGolubKahanOffdiag_abs_le _ _ (by norm_num) (fun i j => hC j i) _
  · exact upperGolubKahanOffdiag_abs_le _ _ (by norm_num) hC _

/-- The scalar oracle uses the requested unshifted rank, including zero and repeated
singular values. Its own trace and live-word bound are retained. -/
theorem bidiagonalRefineLabel_spec {p n : ℕ} {hp : 2 ≤ p} (hn : 0 < n) (k : ℕ)
    (upper : Bool) (C : Matrix (Fin n) (Fin n) (Word p hp))
    (hs : bidiagonalSupport upper (fun i j => (C i j).value))
    (hC : ∀ i j, |(C i j).value| ≤ 1 / 4) (i : Fin n) :
    let result := bidiagonalRefineLabel hn k upper C i
    |result.label.value - ascendingRealSpectrum (fun i j => (C i j).value) i| ≤
      unitRoundoff (svdAuxiliaryPrecision k p) / 64 ∧
    work result.trace ≤ 68 * (n + n) * (svdAuxiliaryPrecision k p + 7) ∧
    TraceAllowed (svdLabelPrecision k p) result.trace ∧
    storage result.liveWords ≤ 26 * (n + n) := by
  dsimp only
  let D : Matrix (Fin n) (Fin n) ℝ := fun i j => (C i j).value
  let e := bidiagonalRefinementEdges hn k upper C
  let b := fun j => (e j).value
  let a := fun _ : Fin (n + n - 1 + 1) => (0 : ℝ)
  let j := Fin.natAdd n i
  let c := bidiagonalRefinementCoord hn
  have hb : ∀ j, |b j| ≤ 1 / 4 := bidiagonalRefinement_edges_bound hn k upper C hC
  have hnorm : realMatrixOperatorNorm (sturmTridiagonal a b) ≤ 3 / 2 := by
    apply (sturmTridiagonal_operatorNorm_le a b (D := 0) (E := 1 / 4)
      le_rfl (by norm_num) (fun _ => by simp [a]) hb).trans
    norm_num
  have h := indexedRefinement (n + n - 1) (svdAuxiliaryPrecision k p + 7)
    (svdLabelPrecision k p) (svdLabelPrecision_ge_two k p) (c.symm j)
    (fun _ => .zero) e (by omega) (by rfl) hnorm (fun t => (hb t).trans (by norm_num))
  have hM : sturmTridiagonal a b = (bidiagonalMassShift upper D 0).submatrix c c :=
    bidiagonalRefinement_matrix hn k upper C
  have hH := bidiagonalMassShift_isHermitian upper D 0
  have hB : ((bidiagonalMassShift upper D 0).submatrix c c).IsHermitian := by
    rw [← hM]
    exact sturmTridiagonal_isHermitian a b
  have hvalue : NoisyRankCertificate.ascendingEigenvalue (sturmTridiagonal_isHermitian a b)
      (c.symm j) = ascendingRealSpectrum D i := by
    change hermitianOrderedEigenvalue (sturmTridiagonal_isHermitian a b) (c.symm j).rev = _
    calc
      _ = hermitianOrderedEigenvalue hB (c.symm j).rev :=
        orderedEigenvalue_eq_of_charpoly _ _ (congrArg Matrix.charpoly hM) _
      _ = hermitianOrderedEigenvalue hH j.rev := orderedEigenvalue_castSubmatrix _ _ hH hB j
      _ = _ := bidiagonalMassShift_zero_positive_index upper D hs i
  have hd : n + n - 1 + 1 = n + n := by omega
  obtain ⟨_, herr, hstrict, hwork, hallowed, hstorage⟩ := h
  change |(bidiagonalRefineLabel hn k upper C i).label.value -
    NoisyRankCertificate.ascendingEigenvalue (sturmTridiagonal_isHermitian a b) (c.symm j)| ≤ _ at herr
  refine ⟨?_, ?_, hallowed, ?_⟩
  · rw [hvalue] at herr
    apply herr.trans
    calc
      _ ≤ 2 * unitRoundoff (svdAuxiliaryPrecision k p + 7) := hstrict.le
      _ = unitRoundoff (svdAuxiliaryPrecision k p) / 64 := by
        rw [← svd_refinement_tolerance_eq]
        ring
  · simpa only [hd] using hwork
  · simpa only [hd] using hstorage

end NumStability.CertifiedTridiagonalEigenpairs
