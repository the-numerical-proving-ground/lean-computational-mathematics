import ComputationalMathematics.Source.CertifiedTridiagonalEigenpairs.BidiagonalMassShift
import ComputationalMathematics.Source.CertifiedTridiagonalEigenpairs.BidiagonalSVDEmptyBin
import ComputationalMathematics.Analysis.MatrixStructure.Bipartite.MassShiftSpectral
import Mathlib.Data.Finset.Sort

/-!
# Requested ranks and parity columns for the mass-shifted bidiagonal SVD

One rank set contains the positive request for every slot and the negative request for each
low slot. The cut uses a native-word comparison on the stored labels. Signed mass magnitudes
are used to identify the spectral ranks and to describe the proof labels.
-/

namespace NumStability.CertifiedTridiagonalEigenpairs.BidiagonalSVDRequest

open Matrix NumStability.Matrix.Bipartite
open FloatingPointFormat.UnboundedBinary
open FloatingPointFormat.UnboundedBinary.EmptyBinScan
open FloatingPointFormat.UnboundedBinary.EmptyBinScan.SourceWork (runStored)

variable {n k p : ℕ}

/-- The positive columns have one entry for every slot and the negative columns are indexed
by the low slots. Slots are in requested-singular-rank order. -/
abbrev Column (low : Fin k → Bool) := Fin k ⊕ {j : Fin k // low j = true}

/-- Ascending zero-based eigenvalue ranks in the shifted tridiagonal. -/
def rank (I : Fin k ↪ Fin n) (low : Fin k → Bool) : Column low ↪ Fin (n + n) where
  toFun := Sum.elim (fun j => Fin.natAdd n (I j)) (fun j => Fin.castAdd n (I j.val).rev)
  inj' := by
    intro a b hab
    cases a with
    | inl i =>
      cases b with
      | inl j => exact congrArg Sum.inl (I.injective (Fin.natAdd_injective n n hab))
      | inr j =>
        have h := congrArg Fin.val hab
        have hj := (I j.val).rev.isLt
        change n + (I i).val = (I j.val).rev.val at h
        omega
    | inr i =>
      cases b with
      | inl j =>
        have h := congrArg Fin.val hab
        have hi := (I i.val).rev.isLt
        change (I i.val).rev.val = n + (I j).val at h
        omega
      | inr j =>
        exact congrArg Sum.inr (Subtype.ext (I.injective
          (Fin.rev_injective (Fin.castAdd_injective n n hab))))

/-- The positive request at the one-based source rank `n+i`. -/
theorem positive_rank_oneBased (I : Fin k ↪ Fin n) (low : Fin k → Bool) (j : Fin k) :
    (rank I low (Sum.inl j)).val + 1 = n + ((I j).val + 1) := by
  change n + (I j).val + 1 = _
  omega

/-- The negative request at the one-based source rank `n-i+1`. -/
theorem negative_rank_oneBased (I : Fin k ↪ Fin n) (low : Fin k → Bool)
    (j : {j : Fin k // low j = true}) :
    (rank I low (Sum.inr j)).val + 1 = n - ((I j.val).val + 1) + 1 := rfl

/-- The distinct ranks supplied together to the tridiagonal call. -/
def rankSet (I : Fin k ↪ Fin n) (low : Fin k → Bool) : Finset (Fin (n + n)) :=
  Finset.univ.map (rank I low)

theorem mem_rankSet_iff (I : Fin k ↪ Fin n) (low : Fin k → Bool) (a : Fin (n + n)) :
    a ∈ rankSet I low ↔ (∃ j, Fin.natAdd n (I j) = a) ∨
      (∃ j, low j = true ∧ Fin.castAdd n (I j).rev = a) := by
  rw [rankSet, Finset.mem_map]
  constructor
  · rintro ⟨j, -, hj⟩
    cases j with
    | inl i => exact Or.inl ⟨i, hj⟩
    | inr i => exact Or.inr ⟨i.val, i.property, hj⟩
  · rintro (⟨i, hi⟩ | ⟨i, hlow, hi⟩)
    · exact ⟨Sum.inl i, Finset.mem_univ _, hi⟩
    · exact ⟨Sum.inr ⟨i, hlow⟩, Finset.mem_univ _, hi⟩

theorem card_rankSet (I : Fin k ↪ Fin n) (low : Fin k → Bool) :
    (rankSet I low).card = k + Fintype.card {j : Fin k // low j = true} := by
  simp [rankSet]

theorem card_rankSet_bounds (I : Fin k ↪ Fin n) (low : Fin k → Bool) :
    k ≤ (rankSet I low).card ∧ (rankSet I low).card ≤ 2 * k := by
  have h := Fintype.card_le_of_injective (Subtype.val : {j : Fin k // low j = true} → Fin k)
    Subtype.val_injective
  rw [Fintype.card_fin] at h
  rw [card_rankSet]
  omega

/-- A single strictly increasing input to the tridiagonal call, in ascending rank order. -/
def orderedRanks (I : Fin k ↪ Fin n) (low : Fin k → Bool) :
    Fin (rankSet I low).card ↪o Fin (n + n) :=
  (rankSet I low).orderEmbOfFin rfl

/-- Locate each parity-designated column in the ordered output of the single call. -/
def outputIndex (I : Fin k ↪ Fin n) (low : Fin k → Bool) :
    Column low ↪ Fin (rankSet I low).card where
  toFun j := ((rankSet I low).orderIsoOfFin rfl).symm
    ⟨rank I low j, Finset.mem_map.mpr ⟨j, Finset.mem_univ _, rfl⟩⟩
  inj' := by
    intro i j hij
    apply (rank I low).injective
    exact congrArg Subtype.val (((rankSet I low).orderIsoOfFin rfl).symm.injective hij)

@[simp] theorem orderedRanks_outputIndex (I : Fin k ↪ Fin n) (low : Fin k → Bool)
    (j : Column low) : orderedRanks I low (outputIndex I low j) = rank I low j := by
  change ((rankSet I low).orderIsoOfFin rfl
    (((rankSet I low).orderIsoOfFin rfl).symm _)).val = _
  rw [OrderIso.apply_symm_apply]

theorem outputIndex_surjective (I : Fin k ↪ Fin n) (low : Fin k → Bool) :
    Function.Surjective (outputIndex I low) := by
  apply ((Fintype.bijective_iff_injective_and_card _).mpr ⟨(outputIndex I low).injective, ?_⟩).2
  simp [Column, card_rankSet]

/-- The call uses auxiliary output precision and fits the SVD working-precision budget. -/
theorem call_precision_bounds (I : Fin k ↪ Fin n) (low : Fin k → Bool)
    (hn : 0 < n) (hk : 0 < k) (hguard : precisionGuard n p) :
    precisionGuard (n + n) (svdAuxiliaryPrecision k p) ∧
      workingPrecision (n + n) (rankSet I low).card (svdAuxiliaryPrecision k p) ≤
        svdWorkingPrecision n k p := by
  simpa only [two_mul] using And.intro (svd_tridiagonal_precisionGuard (k := k) hguard)
    (svd_tridiagonal_workingPrecision_le (p := p) hn hk (card_rankSet_bounds I low).2)

/-- The right parity comes from the negative column for a low slot and the positive
column for a high slot. The left parity always comes from the positive column. -/
def rightColumn (low : Fin k → Bool) (j : Fin k) : Column low :=
  if h : low j = true then Sum.inr ⟨j, h⟩ else Sum.inl j

@[simp] theorem rightColumn_low {low : Fin k → Bool} (j : Fin k) (h : low j = true) :
    rightColumn low j = Sum.inr ⟨j, h⟩ := dif_pos h

@[simp] theorem rightColumn_high {low : Fin k → Bool} (j : Fin k) (h : low j = false) :
    rightColumn low j = Sum.inl j := dif_neg (by simp [h])

/-- Left-parity extraction from the ordered call output, in requested-singular-rank order. -/
def leftParity {𝕜 : Type*} (upper : Bool) (I : Fin k ↪ Fin n) (low : Fin k → Bool)
    (Z : Matrix (Fin (n + n)) (Fin (rankSet I low).card) 𝕜) :
    Matrix (Fin n) (Fin k) 𝕜 :=
  Z.submatrix (fun i => (bidiagonalParityCoord upper n).symm (Sum.inl i))
    (fun j => outputIndex I low (Sum.inl j))

/-- Right-parity extraction from that same ordered output, in the same slot order. -/
def rightParity {𝕜 : Type*} (upper : Bool) (I : Fin k ↪ Fin n) (low : Fin k → Bool)
    (Z : Matrix (Fin (n + n)) (Fin (rankSet I low).card) 𝕜) :
    Matrix (Fin n) (Fin k) 𝕜 :=
  Z.submatrix (fun i => (bidiagonalParityCoord upper n).symm (Sum.inr i))
    (fun j => outputIndex I low (rightColumn low j))

/-- The analysis labels, using either the exact singular values or the stored labels. -/
noncomputable def signedMass (low : Fin k → Bool) (α : ℝ) (s : Fin k → ℝ) :
    Column low → ℝ :=
  Sum.elim (fun j => massMagnitude α (s j)) (fun j => -massMagnitude α (s j.val))

theorem orderedRanks_eigenvalue (upper : Bool) (C : Matrix (Fin n) (Fin n) ℝ)
    (hC : bidiagonalSupport upper C) {α : ℝ} (hα : 0 < α)
    (I : Fin k ↪ Fin n) (low : Fin k → Bool) (j : Column low) :
    hermitianOrderedEigenvalue (bidiagonalMassShift_isHermitian upper C α)
      (orderedRanks I low (outputIndex I low j)).rev =
      signedMass low α (ascendingRealSpectrum C ∘ I) j := by
  rw [orderedRanks_outputIndex]
  cases j with
  | inl i => exact (bidiagonalMassShift_signed_ranks upper C α hC hα (I i)).1
  | inr i => exact (bidiagonalMassShift_signed_ranks upper C α hC hα (I i.val)).2

theorem signedMass_error (low : Fin k → Bool) (α : ℝ) {s t : Fin k → ℝ} {δ : ℝ}
    (h : ∀ j, |s j - t j| ≤ δ) (j : Column low) :
    |signedMass low α s j - signedMass low α t j| ≤ δ := by
  cases j with
  | inl i => exact (massMagnitude_sub_le α (s i) (t i)).trans (h i)
  | inr i =>
    change |(-massMagnitude α (s i.val)) - (-massMagnitude α (t i.val))| ≤ δ
    rw [neg_sub_neg, abs_sub_comm]
    exact (massMagnitude_sub_le α (s i.val) (t i.val)).trans (h i)

/-- Signed analysis labels in the order of the single tridiagonal call. -/
noncomputable def assignedLabels (I : Fin k ↪ Fin n) (low : Fin k → Bool)
    (α : ℝ) (s : Fin k → ℝ) : Fin (rankSet I low).card → ℝ :=
  signedMass low α s ∘
    (Equiv.ofBijective (outputIndex I low)
      ⟨(outputIndex I low).injective, outputIndex_surjective I low⟩).symm

@[simp] theorem assignedLabels_outputIndex (I : Fin k ↪ Fin n) (low : Fin k → Bool)
    (α : ℝ) (s : Fin k → ℝ) (j : Column low) :
    assignedLabels I low α s (outputIndex I low j) = signedMass low α s j := by
  simp [assignedLabels]

/-- The indexed oracle values and stored singular-value labels give the source's
pointwise bound for replacing the oracle diagonal by the analysis diagonal. -/
theorem assignedLabels_error (upper : Bool) (C : Matrix (Fin n) (Fin n) ℝ)
    (hC : bidiagonalSupport upper C) {α ε : ℝ} (hα : 0 < α) (hε : 0 < ε)
    (I : Fin k ↪ Fin n) (low : Fin k → Bool) (s : Fin k → ℝ)
    (oracleLabels : Fin (rankSet I low).card → ℝ)
    (hs : ∀ j, |s j - ascendingRealSpectrum C (I j)| ≤ ε / 64)
    (horacle : ∀ j, |oracleLabels j -
        hermitianOrderedEigenvalue (bidiagonalMassShift_isHermitian upper C α)
          (orderedRanks I low j).rev| ≤ 16 * ε) (j : Fin (rankSet I low).card) :
    |oracleLabels j - assignedLabels I low α s j| < 17 * ε := by
  obtain ⟨j, rfl⟩ := outputIndex_surjective I low j
  specialize horacle (outputIndex I low j)
  rw [orderedRanks_eigenvalue upper C hC hα] at horacle
  rw [assignedLabels_outputIndex]
  have h := signedMass_error low α hs j
  rw [abs_sub_comm] at h
  calc
    _ ≤ _ := abs_sub_le _ (signedMass low α (ascendingRealSpectrum C ∘ I) j) _
    _ ≤ 16 * ε + ε / 64 := add_le_add horacle h
    _ < _ := by linarith

/-- Compare each stored label with the cached lower endpoint of the first empty bin. -/
noncomputable def lowFromEmptyBin
    (cmp : Comparison (svdAuxiliaryPrecision k p + 15) (svdBinLabelPrecision_ge_two k p))
    (labels : List (Word (svdAuxiliaryPrecision k p + 15) (svdBinLabelPrecision_ge_two k p)))
    (hlen : labels.length = k) : Fin k → Bool :=
  let lower := (runStored cmp (svdBinWidthWord k p) labels).result.state.lower
  fun j => cmp.lt (labels.get (Fin.cast hlen.symm j)) lower

/-- The plan uses exactly the source's low slots from the cached scan. Its complementary
slots start at or above the upper endpoint, including labels equal to that endpoint. -/
theorem lowFromEmptyBin_spec (hp : 2 ≤ p)
    (cmp : Comparison (svdAuxiliaryPrecision k p + 15) (svdBinLabelPrecision_ge_two k p))
    (labels : List (Word (svdAuxiliaryPrecision k p + 15) (svdBinLabelPrecision_ge_two k p)))
    (hlen : labels.length = k) (hn : 2 ≤ n) (hk : 1 ≤ k) (hkn : k ≤ n)
    (hguard : precisionGuard n p) (hnonneg : ∀ a ∈ labels, 0 ≤ a.val)
    (hsorted : labels.Pairwise (fun a b => a.val ≤ b.val)) (j : Fin k) :
    let s := (labels.get (Fin.cast hlen.symm j)).val
    let cut := (runStored cmp (svdBinWidthWord k p) labels).result.state
    let low := lowFromEmptyBin cmp labels hlen j
    (low = true ↔ s < cut.lower.val) ∧
    (low = true → s ≤ 2 * unitRoundoff p) ∧
    (low = false → cut.upper.val ≤ s ∧ 2 * svdAlpha k p ≤ s) := by
  dsimp only
  let i := Fin.cast hlen.symm j
  obtain ⟨hα, _, _, _, _, _, _, _, _, he₁, he₂, hb, hs, _⟩ :=
    svd_empty_bin_cut n k p hp cmp labels hn hk hkn hlen hguard hnonneg hsorted
  have hc := cmp.correct (labels.get i) (runStored cmp (svdBinWidthWord k p) labels).result.state.lower
  refine ⟨hc, ?_, ?_⟩
  · intro h
    rcases hs i with hlo | hhi
    · exact hlo.2.trans hb
    · have hlo := hc.mp h
      have hlohi : (runStored cmp (svdBinWidthWord k p) labels).result.state.lower.val ≤
          (runStored cmp (svdBinWidthWord k p) labels).result.state.upper.val := by
        rw [he₁, he₂, hα]
        apply mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.le_succ _)
        rw [svdAlpha_eq_unitRoundoff]
        exact (unitRoundoff_pos _).le
      exact False.elim ((not_lt_of_ge (hlohi.trans hhi.1)) hlo)
  · intro h
    rcases hs i with hlo | hhi
    · exact False.elim (Bool.false_ne_true (h ▸ hc.mpr hlo.1))
    · simpa only [hα] using hhi

end NumStability.CertifiedTridiagonalEigenpairs.BidiagonalSVDRequest
