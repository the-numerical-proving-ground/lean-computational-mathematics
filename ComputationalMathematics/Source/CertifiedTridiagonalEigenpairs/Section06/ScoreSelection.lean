import ComputationalMathematics.Analysis.FunctionalCalculus.Resolvent.ShiftPerturbation
import ComputationalMathematics.Source.CertifiedTridiagonalEigenpairs.RoundedVectorLocal.Assembly
import ComputationalMathematics.Source.CertifiedTridiagonalEigenpairs.Section06.ResolventScores
import Mathlib.Analysis.Normed.Algebra.Spectrum
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.MinMax

/-! # Relative accuracy and selection of rounded resolvent scores -/

open Matrix WithLp
open scoped Matrix.Norms.L2Operator
open NumStability.FloatingPointFormat.UnboundedBinary

namespace NumStability.CertifiedTridiagonalEigenpairs

private lemma norm_dotProduct_le_euclidean {n : ℕ} (x y : Fin n → ℂ) :
    ‖x ⬝ᵥ y‖ ≤ ‖toLp 2 x‖ * ‖toLp 2 y‖ := by
  have hx : ‖toLp 2 (star x)‖ = ‖toLp 2 x‖ := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1
    simp [EuclideanSpace.norm_sq_eq, Pi.star_apply]
  have h := norm_inner_le_norm (𝕜 := ℂ) (toLp 2 (star x)) (toLp 2 y)
  rw [EuclideanSpace.inner_eq_star_dotProduct, hx] at h
  simpa [dotProduct_comm] using h

private lemma imaginaryShift_diagonal_im_eq_column_norm_sq {n : ℕ}
    {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsHermitian) (shift : ℝ)
    {η : ℝ} (hη : 0 < η) (r : Fin n) :
    let G := (MatrixResolvent.imaginaryShift A shift η)⁻¹
    (G r r).im = η * ‖toLp 2 (G.col r)‖ ^ 2 := by
  intro G
  have h := congrArg (fun M : Matrix (Fin n) (Fin n) ℂ => (M r r).re)
    (MatrixResolvent.imaginaryPart_inv_imaginaryShift hA shift hη)
  change ((2 * Complex.I : ℂ)⁻¹ * (G r r - star (G r r))).re =
    ((η : ℂ) * (Gᴴ * G) r r).re at h
  have hinner : (Gᴴ * G) r r =
      inner ℂ (toLp 2 (G.col r)) (toLp 2 (G.col r)) := by
    rw [EuclideanSpace.inner_eq_star_dotProduct, Matrix.mul_apply, dotProduct]
    apply Finset.sum_congr rfl
    intro i _
    exact mul_comm _ _
  rw [hinner, inner_self_eq_norm_sq_to_K] at h
  norm_num [Complex.mul_re, Complex.sub_re, Complex.sub_im, Complex.star_def,
    Complex.inv_re, Complex.inv_im, Complex.normSq_apply, Complex.mul_im,
    ← Complex.ofReal_pow, Complex.ofReal_re, Complex.ofReal_im] at h
  linarith

set_option maxHeartbeats 1000000 in
/-- The diagonal perturbation estimate of Section 6, including the dependence on the norm
of the candidate-specific perturbation and its uniform relative bound. -/
theorem exactResolventRelativeDiagonalError {n : ℕ} {A E : Matrix (Fin n) (Fin n) ℂ}
    (hA : A.IsHermitian) (hAs : A.IsSymm) (r : Fin n) {shift η : ℝ}
    (hη : 0 < η) (hE : ‖E‖ ≤ η / 64) :
    let K := MatrixResolvent.imaginaryShift A shift η
    let G := K⁻¹
    let H := (K + E)⁻¹
    let δ := ‖E‖
    ‖H r r - G r r‖ ≤ δ / (1 - δ / η) * ‖toLp 2 (G.col r)‖ ^ 2 ∧
      δ / (1 - δ / η) * ‖toLp 2 (G.col r)‖ ^ 2 =
        (δ / η) / (1 - δ / η) * (G r r).im ∧
      (δ / η) / (1 - δ / η) * (G r r).im ≤ (G r r).im / 63 := by
  intro K G H δ
  have hδ₀ : 0 ≤ δ := norm_nonneg E
  have hsmall : δ < η := by dsimp only [δ]; linarith
  have hηδ : 0 < η - δ := sub_pos.mpr hsmall
  have hs : G.IsSymm := MatrixResolvent.isSymm_inv_imaginaryShift hAs shift η
  obtain ⟨_, hH, hLeft, hRight⟩ := MatrixResolvent.imaginaryShift_perturbation hA hη hsmall
  change ‖H‖ ≤ (η - δ)⁻¹ at hH
  change H - G = -(H * E * G) at hLeft
  change H = G - G * E * H at hRight
  let g := toLp 2 (G.col r)
  let w := toLp 2 (H.col r)
  have hcol : w - g = -toLp 2 ((H * E) *ᵥ G.col r) := by
    rw [← WithLp.toLp_sub, ← WithLp.toLp_neg]
    exact congrArg (fun M => toLp 2 (M.col r)) hLeft
  have hwnorm : ‖w‖ ≤ (1 + (η - δ)⁻¹ * δ) * ‖g‖ := by
    calc
      ‖w‖ = ‖(w - g) + g‖ := by rw [sub_add_cancel]
      _ ≤ ‖w - g‖ + ‖g‖ := norm_add_le _ _
      _ = ‖toLp 2 ((H * E) *ᵥ G.col r)‖ + ‖g‖ := by rw [hcol, norm_neg]
      _ ≤ ‖H * E‖ * ‖g‖ + ‖g‖ :=
        add_le_add_left (Matrix.l2_opNorm_mulVec (H * E) g) _
      _ ≤ ((η - δ)⁻¹ * δ) * ‖g‖ + ‖g‖ := by
        exact add_le_add_left (mul_le_mul_of_nonneg_right
          ((Matrix.l2_opNorm_mul H E).trans (mul_le_mul_of_nonneg_right hH hδ₀))
          (norm_nonneg g)) _
      _ = _ := by ring
  have hrow : G.row r = G.col r := funext fun i => (hs.apply r i).symm
  have hdiff : H r r - G r r = -((G * (E * H)) r r) := by
    have h := congrArg (fun M : Matrix (Fin n) (Fin n) ℂ => M r r) hRight
    change H r r = G r r - (G * E * H) r r at h
    rw [Matrix.mul_assoc] at h
    rw [h]
    ring
  have hden : 0 < 1 - δ / η := sub_pos.mpr ((div_lt_one hη).2 hsmall)
  have hcoeff : δ * (1 + (η - δ)⁻¹ * δ) = δ / (1 - δ / η) := by
    have heq : 1 - δ / η = (η - δ) / η := by rw [sub_div, div_self hη.ne']
    rw [heq]
    field_simp
    ring
  have him : (G r r).im = η * ‖g‖ ^ 2 :=
    imaginaryShift_diagonal_im_eq_column_norm_sq hA shift hη r
  refine ⟨?_, ?_, ?_⟩
  · rw [hdiff, norm_neg]
    change ‖G.row r ⬝ᵥ (E *ᵥ H.col r)‖ ≤ _
    rw [hrow]
    calc
      _ ≤ ‖g‖ * ‖toLp 2 (E *ᵥ H.col r)‖ := norm_dotProduct_le_euclidean _ _
      _ ≤ ‖g‖ * (δ * ‖w‖) :=
        mul_le_mul_of_nonneg_left (Matrix.l2_opNorm_mulVec E w) (norm_nonneg _)
      _ ≤ ‖g‖ * (δ * ((1 + (η - δ)⁻¹ * δ) * ‖g‖)) := by gcongr
      _ = _ := by rw [← hcoeff]; dsimp only [g]; ring
  · rw [him]
    change δ / (1 - δ / η) * ‖g‖ ^ 2 =
      (δ / η) / (1 - δ / η) * (η * ‖g‖ ^ 2)
    field_simp
  · have hfrac : (δ / η) / (1 - δ / η) ≤ (63 : ℝ)⁻¹ := by
      rw [inv_eq_one_div, div_le_div_iff₀ hden (by norm_num)]
      have h64 : δ / η ≤ 1 / 64 := (div_le_iff₀ hη).2 (by
        change ‖E‖ ≤ _
        linarith)
      linarith
    have hI : 0 ≤ (G r r).im := by rw [him]; positivity
    rw [div_eq_inv_mul (G r r).im]
    exact mul_le_mul_of_nonneg_right hfrac hI

/-- The exact positive imaginary score of a complex twist with stored components. -/
theorem vectorComplexPivot_inv_im (x y : ℝ) :
    ((vectorComplexPivot (x, y))⁻¹).im = y / (x ^ 2 + y ^ 2) := by
  simp [vectorComplexPivot, Complex.inv_im, Complex.normSq_apply, pow_two]

/-- The source's positive denominator and final rounding give relative error at most
five working unit roundoffs. -/
theorem vectorScore_relative_error (q : ℕ) (hq : 2 ≤ q)
    (hω : unitRoundoff q ≤ 1 / 128) (x y : ℝ) (hy : 0 < y) :
    let I := ((vectorComplexPivot (x, y))⁻¹).im
    0 < I ∧ 0 < vectorSquaredModulus q hq x y ∧
      |vectorScore q hq (x, y) - I| ≤ 5 * unitRoundoff q * I := by
  intro I
  let ω := unitRoundoff q
  let S := x ^ 2 + y ^ 2
  let D := vectorSquaredModulus q hq x y
  have hS : 0 < S := by dsimp only [S]; positivity
  have hD : 0 < D := vectorSquaredModulus_pos q hq x y hy
  have hI : I = y / S := vectorComplexPivot_inv_im x y
  have hI₀ : 0 < I := hI ▸ div_pos hy hS
  refine ⟨hI₀, hD, ?_⟩
  obtain ⟨ε, hε, hround⟩ := roundToEven_signedRelErrorWitness q hq (y / D)
  obtain ⟨hDlo, hDhi⟩ := vectorSquaredModulus_bounds q hq x y
  change (1 - ω)^2 * S ≤ D at hDlo
  change D ≤ (1 + ω)^2 * S at hDhi
  have hω₀ := (unitRoundoff_pos q).le
  have hω₂ : ω^2 ≤ ω / 128 := by
    nlinarith [mul_nonneg hω₀ (sub_nonneg.mpr hω)]
  have hω₃ : ω^3 ≤ ω / 128^2 := by
    nlinarith [mul_nonneg hω₀ (sub_nonneg.mpr hω₂)]
  have hlo : 0 ≤ 1 - 5 * ω := by linarith
  have hhi : 0 ≤ 1 + 5 * ω := by linarith
  have hL : (1 - 5 * ω) * (1 + ω)^2 ≤ 1 + ε := by
    nlinarith [(abs_le.mp hε).1, sq_nonneg ω, mul_nonneg hω₀ (sq_nonneg ω)]
  have hU : 1 + ε ≤ (1 + 5 * ω) * (1 - ω)^2 := by
    nlinarith [(abs_le.mp hε).2, sq_nonneg ω, mul_nonneg hω₀ (sq_nonneg ω)]
  change |roundToEven q hq (y / D) - I| ≤ 5 * ω * I
  rw [hround, hI, abs_le]
  have hylower : (1 - 5 * ω) * D ≤ (1 + ε) * S := calc
    _ ≤ (1 - 5 * ω) * ((1 + ω)^2 * S) := mul_le_mul_of_nonneg_left hDhi hlo
    _ = ((1 - 5 * ω) * (1 + ω)^2) * S := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hL hS.le
  have hyupper : (1 + ε) * S ≤ (1 + 5 * ω) * D := calc
    _ ≤ ((1 + 5 * ω) * (1 - ω)^2) * S := mul_le_mul_of_nonneg_right hU hS.le
    _ = (1 + 5 * ω) * ((1 - ω)^2 * S) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hDlo hhi
  constructor
  · have h : (1 - 5 * ω) * (y / S) ≤ y / D * (1 + ε) := by
      rw [← mul_div_assoc, mul_comm (y / D), ← mul_div_assoc, div_le_div_iff₀ hS hD]
      nlinarith [mul_le_mul_of_nonneg_right hylower hy.le]
    linarith
  · have h : y / D * (1 + ε) ≤ (1 + 5 * ω) * (y / S) := by
      rw [mul_comm (y / D), ← mul_div_assoc, ← mul_div_assoc, div_le_div_iff₀ hD hS]
      nlinarith [mul_le_mul_of_nonneg_right hyupper hy.le]
    linarith

/-- Store the scores in index order and scan the stored pairs for the first maximizer. -/
noncomputable def vectorScoreMaximizer (n : ℕ) (hn : 0 < n) (s : Fin n → ℝ) : Fin n :=
  (((List.finRange n).map (fun i => (i, s i))).argmax Prod.snd).get
      (by
        rw [Option.isSome_iff_ne_none]
        exact fun h => hn.ne' (by simpa using congrArg List.length (List.argmax_eq_none.mp h)))
    |>.1

/-- The scan selects the least index whose stored score is maximal. -/
theorem vectorScoreMaximizer_spec (n : ℕ) (hn : 0 < n) (s : Fin n → ℝ) :
    let r := vectorScoreMaximizer n hn s
    (∀ i, s i ≤ s r) ∧ (∀ i, s i = s r → r ≤ i) := by
  intro r
  let candidates := (List.finRange n).map (fun i => (i, s i))
  let p := (candidates.argmax Prod.snd).get (by
    rw [Option.isSome_iff_ne_none]
    exact fun h => hn.ne' (by simpa [candidates] using congrArg List.length (List.argmax_eq_none.mp h)))
  have hp : p ∈ candidates.argmax Prod.snd := (Option.some_get _).symm
  have hr : p.1 = r := rfl
  obtain ⟨i, _, hi⟩ := List.mem_map.mp (List.argmax_mem hp)
  have hp' : (r, s r) ∈ candidates.argmax Prod.snd := by
    have hir : i = r := (congrArg Prod.fst hi).trans hr
    rw [hir] at hi
    exact hi ▸ hp
  have hmem (j : Fin n) : (j, s j) ∈ candidates :=
    List.mem_map.mpr ⟨j, List.mem_finRange j, rfl⟩
  have hidx (j : Fin n) :
      @List.idxOf _ instBEqOfDecidableEq (j, s j) candidates = j.val := by
    have hn : candidates.Nodup :=
      (List.nodup_finRange n).map (fun _ _ h => congrArg Prod.fst h)
    have hj : j.val < candidates.length := by simp [candidates]
    simpa [candidates] using
      (@List.Nodup.idxOf_getElem _ instBEqOfDecidableEq (by infer_instance) _ hn j.val hj)
  constructor
  · intro j
    exact List.le_of_mem_argmax (f := Prod.snd) (hmem j) hp'
  · intro j hj
    have h := List.index_of_argmax hp' (hmem j) hj.ge
    rwa [hidx, hidx] at h

/-- Select by the scores of the actual rounded twists of the two sweeps. -/
noncomputable def vectorSelectedIndex (q : ℕ) (hq : 2 ≤ q) (n : ℕ) (hn : 0 < n)
    (a b : ℕ → ℝ) (η : ℝ) : Fin n :=
  vectorScoreMaximizer n hn (fun r => vectorScore q hq (vectorSweepTwist q hq n a b η r))

/-- The selected index attains the greatest rounded score and is the least in a tie. -/
theorem vectorSelectedIndex_spec (q : ℕ) (hq : 2 ≤ q) (n : ℕ) (hn : 0 < n)
    (a b : ℕ → ℝ) (η : ℝ) :
    let s := fun r => vectorScore q hq (vectorSweepTwist q hq n a b η r)
    let r := vectorSelectedIndex q hq n hn a b η
    (∀ i, s i ≤ s r) ∧ (∀ i, s i = s r → r ≤ i) :=
  vectorScoreMaximizer_spec n hn _

private theorem vectorScore_bounds_of_backward
    {I J s ω : ℝ} (hω₀ : 0 ≤ ω) (hω : ω ≤ 1 / 128)
    (hJ : |J - I| ≤ I / 63) (hs : |s - J| ≤ 5 * ω * J) :
    (1 - 5 * ω) * (62 / 63) * I ≤ s ∧
      s ≤ (1 + 5 * ω) * (64 / 63) * I := by
  have hJlo : (62 / 63) * I ≤ J := by linarith [(abs_le.mp hJ).1]
  have hJhi : J ≤ (64 / 63) * I := by linarith [(abs_le.mp hJ).2]
  have hslo : (1 - 5 * ω) * J ≤ s := by linarith [(abs_le.mp hs).1]
  have hshi : s ≤ (1 + 5 * ω) * J := by linarith [(abs_le.mp hs).2]
  rw [mul_assoc, mul_assoc]
  exact ⟨(mul_le_mul_of_nonneg_left hJlo (by linarith)).trans hslo,
    hshi.trans (mul_le_mul_of_nonneg_left hJhi (by linarith))⟩

private theorem vectorScore_ratio_gt_half {ω : ℝ} (hω₀ : 0 ≤ ω) (hω : 5 * ω ≤ 1 / 128) :
    (1 / 2 : ℝ) < ((1 - 5 * ω) / (1 + 5 * ω)) * (62 / 64) := by
  rw [mul_comm _ (62 / 64 : ℝ), ← mul_div_assoc, lt_div_iff₀ (by linarith)]
  linarith

/-- The score for a single candidate and the backward error of its stored twist. -/
def RoundedVectorScoreAccuracy {n : ℕ} (q : ℕ) (hq : 2 ≤ q) (η : ℝ)
    (K E : Matrix (Fin n) (Fin n) ℂ) (i : Fin n) (twist : ℝ × ℝ) : Prop :=
  let ω := unitRoundoff q
  let G := K⁻¹
  let H := (K + E)⁻¹
  let δ := ‖E‖
  let I := (G i i).im
  let s := vectorScore q hq twist
  Eᵀ = E ∧
    (∀ j k : Fin n, j.val + 1 < k.val ∨ k.val + 1 < j.val → E j k = 0) ∧
    IsUnit (K + E) ∧ δ ≤ 40 * ω ∧ 40 * ω ≤ η / 64 ∧
    ‖H i i - G i i‖ ≤ δ / (1 - δ / η) * ‖toLp 2 (G.col i)‖ ^ 2 ∧
    δ / (1 - δ / η) * ‖toLp 2 (G.col i)‖ ^ 2 = (δ / η) / (1 - δ / η) * I ∧
    (δ / η) / (1 - δ / η) * I ≤ I / 63 ∧
    (H i i).im = ((vectorComplexPivot twist)⁻¹).im ∧
    (H i i).im = twist.2 / (twist.1 ^ 2 + twist.2 ^ 2) ∧
    0 < (H i i).im ∧ 0 < vectorSquaredModulus q hq twist.1 twist.2 ∧
    |s - (H i i).im| ≤ 5 * ω * (H i i).im ∧
    (1 - 5 * ω) * (62 / 63) * I ≤ s ∧ s ≤ (1 + 5 * ω) * (64 / 63) * I

set_option maxHeartbeats 1400000 in
/-- Relative score accuracy and the actual least-maximizer selection (equations (70)–(72)).
The diagonal data are shifted in exact arithmetic before the directional sweeps
perform their first rounding. A single real matrix determines all exact scores. -/
theorem roundedVectorScoreSelection {n : ℕ} (hn : 2 ≤ n) (q : ℕ) (hq : 2 ≤ q)
    (a b : ℕ → ℝ) (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsSymm)
    {shift target η : ℝ} (hη : 0 < η) (hηmax : η ≤ 1 / 2) (hηNative : Native q hq η)
    (hω : unitRoundoff q ≤ η / 4096)
    (ha : ∀ i < n, |a i| ≤ 5) (hb : ∀ i, i + 1 < n → |b i| ≤ 1)
    (hK : vectorShiftedMatrix n a b η = MatrixResolvent.imaginaryShift (A.map Complex.ofReal) shift η)
    (htarget : target ∈ spectrum ℝ A) (hnear : |shift - target| ≤ η) :
    let ω := unitRoundoff q
    let K := MatrixResolvent.imaginaryShift (A.map Complex.ofReal) shift η
    let G := K⁻¹
    let I := fun r => (G r r).im
    let twist := vectorSweepTwist q hq n a b η
    let s := fun r => vectorScore q hq (twist r)
    let r := vectorSelectedIndex q hq n (by omega) a b η
    (∀ i, ∃ E, RoundedVectorScoreAccuracy q hq η K E i (twist i)) ∧
    (∀ i, s i ≤ s r) ∧ (∀ i, s i = s r → r ≤ i) ∧
    (∀ i, ((1 - 5 * ω) / (1 + 5 * ω)) * (62 / 64) * I i ≤ I r) ∧
    (∀ rStar, (∀ i, I i ≤ I rStar) →
      (4 * (n : ℝ) * η)⁻¹ ≤ ((1 - 5 * ω) / (1 + 5 * ω)) * (62 / 64) * I rStar) ∧
    (4 * (n : ℝ) * η)⁻¹ ≤ I r := by
  intro ω K G I twist s r
  have hω₀ : 0 ≤ ω := (unitRoundoff_pos q).le
  have hωsmall : ω ≤ 1 / 128 := by change unitRoundoff q ≤ _; linarith
  have hωfive : 5 * ω ≤ 1 / 128 := by change 5 * unitRoundoff q ≤ _; linarith
  have hωη : 40 * ω ≤ η / 64 := by change 40 * unitRoundoff q ≤ _; linarith
  have hAs : (A.map Complex.ofReal).IsSymm := by
    ext i j
    exact congrArg Complex.ofReal (hA.apply i j)
  have hAc := MatrixResolvent.isHermitian_map_ofReal hA
  have hlocal := (roundedVectorStructuredBackward n q hn hq a b η
    hωsmall hη hηmax hηNative ha hb).2
  have hentry (i : Fin n) : ∃ E, RoundedVectorScoreAccuracy q hq η K E i (twist i) := by
    obtain ⟨hy, _, E, β, hEs, hband, _, hunit, hinv, hE, _, _⟩ := hlocal i
    change IsUnit (vectorShiftedMatrix n a b η + E) at hunit
    change ((vectorShiftedMatrix n a b η + E)⁻¹) i i = (vectorComplexPivot (twist i))⁻¹ at hinv
    rw [hK] at hunit hinv
    let H := (K + E)⁻¹
    have him : (H i i).im = ((vectorComplexPivot (twist i))⁻¹).im := congrArg Complex.im hinv
    have hy₀ : 0 < (twist i).2 := hη.trans_le hy
    obtain ⟨hrel, heq, hunif⟩ := exactResolventRelativeDiagonalError hAc hAs i
      (shift := shift) hη (hE.trans hωη)
    obtain ⟨hpositive, hD, hround⟩ := vectorScore_relative_error q hq hωsmall
      (twist i).1 (twist i).2 hy₀
    change 0 < ((vectorComplexPivot (twist i))⁻¹).im at hpositive
    change |s i - ((vectorComplexPivot (twist i))⁻¹).im| ≤
      5 * ω * ((vectorComplexPivot (twist i))⁻¹).im at hround
    rw [← him] at hpositive hround
    have himle : |(H i i).im - I i| ≤ I i / 63 := by
      have h := Complex.abs_im_le_norm (H i i - G i i)
      rw [Complex.sub_im] at h
      exact h.trans (hrel.trans (heq.le.trans hunif))
    obtain ⟨hslo, hshi⟩ := vectorScore_bounds_of_backward hω₀ hωsmall himle hround
    refine ⟨E, hEs, hband, hunit, hE, hωη, hrel, heq, hunif, him, ?_,
      hpositive, hD, hround, hslo, hshi⟩
    exact him.trans (vectorComplexPivot_inv_im (twist i).1 (twist i).2)
  obtain ⟨hmax, hleast⟩ := vectorSelectedIndex_spec q hq n (by omega) a b η
  have hratio (i : Fin n) : ((1 - 5 * ω) / (1 + 5 * ω)) * (62 / 64) * I i ≤ I r := by
    obtain ⟨E, _, _, _, _, _, _, _, _, _, _, _, _, _, hi, _⟩ := hentry i
    obtain ⟨F, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hr⟩ := hentry r
    have hs := hi.trans ((hmax i).trans hr)
    have hD : 0 < (1 + 5 * ω) * (64 / 63) := by positivity
    have h := (div_le_iff₀ hD).2
      (show (1 - 5 * ω) * (62 / 63) * I i ≤ I r * ((1 + 5 * ω) * (64 / 63)) from
        by rw [mul_comm (I r)]; exact hs)
    convert h using 1
    field_simp
  have hn₀ : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  obtain ⟨i, hi⟩ := (exactResolventScores hA hη htarget hnear).2.2.2
  have hhalf := vectorScore_ratio_gt_half hω₀ hωfive
  have hlower {J : ℝ} (hJ : (2 * (n : ℝ) * η)⁻¹ ≤ J) :
      (4 * (n : ℝ) * η)⁻¹ ≤ ((1 - 5 * ω) / (1 + 5 * ω)) * (62 / 64) * J := by
    have hJ₀ : 0 ≤ J := (by positivity : 0 ≤ (2 * (n : ℝ) * η)⁻¹).trans hJ
    calc
      _ = (1 / 2) * (2 * (n : ℝ) * η)⁻¹ := by field_simp; ring
      _ ≤ (1 / 2) * J := mul_le_mul_of_nonneg_left hJ (by norm_num)
      _ ≤ _ := mul_le_mul_of_nonneg_right hhalf.le hJ₀
  exact ⟨hentry, hmax, hleast, hratio, fun rStar h => hlower (hi.trans (h i)),
    (hlower hi).trans (hratio i)⟩


/-- The diagonal input to the sweeps, before the working-precision subtraction is rounded. -/
noncomputable def vectorInputDiagonal {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (shift : ℝ) (i : ℕ) : ℝ :=
  if hi : i < n then A ⟨i, hi⟩ ⟨i, hi⟩ - shift else 0

/-- The stored consecutive upper diagonal of the real tridiagonal input. -/
noncomputable def vectorInputEdge {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (i : ℕ) : ℝ :=
  if hi : i + 1 < n then A ⟨i, by omega⟩ ⟨i + 1, hi⟩ else 0

/-- The matrix described by the sweep input is the shifted real input. -/
theorem vectorShiftedMatrix_eq_imaginaryShift {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.IsSymm)
    (hband : ∀ i j : Fin n, i.val + 1 < j.val ∨ j.val + 1 < i.val → A i j = 0)
    (shift η : ℝ) :
    vectorShiftedMatrix n (vectorInputDiagonal A shift) (vectorInputEdge A) η =
      MatrixResolvent.imaginaryShift (A.map Complex.ofReal) shift η := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp only [vectorShiftedMatrix, vectorInputDiagonal, dif_pos i.isLt,
      Fin.eta, MatrixResolvent.imaginaryShift, Matrix.sub_apply, Matrix.map_apply,
      Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one]
    apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im]
  · simp only [vectorShiftedMatrix, if_neg hij, MatrixResolvent.imaginaryShift,
      Matrix.sub_apply, Matrix.map_apply, Matrix.smul_apply, Matrix.one_apply_ne hij,
      smul_eq_mul, mul_zero, sub_zero]
    by_cases hupper : i.val + 1 = j.val
    · simp [hupper, vectorInputEdge]
    · by_cases hlower : j.val + 1 = i.val
      · have hj : j.val + 1 < n := hlower ▸ i.isLt
        have h : (⟨j.val + 1, hj⟩ : Fin n) = i := Fin.ext hlower
        simpa [hupper, hlower, vectorInputEdge, hj, h] using congrArg Complex.ofReal (hA.apply i j)
      · have hv : i.val ≠ j.val := fun h => hij (Fin.ext h)
        have hz := hband i j (by omega)
        simp [hupper, hlower, hz]

private theorem abs_matrix_apply_le_l2OpNorm {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (i j : Fin n) : |A i j| ≤ ‖A‖ := by
  let e := EuclideanSpace.single j (1 : ℝ)
  have hcol : A *ᵥ e.ofLp = A.col j := by
    change A *ᵥ Pi.single j 1 = _
    exact Matrix.mulVec_single_one A j
  have hmul : ‖toLp 2 (A.col j)‖ ≤ ‖A‖ := by
    have h := Matrix.l2_opNorm_mulVec A e
    change ‖toLp 2 (A *ᵥ e.ofLp)‖ ≤ ‖A‖ * ‖e‖ at h
    simpa [hcol, e, EuclideanSpace.norm_single] using h
  exact (show |A i j| ≤ ‖toLp 2 (A.col j)‖ from
    by simpa [Real.norm_eq_abs] using PiLp.norm_apply_le (toLp 2 (A.col j)) i).trans hmul

/-- The paper's matrix and shift hypotheses bound the real input data for both sweeps. -/
theorem vectorSweepInputBounds {n : ℕ} (hn : 2 ≤ n)
    (A : Matrix (Fin n) (Fin n) ℝ) (hAnorm : ‖A‖ ≤ 2)
    (hb : ∀ i j : Fin n, i.val + 1 = j.val → |A i j| ≤ 1)
    {shift target η : ℝ} (hηmax : η ≤ 1 / 2)
    (htarget : target ∈ spectrum ℝ A) (hnear : |shift - target| ≤ η) :
    (∀ i < n, |vectorInputDiagonal A shift i| ≤ 5) ∧
      (∀ i, i + 1 < n → |vectorInputEdge A i| ≤ 1) := by
  letI : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  letI : NormOneClass (Matrix (Fin n) (Fin n) ℝ) := ⟨by
    rw [← Matrix.diagonal_one, Matrix.l2_opNorm_diagonal]
    exact norm_one⟩
  have ht : |target| ≤ 2 := by
    rw [← Real.norm_eq_abs]
    exact (spectrum.norm_le_norm_of_mem htarget).trans hAnorm
  have hs : |shift| ≤ 5 / 2 := by
    have h := abs_add_le (shift - target) target
    rw [sub_add_cancel] at h
    linarith
  have ha (i : ℕ) (hi : i < n) : |vectorInputDiagonal A shift i| ≤ 5 := by
    rw [vectorInputDiagonal, dif_pos hi]
    have hii := (abs_matrix_apply_le_l2OpNorm A ⟨i, hi⟩ ⟨i, hi⟩).trans hAnorm
    have h := abs_sub (A ⟨i, hi⟩ ⟨i, hi⟩) shift
    linarith
  have hbe (i : ℕ) (hi : i + 1 < n) : |vectorInputEdge A i| ≤ 1 := by
    rw [vectorInputEdge, dif_pos hi]
    exact hb ⟨i, by omega⟩ ⟨i + 1, hi⟩ rfl
  exact ⟨ha, hbe⟩

set_option maxHeartbeats 1000000 in
/-- Score selection directly from the tridiagonal matrix and supplied shift.
The norm and proximity assumptions supply the local diagonal bound for the actual sweeps. -/
theorem roundedTridiagonalVectorScoreSelection {n : ℕ} (hn : 2 ≤ n) (q : ℕ) (hq : 2 ≤ q)
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsSymm) (hAnorm : ‖A‖ ≤ 2)
    (hband : ∀ i j : Fin n, i.val + 1 < j.val ∨ j.val + 1 < i.val → A i j = 0)
    (hb : ∀ i j : Fin n, i.val + 1 = j.val → |A i j| ≤ 1)
    {shift target η : ℝ} (hη : 0 < η) (hηmax : η ≤ 1 / 2)
    (hηpow : ∃ m : ℤ, η = (2 : ℝ) ^ m) (hω : unitRoundoff q ≤ η / 4096)
    (htarget : target ∈ spectrum ℝ A) (hnear : |shift - target| ≤ η) :
    let ω := unitRoundoff q
    let a := vectorInputDiagonal A shift
    let b := vectorInputEdge A
    let K := MatrixResolvent.imaginaryShift (A.map Complex.ofReal) shift η
    let I := fun r => (K⁻¹ r r).im
    let twist := vectorSweepTwist q hq n a b η
    let s := fun r => vectorScore q hq (twist r)
    let r := vectorSelectedIndex q hq n (by omega) a b η
    (∀ i, ∃ E, RoundedVectorScoreAccuracy q hq η K E i (twist i)) ∧
    (∀ i, s i ≤ s r) ∧ (∀ i, s i = s r → r ≤ i) ∧
    (∀ i, ((1 - 5 * ω) / (1 + 5 * ω)) * (62 / 64) * I i ≤ I r) ∧
    (∀ rStar, (∀ i, I i ≤ I rStar) →
      (4 * (n : ℝ) * η)⁻¹ ≤ ((1 - 5 * ω) / (1 + 5 * ω)) * (62 / 64) * I rStar) ∧
    (4 * (n : ℝ) * η)⁻¹ ≤ I r := by
  obtain ⟨m, hm⟩ := hηpow
  have hηNative : Native q hq η := hm ▸ native_zpow q hq m
  obtain ⟨ha, hbe⟩ := vectorSweepInputBounds hn A hAnorm hb hηmax htarget hnear
  exact roundedVectorScoreSelection hn q hq _ _ A hA hη hηmax hηNative hω ha hbe
    (vectorShiftedMatrix_eq_imaginaryShift A hA hband shift η) htarget hnear

end NumStability.CertifiedTridiagonalEigenpairs
