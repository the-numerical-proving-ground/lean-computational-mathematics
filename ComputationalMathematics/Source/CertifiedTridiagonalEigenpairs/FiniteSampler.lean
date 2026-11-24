import ComputationalMathematics.Algorithms.Arithmetic.ScalarWork
import ComputationalMathematics.Analysis.FloatingPointArithmetic.UnboundedBinary.IntegerWords
import ComputationalMathematics.Source.CertifiedTridiagonalEigenpairs.Parameters
import Mathlib.Data.Matrix.Basic
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Probability.Distributions.Uniform

/-!
# Finite fair-bit perturbations for selected tridiagonal eigenpairs

Equation `alg:sample` interprets each word of fair bits as a binary integer
and uses the center of the corresponding cell in the perturbation interval.
-/

namespace NumStability.CertifiedTridiagonalEigenpairs

open FloatingPointFormat.UnboundedBinary
open scoped ENNReal

/-- A word of exactly `b` bits in draw order, most significant bit first. -/
abbrev FairBitWord (b : ℕ) := Fin b → Bool

private def wordSnocEquiv (b : ℕ) : FairBitWord (b + 1) ≃ FairBitWord b × Bool where
  toFun word := (Fin.init word, word (Fin.last b))
  invFun pair := Fin.snoc pair.1 pair.2
  left_inv := Fin.snoc_init_self
  right_inv := by
    rintro ⟨word, bit⟩
    exact Prod.ext (Fin.init_snoc (α := fun _ => Bool) bit word)
      (Fin.snoc_last (α := fun _ => Bool) bit word)

/-- Binary accumulation is a bijection from exact-length words to grid indices. -/
def bitWordEquiv : (b : ℕ) → FairBitWord b ≃ Fin (2 ^ b)
  | 0 =>
      { toFun := fun _ => 0
        invFun := fun _ i => Fin.elim0 i
        left_inv := fun _ => funext fun i => Fin.elim0 i
        right_inv := fun r => Fin.ext (by have h := r.isLt; simp only [pow_zero] at h; omega) }
  | b + 1 => (wordSnocEquiv b).trans <|
      ((bitWordEquiv b).prodCongr finTwoEquiv.symm).trans <|
        finProdFinEquiv.trans (finCongr (pow_succ 2 b).symm)

@[simp] theorem bitWordEquiv_zero (word : FairBitWord 0) :
    (bitWordEquiv 0 word).val = 0 := rfl

theorem bitWordEquiv_succ (b : ℕ) (word : FairBitWord (b + 1)) :
    (bitWordEquiv (b + 1) word).val =
      2 * (bitWordEquiv b (Fin.init word)).val + (word (Fin.last b)).toNat := by
  rw [bitWordEquiv]
  change (finCongr (pow_succ 2 b).symm
    (finProdFinEquiv (bitWordEquiv b (Fin.init word), finTwoEquiv.symm (word (Fin.last b))))).val = _
  rw [finCongr_apply, Fin.val_cast, finProdFinEquiv_apply_val]
  cases word (Fin.last b) <;> simp [finTwoEquiv, Bool.toNat, Nat.add_comm]

/-- The draws `r_i` obtained from all the bit words of a trial. -/
def trialDraws (n k : ℕ) :
    (Fin n → FairBitWord (rngBits n k)) ≃ (Fin n → Fin (2 ^ rngBits n k)) :=
  Equiv.piCongrRight fun _ => bitWordEquiv (rngBits n k)

noncomputable section

private theorem uniform_map_equiv {A B : Type*} [Fintype A] [Fintype B]
    [Nonempty A] [Nonempty B] (e : A ≃ B) :
    (PMF.uniformOfFintype A).map e = PMF.uniformOfFintype B := by
  classical
  ext y
  rw [PMF.map_apply]
  simp_rw [show ∀ x, y = e x ↔ x = e.symm y from
    fun x => ⟨fun h => by rw [h, e.symm_apply_apply], fun h => by rw [h, e.apply_symm_apply]⟩]
  rw [tsum_ite_eq, PMF.uniformOfFintype_apply, PMF.uniformOfFintype_apply, Fintype.card_congr e]

/-- The law of independent fair bits at all trial bit positions. -/
def trialBitLaw (n k : ℕ) : PMF (Fin n → FairBitWord (rngBits n k)) :=
  PMF.uniformOfFintype _

theorem trialBitLaw_apply (n k : ℕ) (words : Fin n → FairBitWord (rngBits n k)) :
    trialBitLaw n k words = ((2 : ℝ≥0∞) ^ (n * rngBits n k))⁻¹ := by
  rw [trialBitLaw, PMF.uniformOfFintype_apply, Fintype.card_fun, Fintype.card_fun]
  rw [Fintype.card_bool, Fintype.card_fin, Fintype.card_fin, Nat.cast_pow, Nat.cast_pow,
    Nat.cast_ofNat, ← pow_mul, Nat.mul_comm]

/-- The draw law is uniform on the product of the integer ranges. -/
theorem trialDraws_law (n k : ℕ) [NeZero (2 ^ rngBits n k)] :
    (trialBitLaw n k).map (trialDraws n k) = PMF.uniformOfFintype _ :=
  uniform_map_equiv (trialDraws n k)

/-- The joint mass factors into the same uniform mass for each coordinate. -/
theorem trialDraws_law_apply (n k : ℕ) (r : Fin n → Fin (2 ^ rngBits n k)) :
    ((trialBitLaw n k).map (trialDraws n k)) r =
      ((((2 : ℝ≥0∞) ^ rngBits n k)⁻¹) ^ n) := by
  letI : NeZero (2 ^ rngBits n k) := ⟨by positivity⟩
  rw [trialDraws_law, PMF.uniformOfFintype_apply, Fintype.card_fun]
  rw [Fintype.card_fin, Fintype.card_fin, Nat.cast_pow, Nat.cast_pow, Nat.cast_ofNat,
    ENNReal.inv_pow]

/-- Numerical accumulation by an exponent shift and nearest-even addition
for each bit. -/
def accumulate (q : ℕ) (hq : 2 ≤ q) : (b : ℕ) → FairBitWord b → ℝ
  | 0, _ => 0
  | b + 1, word => roundToEven q hq
      (2 * accumulate q hq b (Fin.init word) + (word (Fin.last b)).toNat)

/-- All prefixes accumulate exactly at precision `q`. -/
theorem accumulate_eq (q : ℕ) (hq : 2 ≤ q) (b : ℕ) (hb : b ≤ q)
    (word : FairBitWord b) :
    accumulate q hq b word = ((bitWordEquiv b word).val : ℝ) := by
  induction b with
  | zero => simp [accumulate]
  | succ b ih =>
      rw [accumulate, ih (by omega)]
      have h := roundToEven_natCast_of_lt_two_pow q hq
        ((bitWordEquiv (b + 1) word).isLt.trans_le (Nat.pow_le_pow_right (by decide) hb))
      rw [bitWordEquiv_succ] at h ⊢
      simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] using h

/-- Perturbation of a coordinate with decoded draw `r`. -/
def cellCenter (δ : ℝ) (b : ℕ) (r : Fin (2 ^ b)) : ℝ :=
  δ * (2 * (r.val : ℝ) + 1 - 2 ^ b) / 2 ^ b

/-- Radius of each cell, also the offset bound in the coupling proof. -/
def cellRadius (δ : ℝ) (b : ℕ) : ℝ := δ / 2 ^ b

theorem cellCenter_as_radius {δ : ℝ} {b : ℕ} (r : Fin (2 ^ b)) :
    cellCenter δ b r = (2 * (r.val : ℝ) + 1 - 2 ^ b) * cellRadius δ b := by
  unfold cellCenter cellRadius
  ring

theorem abs_cellCenter_lt {δ : ℝ} (hδ : 0 < δ) {b : ℕ} (r : Fin (2 ^ b)) :
    |cellCenter δ b r| < δ := by
  have hr₀ : 0 ≤ (r.val : ℝ) := by positivity
  have hr₁ : (r.val : ℝ) + 1 ≤ (2 : ℝ) ^ b := by exact_mod_cast r.isLt
  have hp : 0 < (2 : ℝ) ^ b := by positivity
  rw [cellCenter, abs_lt]
  constructor
  · apply (lt_div_iff₀ hp).2
    nlinarith [mul_nonneg hδ.le hr₀]
  · apply (div_lt_iff₀ hp).2
    nlinarith [mul_nonneg hδ.le (sub_nonneg.mpr hr₁)]

/-- The arithmetic after accumulation. Exponent shifts form the doubled
draw and the grid size. Two integer operations give the signed numerator.
A final exponent shift supplies both factors of the perturbation scale. -/
def formCenter (q : ℕ) (hq : 2 ≤ q) (p b : ℕ) (r : ℝ) : ℝ :=
  let odd := roundToEven q hq (2 * r + 1)
  let numerator := roundToEven q hq (odd - 2 ^ b)
  numerator * (2 : ℝ) ^ (-((p + 8 + b : ℕ) : ℤ))

theorem workingPrecision_ge_two (n k p : ℕ) : 2 ≤ workingPrecision n k p := by
  unfold workingPrecision
  omega

/-- The rounded center arithmetic agrees exactly with `alg:sample`. -/
theorem formCenter_eq (n k p : ℕ) (r : Fin (2 ^ rngBits n k)) :
    formCenter (workingPrecision n k p) (workingPrecision_ge_two n k p)
      p (rngBits n k) (r.val : ℝ) = cellCenter (perturbationScale p) (rngBits n k) r := by
  have hpow : 2 ^ (rngBits n k + 1) ≤ (2 : ℕ) ^ workingPrecision n k p :=
    Nat.pow_le_pow_right (by decide) (rngBits_add_one_lt_workingPrecision n k p).le
  obtain ⟨_, hodd, hnum⟩ := samplerIntegers_lt_two_pow (n := n) (k := k) r.isLt
  have rodd := roundToEven_natCast_of_lt_two_pow _ (workingPrecision_ge_two n k p)
    (hodd.trans_le hpow)
  have rnum := roundToEven_intCast_of_natAbs_lt_two_pow _ (workingPrecision_ge_two n k p)
    (hnum.trans_le hpow)
  push_cast at rodd rnum
  simp only [formCenter, rodd, rnum, cellCenter, perturbationScale_eq_roundoff,
    unitRoundoff, zpow_neg, zpow_natCast, pow_add, mul_inv, div_eq_mul_inv]
  ring

/-- The trial rounds each perturbed diagonal once and copies the other
entries from the fixed normalized matrix. -/
def sampledMatrix (n k p : ℕ) (S : Matrix (Fin n) (Fin n) ℝ)
    (words : Fin n → FairBitWord (rngBits n k)) : Matrix (Fin n) (Fin n) ℝ :=
  let q := workingPrecision n k p
  let hq := workingPrecision_ge_two n k p
  let b := rngBits n k
  Matrix.of fun i j =>
    if i = j then
      roundToEven q hq (S i i + formCenter q hq p b (accumulate q hq b (words i)))
    else S i j

theorem sampledMatrix_diag (n k p : ℕ) (S : Matrix (Fin n) (Fin n) ℝ)
    (words : Fin n → FairBitWord (rngBits n k)) (i : Fin n) :
    sampledMatrix n k p S words i i =
      roundToEven (workingPrecision n k p) (workingPrecision_ge_two n k p)
        (S i i + cellCenter (perturbationScale p) (rngBits n k) (trialDraws n k words i)) := by
  have hb : rngBits n k ≤ workingPrecision n k p :=
    Nat.le_of_lt (Nat.lt_of_succ_lt (rngBits_add_one_lt_workingPrecision n k p))
  simp only [sampledMatrix, Matrix.of_apply, accumulate_eq _ _ _ hb]
  exact congrArg (fun x => roundToEven (workingPrecision n k p)
    (workingPrecision_ge_two n k p) (S i i + x))
    (formCenter_eq n k p (trialDraws n k words i))

theorem sampledMatrix_offDiag (n k p : ℕ) (S : Matrix (Fin n) (Fin n) ℝ)
    (words : Fin n → FairBitWord (rngBits n k)) {i j : Fin n} (h : i ≠ j) :
    sampledMatrix n k p S words i j = S i j := by
  simp [sampledMatrix, h]

theorem trialCellRadius_eq (n k p : ℕ) :
    cellRadius (perturbationScale p) (rngBits n k) = gapLabelError n k p :=
  perturbationScale_div_rng n k p

/-- Diagonal storage incurs only the rounding of the sum in `alg:sample`. -/
theorem sampledMatrix_diag_roundoff {n k p : ℕ} (hn : 2 ≤ n)
    (guard : precisionGuard n p) (S : Matrix (Fin n) (Fin n) ℝ)
    (words : Fin n → FairBitWord (rngBits n k)) (i : Fin n) (hS : |S i i| ≤ 1 / 4) :
    |sampledMatrix n k p S words i i -
      (S i i + cellCenter (perturbationScale p) (rngBits n k) (trialDraws n k words i))| ≤
        2 * workingRoundoff n k p := by
  have hp : 2 ≤ p := by
    have := clog_add_le_of_precisionGuard (by omega : 0 < n) guard
    omega
  have hδ : 0 < perturbationScale p := div_pos (unitRoundoff_pos p) (by norm_num)
  have hδle : perturbationScale p ≤ 1 / 1024 := by
    unfold perturbationScale
    linarith [unitRoundoff_le_quarter p hp]
  have hcenter :=
    abs_cellCenter_lt hδ (trialDraws n k words i)
  rw [sampledMatrix_diag]
  calc
    _ ≤ workingRoundoff n k p * 2 := by
      apply abs_roundToEven_sub_le_of_abs_le
      linarith [abs_add_le (S i i)
        (cellCenter (perturbationScale p) (rngBits n k) (trialDraws n k words i))]
    _ = _ := mul_comm _ _

end

private def accumulateStep (q : ℕ) : List ScalarWork.Step :=
  [.index, .fairBit, .scaleByPowerOfTwo, .arithmetic q]

private def storeDiagonalSteps (q : ℕ) : List ScalarWork.Step :=
  [.index, .scaleByPowerOfTwo, .arithmetic q, .scaleByPowerOfTwo, .arithmetic q,
    .scaleByPowerOfTwo, .arithmetic q]

private def diagonalTrace (q b : ℕ) : List ScalarWork.Step :=
  (List.replicate b (accumulateStep q)).flatten ++ storeDiagonalSteps q

/-- The trace for constructing and storing the sampled diagonal. The
off-diagonal data of the tridiagonal matrix are carried forward from `S`. -/
def samplerTrace (n k p : ℕ) : List ScalarWork.Step :=
  (List.replicate n (diagonalTrace (workingPrecision n k p) (rngBits n k))).flatten

/-- Recognize a charge for generating one independent fair bit. -/
def isFairBit : ScalarWork.Step → Bool
  | .fairBit => true
  | _ => false

/-- Each trial generates exactly one bit for each position in each word. -/
theorem samplerTrace_randBits (n k p : ℕ) :
    (samplerTrace n k p).countP isFairBit = n * rngBits n k := by
  simp [samplerTrace, diagonalTrace, accumulateStep,
    storeDiagonalSteps, isFairBit]

theorem samplerTrace_allowed (n k p : ℕ) :
    ScalarWork.TraceAllowed (workingPrecision n k p) (samplerTrace n k p) := by
  have hq := workingPrecision_ge_two n k p
  intro step h
  obtain ⟨steps, hs, hstep⟩ := List.mem_flatten.mp h
  have heq := List.eq_of_mem_replicate hs
  subst steps
  rcases List.mem_append.mp hstep with hacc | hstore
  · obtain ⟨steps, hs, hstep⟩ := List.mem_flatten.mp hacc
    have heq := List.eq_of_mem_replicate hs
    subst steps
    simp [accumulateStep] at hstep
    rcases hstep with rfl | rfl | rfl | rfl <;> simp [ScalarWork.Step.Allowed, hq]
  · simp [storeDiagonalSteps] at hstore
    rcases hstore with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [ScalarWork.Step.Allowed, hq]

/-- The charged sampler work is linear in the number of bits drawn. -/
theorem samplerTrace_work (n k p : ℕ) :
    ScalarWork.work (samplerTrace n k p) = n * (4 * rngBits n k + 7) := by
  simp [ScalarWork.work, samplerTrace, diagonalTrace, accumulateStep, storeDiagonalSteps,
    Nat.mul_comm 4]

end NumStability.CertifiedTridiagonalEigenpairs
