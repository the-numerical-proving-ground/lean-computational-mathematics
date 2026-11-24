import ComputationalMathematics.Analysis.FloatingPointArithmetic.UnboundedBinary.VectorNormalization

/-! # Indexed implementation of rounded vector normalization -/

namespace NumStability.FloatingPointFormat.UnboundedBinary.Word

variable {n p q : ℕ} {hq : 2 ≤ q}

private noncomputable def squareWord (x : Word q hq) : Word q hq :=
  (ScalarOperation.mul x x).eval

private noncomputable def sumSquaresLoop (x : Vector (Word q hq) n) :
    (remaining k : ℕ) → k + remaining ≤ n → Word q hq → Word q hq
  | 0, _, _, s => s
  | remaining + 1, k, h, s =>
    let term := squareWord (x.get ⟨k, by omega⟩)
    sumSquaresLoop x remaining (k + 1) (by omega) ((ScalarOperation.add s term).eval)

private def readPrefix {α : Type*} (x : Vector α n) {k : ℕ} (hkn : k ≤ n) :
    Fin k → α := fun i => x.get (i.castLE hkn)

private theorem sumSquares_prefix_succ (x : Vector (Word q hq) n) {k : ℕ}
    (hk : 0 < k) (hkn : k + 1 ≤ n) :
    sumSquares (readPrefix x hkn) =
      (ScalarOperation.add (sumSquares (readPrefix x (show k ≤ n by omega)))
        (squareWord (x.get ⟨k, by omega⟩))).eval := by
  cases k with
  | zero => omega
  | succ k => rfl

private theorem sumSquaresLoop_eq (x : Vector (Word q hq) n)
    (remaining k : ℕ) (hb : k + remaining ≤ n) (hk : 0 < k) :
    sumSquaresLoop x remaining k hb (sumSquares (readPrefix x (show k ≤ n by omega))) =
      sumSquares (readPrefix x hb) := by
  induction remaining generalizing k with
  | zero => rfl
  | succ remaining ih =>
    rw [sumSquaresLoop]
    have hkn : k + 1 ≤ n := by omega
    rw [← sumSquares_prefix_succ x hk hkn, ih (k + 1) (by omega) (by omega)]
    have heq : k + 1 + remaining = k + (remaining + 1) := by omega
    have hc := congrArg (fun m => if hmn : m ≤ n then sumSquares (readPrefix x hmn) else .zero) heq
    simpa only [dif_pos (show k + 1 + remaining ≤ n by omega), dif_pos hb] using hc

/-- Store the first square once and accumulate the remaining squares using
direct array reads and a single running sum. -/
noncomputable def sumSquaresScan (x : Vector (Word q hq) n) : Word q hq :=
  if hn : 0 < n then
    sumSquaresLoop x (n - 1) 1 (by omega) (squareWord (x.get ⟨0, hn⟩))
  else .zero

theorem sumSquaresScan_eq (x : Vector (Word q hq) n) :
    sumSquaresScan x = sumSquares x.get := by
  by_cases hn : 0 < n
  · rw [sumSquaresScan, dif_pos hn]
    have hb : 1 + (n - 1) ≤ n := by omega
    have hseed : squareWord (x.get ⟨0, hn⟩) = sumSquares (readPrefix x (show 1 ≤ n by omega)) :=
      rfl
    rw [hseed, sumSquaresLoop_eq _ _ _ hb (by decide)]
    have heq : 1 + (n - 1) = n := by omega
    have h := congrArg (fun k => if hk : k ≤ n then sumSquares (readPrefix x hk) else .zero) heq
    simpa only [dif_pos hb, dif_pos (le_refl n), readPrefix, Fin.castLE_refl] using h
  · have hzero : n = 0 := by omega
    subst n
    rfl

/-- The one rounded square root of the indexed sum. -/
noncomputable def roundedNormScan (x : Vector (Word q hq) n) : Word q hq :=
  (ScalarOperation.sqrt (sumSquaresScan x) (by rw [sumSquaresScan_eq]; exact sumSquares_nonneg _)).eval

theorem roundedNormScan_eq (x : Vector (Word q hq) n) :
    roundedNormScan x = roundedNorm x.get := by
  change round q hq (Real.sqrt (sumSquaresScan x).value) =
    round q hq (Real.sqrt (sumSquares x.get).value)
  rw [sumSquaresScan_eq]

/-- Normalize and convert in one indexed output pass using a shared rounded
denominator. -/
noncomputable def normalizeToScan (p : ℕ) (hp : 2 ≤ p) (x : Vector (Word q hq) n)
    (hx : euclidean x.get ≠ 0) : Vector (Word p hp) n :=
  let d := roundedNormScan x
  have hd : d.value ≠ 0 := by
    dsimp [d]
    rw [roundedNormScan_eq]
    exact (roundedNorm_pos _ hx).ne'
  Vector.ofFn fun i => ((ScalarOperation.div (x.get i) d hd).eval).convert p hp

theorem normalizeToScan_get (hp : 2 ≤ p) (x : Vector (Word q hq) n)
    (hx : euclidean x.get ≠ 0) :
    (normalizeToScan p hp x hx).get = normalizeTo p hp x.get hx := by
  funext i
  change (normalizeToScan p hp x hx)[i.val] = _
  rw [normalizeToScan, Vector.getElem_ofFn]
  change (round q hq ((x.get i).value / (roundedNormScan x).value)).convert p hp =
    (round q hq ((x.get i).value / (roundedNorm x.get).value)).convert p hp
  rw [roundedNormScan_eq]

end NumStability.FloatingPointFormat.UnboundedBinary.Word
