import ComputationalMathematics.Source.CertifiedTridiagonalEigenpairs.ExactBranchExecution
import ComputationalMathematics.Source.CertifiedTridiagonalEigenpairs.Retry.NormalizedInput
import ComputationalMathematics.Source.CertifiedTridiagonalEigenpairs.AcceptedOutput.RequestedRanks

/-! The nontrivial tridiagonal setup and its ordered requested neighborhood (§3.1). -/

namespace NumStability.CertifiedTridiagonalEigenpairs

open FloatingPointFormat.UnboundedBinary ScalarWork

/-- Observe the clipping tests and, for a valid rank, its flag write. -/
def rankFlagMarkTrace (N rank : ℕ) : List Step :=
  [.comparison, .comparison] ++ (if 1 ≤ rank ∧ rank ≤ N then [.index, .index] else [])

/-- Observe initialization, the four mark attempts per requested rank, and
the reads, tests and conditional output writes of the two rank scans. -/
noncomputable def rankFlagTrace (N : ℕ) (J : Finset ℕ) : List Step :=
  let requested := trialRequestedFlags N J
  let neighbors := trialNeighborFlags N J
  List.replicate (2 * N) .index ++
    J.toList.flatMap (fun rank =>
      [.index, .index, .index] ++ rankFlagMarkTrace N rank ++ rankFlagMarkTrace N rank ++
        rankFlagMarkTrace N (rank - 1) ++ rankFlagMarkTrace N (rank + 1)) ++
    (List.finRange N).flatMap (fun i =>
      [.index, .index, .comparison, .comparison] ++
        (if requested[i.val] then [.index] else []) ++
        (if neighbors[i.val] then [.index] else []))

namespace SourceTargets

/-- Exact binary scaling, parameter values and representability, and the
rank lists obtained by marking and scanning both sets of flags. -/
def tridiagonalScalingParameters : Prop :=
  ∀ {n p : ℕ} (hp : 2 ≤ p) (a : Fin (n + 1) → Word p hp) (b : Fin n → Word p hp)
    (J : Finset ℕ), 2 ≤ n + 1 → storedTridiagonal a b ≠ 0 →
    J.Nonempty → J ⊆ Finset.Icc 1 (n + 1) → precisionGuard (n + 1) p →
    let T := storedTridiagonal a b
    let entry := largestStoredEntry a b
    let scan := runNormalizationScan a b
    let cover := runNormalizationScan (n := 0) (fun _ => entry) Fin.elim0
    let k := J.card
    let L := Nat.clog 2 (n + 1)
    let Lk := Nat.clog 2 k
    let N := nextPowerOfTwo (n + 1)
    let Nk := nextPowerOfTwo k
    let q := workingPrecision (n + 1) k p
    let u := unitRoundoff p
    let delta := perturbationScale p
    let g := gapScale (n + 1) k p
    let gap := certifiedGap (n + 1) k p
    let alpha := gapLabelError (n + 1) k p
    let eps := gapTolerance (n + 1) k p
    let eta := vectorTolerance (n + 1) k p
    let w := workingRoundoff (n + 1) k p
    let Jplus := requestedNeighborRanks (n + 1) J
    let Jscan := requestedRankScan n J
    let JplusScan := trialRanks n J
    (∃ i j, |entry.value| = |T i j|) ∧ (∀ i j, |T i j| ≤ |entry.value|) ∧
    work scan.trace ≤ 32 * (n + 1) ∧ TraceAllowed p scan.trace ∧
    storage scan.liveWords ≤ 24 * (n + 1) ∧
    (∃ e r : ℤ, coveringExponent entry = some e ∧ scan.exponent = some r ∧
      cover.exponent = some r ∧ work cover.trace ≤ 32 ∧
      let P := (2 : ℝ) ^ e
      let R := (2 : ℝ) ^ r
      let S := normalizedTridiagonal a b r
      let diagonal := Vector.ofFn (fun i => normalizeTrialWord (n := n) (J := J) r (a i))
      let subdiagonal := Vector.ofFn (fun i => normalizeTrialWord (n := n) (J := J) r (b i))
      let rowMax := Finset.univ.sup' Finset.univ_nonempty (fun i => ∑ j, |S i j|)
      |entry.value| ≤ P ∧ (∀ l : ℤ, |entry.value| ≤ (2 : ℝ) ^ l → P ≤ (2 : ℝ) ^ l) ∧
      R = 4 * P ∧ S = R⁻¹ • T ∧
      sturmTridiagonal (fun i => (diagonal.get i).value) (fun i => (subdiagonal.get i).value) =
        S ∧ (∀ i j, |S i j| ≤ 1 / 4) ∧
      realMatrixOperatorNorm S ≤ rowMax ∧ rowMax ≤ 3 / 4 ∧ R < 8 * realMatrixOperatorNorm T) ∧
    delta = u / 256 ∧ g = delta / (1024 * (N : ℝ) ^ 3 * Nk) ∧
    g = u * (2 : ℝ) ^ (-18 : ℤ) * ((N : ℝ) ^ 3)⁻¹ * (Nk : ℝ)⁻¹ ∧ gap = g / 2 ∧
    rngBits (n + 1) k = 3 * L + Lk + 16 ∧ alpha = g / 64 ∧ eps = g / 128 ∧
    eta = gap * (2 : ℝ) ^ (-(⌈(p : ℝ) / 2⌉₊ : ℤ)) / (16 * quarterPowerOfTwo (n + 1)) ∧
    w = (2 : ℝ) ^ (-(q : ℤ)) ∧
    (∀ x ∈ [delta, g, gap, alpha, eps, eta, w], ∃ e : ℤ, x = (2 : ℝ) ^ e) ∧
    (∀ j, j ∈ Jplus ↔ j ∈ Finset.Icc 1 (n + 1) ∧
      ∃ i ∈ J, j = i - 1 ∨ j = i ∨ j = i + 1) ∧ Jplus.card ≤ 3 * k ∧
    (∀ i : Fin (n + 1), i ∈ Jscan ↔ i.val + 1 ∈ J) ∧
    (∀ i : Fin (n + 1), i ∈ JplusScan ↔ i.val + 1 ∈ Jplus) ∧
    Jscan.Pairwise (· < ·) ∧ JplusScan.Pairwise (· < ·) ∧
    work (rankFlagTrace (n + 1) J) ≤ 19 * (n + 1 + k)

end SourceTargets

end NumStability.CertifiedTridiagonalEigenpairs
