import ComputationalMathematics.Analysis.Eigenvalues.ComplexHermitianL1.Defs
import ComputationalMathematics.Analysis.FloatingPointArithmetic.UnboundedBinary.Basic
import ComputationalMathematics.Analysis.OrderStatistics.CountIntegral
import ComputationalMathematics.Analysis.SingularValues.CommonWitnessBlocks
import ComputationalMathematics.Analysis.SingularValues.FullRealSVD.Unsorted
import ComputationalMathematics.Analysis.SingularValues.MirskyL1
import ComputationalMathematics.Order.Finset.OrderedCompletion.Basic

/-!
# Rank completion for selected bidiagonal singular triplets

The source's ordered perturbation, threshold-count cancellation, and complementary
clipping use the actual spectra of `B`, `B + E₀`, and the unchanged compression.
The previously established label, preliminary perturbation, and polar-distance
bounds are inputs to the rank-completion step.
-/

namespace NumStability.CertifiedTridiagonalEigenpairs.ClaimTargets

open CommonWitnessBlocks ComplexHermitianL1 FloatingPointFormat.UnboundedBinary Matrix.Bipartite
  OrderStatistics
open scoped BigOperators ComplexOrder MeasureTheory

/-- The Hermitian estimate and the trace of its common upper bound. -/
def hermitianOrderedPerturbation : Prop :=
  ∀ (n : ℕ) (F G : Matrix (Fin n) (Fin n) ℂ)
    (hF : F.IsHermitian) (hG : G.IsHermitian),
    let plus := (hF.sub hG).cfc (fun x : ℝ => max x 0)
    let minus := (hF.sub hG).cfc (fun x : ℝ => max (-x) 0)
    let K := G + plus
    F - G = plus - minus ∧ plus.PosSemidef ∧ minus.PosSemidef ∧
    K = F + minus ∧ (K - F).PosSemidef ∧ (K - G).PosSemidef ∧
    (∑ i, |complexOrderedEigenvalue hF i - complexOrderedEigenvalue hG i|) ≤
      Complex.re (2 * K.trace - F.trace - G.trace) ∧
    2 * K.trace - F.trace - G.trace = (complexNuclearNorm (F - G) : ℂ)

/-- The ordered singular perturbation, exact count identity, and construction
using the same selected columns and the same complementary singular factors. -/
def svdIndexedCompletion : Prop :=
  hermitianOrderedPerturbation ∧
  (∀ (n : ℕ) (B E₀ : Matrix (Fin n) (Fin n) ℝ),
    realMatrixNuclearNorm (finEmbedding (B + E₀) - finEmbedding B) = 2 * realMatrixNuclearNorm E₀ ∧
    (∑ i, |hermitianOrderedEigenvalue (finEmbedding_isHermitian (B + E₀)) i -
      hermitianOrderedEigenvalue (finEmbedding_isHermitian B) i|) =
      2 * ∑ i, |ascendingRealSpectrum (B + E₀) i - ascendingRealSpectrum B i| ∧
    (∑ i, |ascendingRealSpectrum (B + E₀) i - ascendingRealSpectrum B i|) ≤
      realMatrixNuclearNorm E₀) ∧
  (∀ (n : ℕ) (a b : Fin n → ℝ), Monotone a → Monotone b →
    (∫ x : ℝ, |countLE a x - countLE b x|) = ∑ i, |a i - b i|) ∧
  (∀ (n k p : ℕ), 2 ≤ n → 1 ≤ k →
    ∀ (I : Fin k → Fin n) (hI : StrictMono I)
      (B : Matrix (Fin n) (Fin n) ℝ)
      (Uhat Vhat Q P : Matrix (Fin n) (Fin k) ℝ)
      (Qperp Pperp : Matrix (Fin n) (Fin (n - k)) ℝ) (s : Fin k → ℝ),
      Monotone s → (∀ j, 0 ≤ s j) →
      (Matrix.fromCols Q Qperp).transpose * Matrix.fromCols Q Qperp = 1 →
      (Matrix.fromCols P Pperp).transpose * Matrix.fromCols P Pperp = 1 →
      let u := unitRoundoff p
      let delta := 16 * u * realMatrixOperatorNorm B
      let distance := 4 * Real.sqrt (k : ℝ) * u
      let C₀ := Qperp.transpose * B * Pperp
      let B₀ := Q * Matrix.diagonal s * P.transpose + Qperp * C₀ * Pperp.transpose
      let E₀ := B₀ - B
      let lambda := ascendingRealSpectrum B
      (∀ j, |s j - lambda (I j)| ≤ delta) →
      realMatrixNuclearNorm E₀ ≤ 960 * (k : ℝ) * u * realMatrixOperatorNorm B →
      max (realMatrixOperatorNorm (Uhat - Q)) (realMatrixOperatorNorm (Vhat - P)) ≤ distance →
      let slots : Fin k ↪ Fin n := ⟨I, hI.injective⟩
      let J := orderedComplement slots
      let t := ascendingRealSpectrum C₀
      let w := ascendingRealSpectrum (B + E₀)
      let d := completeSelectedValues I lambda s
      w = combinedValues slots s t ∘ Tuple.sort (combinedValues slots s t) ∧
      (∀ x : ℝ, countLE t x - countLE (lambda ∘ J) x =
        countLE w x - countLE lambda x - (countLE s x - countLE (lambda ∘ I) x)) ∧
      (∑ l, |t l - lambda (J l)|) ≤ realMatrixNuclearNorm E₀ + ∑ j, |s j - lambda (I j)| ∧
      (∀ l, |d (J l) - lambda (J l)| ≤ delta) ∧
      Monotone d ∧ (∀ i, 0 ≤ d i) ∧ (∀ j, d (I j) = s j) ∧
      ∃ A D : Matrix (Fin (n - k)) (Fin (n - k)) ℝ,
        A.transpose * A = 1 ∧ D.transpose * D = 1 ∧
        C₀ = A * Matrix.diagonal t * D.transpose ∧
        let C := A * Matrix.diagonal (d ∘ J) * D.transpose
        let U := (Matrix.fromCols Q (Qperp * A)).submatrix id (slotEquiv slots).symm
        let V := (Matrix.fromCols P (Pperp * D)).submatrix id (slotEquiv slots).symm
        let W := U * Matrix.diagonal d * V.transpose
        let E := W - B
        U.transpose * U = 1 ∧ V.transpose * V = 1 ∧
        U.submatrix id I = Q ∧ V.submatrix id I = P ∧
        U.submatrix id J = Qperp * A ∧ V.submatrix id J = Pperp * D ∧
        B + E = W ∧
        W = Q * Matrix.diagonal s * P.transpose + Qperp * C * Pperp.transpose ∧
        realMatrixOperatorNorm (C - C₀) ≤ realMatrixNuclearNorm E₀ + ((k : ℝ) + 1) * delta ∧
        (k = n → C = C₀ ∧ W = B₀) ∧
        realMatrixOperatorNorm E ≤ 2 * realMatrixNuclearNorm E₀ + ((k : ℝ) + 1) * delta ∧
        2 * realMatrixNuclearNorm E₀ + ((k : ℝ) + 1) * delta ≤
          1952 * (k : ℝ) * u * realMatrixOperatorNorm B ∧
        max (realMatrixOperatorNorm (Uhat - U.submatrix id I))
          (realMatrixOperatorNorm (Vhat - V.submatrix id I)) ≤ distance)

end NumStability.CertifiedTridiagonalEigenpairs.ClaimTargets
