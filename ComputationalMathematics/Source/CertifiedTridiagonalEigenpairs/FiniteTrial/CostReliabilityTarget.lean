import ComputationalMathematics.Source.CertifiedTridiagonalEigenpairs.FiniteTrial.Target

/-! Source statement for the cost and reliability of one finite trial (`rand:trial`). -/

namespace NumStability.CertifiedTridiagonalEigenpairs

open FloatingPointFormat.UnboundedBinary
open scoped ENNReal

/-- The actual finite experiment rejects on precisely these bit words. -/
def trialRejected (n p : ℕ) (J : Finset ℕ) (a : Fin (n + 1) → TrialWord n J p)
    (b : Fin n → TrialWord n J p) : Set (Fin (n + 1) → FairBitWord (rngBits (n + 1) J.card)) :=
  {words | trialAccepts n p J a b words = false}

namespace SourceTargets

/-- The prescribed independent fair bits give a rejection probability at most
`β = 3 / (2048 * (2 ^ clog 2 (n + 1)) ^ 2)`, uniformly over the eligible input. -/
def finiteTrialUniformRejection : Prop :=
  ∀ (n p : ℕ) (J : Finset ℕ) (a : Fin (n + 1) → TrialWord n J p)
    (b : Fin n → TrialWord n J p),
    2 ≤ n + 1 → precisionGuard (n + 1) p → J.Nonempty → J ⊆ Finset.Icc 1 (n + 1) →
    (∀ i, |(a i).value| ≤ 1 / 4) → (∀ i, |(b i).value| ≤ 1 / 4) →
    (trialBitLaw (n + 1) J.card).toMeasure (trialRejected n p J a b) ≤
      ENNReal.ofReal (rejectionBound (n + 1))

/-- The one-trial theorem couples its deterministic certificate and exact
work and bit bounds with the rejection probability of the same run. -/
def finiteTrialCostReliability : Prop :=
  finiteTrialCertificate ∧ finiteTrialUniformRejection

end SourceTargets
end NumStability.CertifiedTridiagonalEigenpairs
