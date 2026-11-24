import ComputationalMathematics.Source.CertifiedTridiagonalEigenpairs.BidiagonalSVDInputPrecisionTarget

namespace NumStability.CertifiedTridiagonalEigenpairs

open BidiagonalSVDRequest FloatingPointFormat.UnboundedBinary
open scoped Matrix

/-- The native bidiagonal input, ordered triplet task, and working-precision formula. -/
theorem bidiagonalSVDInputPrecision : SourceTargets.bidiagonalSVDInputPrecision := by
  intro n p hp upper a b I hI hInonempty _hguard
  dsimp only
  have hlog (m : ℕ) : ⌈Real.logb 2 (m : ℝ)⌉₊ = Nat.clog 2 m := by
    simpa using Real.natCeil_logb_natCast 2 m
  rw [hlog (n + 1), hlog I.card]
  obtain ⟨U, V, hσ, hσ₀, hB⟩ :=
    exists_orthonormalBases_ascendingRealSpectrum (storedBidiagonal upper a b)
  refine ⟨Finset.card_pos.mpr hInonempty, ?_, (requestedRankOrder hI).strictMono,
    requestedRankOrder_covers hI, hσ, hσ₀, ?_, rfl, ?_⟩
  · simpa using Fintype.card_le_of_injective (requestedRankOrder hI)
      (requestedRankOrder hI).injective
  · refine ⟨U, V, hB, ?_, ?_⟩
    · let M := orthonormalBasisMatrix U
      let N := orthonormalBasisMatrix V
      let D := Matrix.diagonal (ascendingRealSpectrum (storedBidiagonal upper a b))
      have h : storedBidiagonal upper a b * N = M * D := by
        conv_lhs => rw [hB]
        dsimp only [M, N]
        rw [mul_assoc, orthonormalBasisMatrix_transpose_mul_self, Matrix.mul_one]
      dsimp only [D] at h
      ext i j
      have hentry := congrArg (fun A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ =>
        A i (requestedRankOrder hI j)) h
      dsimp only at hentry
      simp only [Matrix.mul_diagonal] at hentry ⊢
      simpa [Matrix.mul_apply, Function.comp_def, M, N] using hentry
    · let M := orthonormalBasisMatrix U
      let N := orthonormalBasisMatrix V
      let D := Matrix.diagonal (ascendingRealSpectrum (storedBidiagonal upper a b))
      have h : (storedBidiagonal upper a b).transpose * M = N * D := by
        conv_lhs => rw [hB]
        dsimp only [M, N, D]
        simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.diagonal_transpose,
          mul_assoc, orthonormalBasisMatrix_transpose_mul_self, Matrix.mul_one]
      dsimp only [D] at h
      ext i j
      have hentry := congrArg (fun A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ =>
        A i (requestedRankOrder hI j)) h
      dsimp only at hentry
      simp only [Matrix.mul_diagonal] at hentry ⊢
      simpa [Matrix.mul_apply, Function.comp_def, M, N] using hentry
  · intro out
    exact ⟨fun i => (out.labels i).native_value, fun j i => (out.leftWords i j).native_value,
      fun j i => (out.rightWords i j).native_value⟩

end NumStability.CertifiedTridiagonalEigenpairs
