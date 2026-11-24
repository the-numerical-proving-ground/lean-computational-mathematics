import ComputationalMathematics.Source.CertifiedTridiagonalEigenpairs.Retry.Execution

/-! Direct indexed reads from the two stored bands of the accepted matrix. -/

namespace NumStability.CertifiedTridiagonalEigenpairs

variable {n p : ℕ} {J : Finset ℕ}

/-- Read an entry using a diagonal read, an adjacent-band read, or the structural
zero. This avoids constructing any dense representation for the vector solver. -/
noncomputable def RetryResult.readMatrix (trial : RetryResult n J p)
    (b : Fin n → TrialWord n J p) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  .of fun i j =>
    if i = j then (trial.trial.val.diagonal[i.val]).value
    else if h : i.val + 1 = j.val then (b ⟨i.val, by have := j.isLt; omega⟩).value
    else if h : j.val + 1 = i.val then (b ⟨j.val, by have := i.isLt; omega⟩).value
    else 0

/-- Direct reads are exactly the represented matrix certified by the gate. -/
theorem RetryResult.readMatrix_eq (trial : RetryResult n J p) (b : Fin n → TrialWord n J p) :
    trial.readMatrix b = trial.matrix b := by
  ext i j
  by_cases heq : i = j
  · subst j
    simp [RetryResult.readMatrix, RetryResult.matrix, sturmTridiagonal_diagonal]
  by_cases hupper : i.val + 1 = j.val
  · let e : Fin n := ⟨i.val, by have := j.isLt; omega⟩
    have hi : e.castSucc = i := Fin.ext rfl
    have hj : e.succ = j := Fin.ext hupper
    have h := sturmTridiagonal_upper
      (fun x => (trial.trial.val.diagonal[x.val]).value) (fun x => (b x).value) e
    rw [hi, hj] at h
    simpa only [RetryResult.readMatrix, Matrix.of_apply, RetryResult.matrix, if_neg heq,
      dif_pos hupper] using h.symm
  by_cases hlower : j.val + 1 = i.val
  · let e : Fin n := ⟨j.val, by have := i.isLt; omega⟩
    have hi : e.succ = i := Fin.ext hlower
    have hj : e.castSucc = j := Fin.ext rfl
    have h := sturmTridiagonal_lower
      (fun x => (trial.trial.val.diagonal[x.val]).value) (fun x => (b x).value) e
    rw [hi, hj] at h
    simpa only [RetryResult.readMatrix, Matrix.of_apply, RetryResult.matrix, if_neg heq,
      dif_neg hupper, dif_pos hlower] using h.symm
  simp [RetryResult.readMatrix, RetryResult.matrix, heq, hupper, hlower,
    sturmTridiagonal_support _ _ i j heq hupper hlower]

end NumStability.CertifiedTridiagonalEigenpairs
