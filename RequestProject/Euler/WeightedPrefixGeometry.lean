module

public import RequestProject.Euler.BanachWeightedTrajectoryEnvelope

/-! A weighted ancestor bound and the current cell bound give the
full geometric prefix tube. Current k is kept outside Fin k. -/

@[expose] public section

set_option maxHeartbeats 2500000

noncomputable section

namespace Euler2D

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem norm_prefix_le_of_weighted_current {h K δ : ℝ}
    (hh : 0 < h) (hh1 : h ≤ 1) (hK : 0 ≤ K)
    (k : ℕ) (x : ℕ → E) (hx : weightedFamilyNorm h k x ≤ K)
    (hcurrent : ‖x k‖ ≤ δ) (hsmall : h * K ≤ δ) (j : Fin (k + 1)) :
    ‖x j‖ ≤ δ := by
  by_cases hj : (j : ℕ) = k
  · simpa only [hj] using hcurrent
  have hjk : (j : ℕ) < k := by have hi := j.isLt; omega
  have hp : 1 ≤ k - (j : ℕ) := by omega
  have hpow : h ^ (k - (j : ℕ)) ≤ h := by
    simpa only [pow_one] using pow_le_pow_of_le_one hh.le hh1 hp
  exact (norm_le_weightedFamilyNorm hh k x ⟨j, hjk⟩).trans
    ((mul_le_mul_of_nonneg_left hx (pow_pos hh _).le).trans
      ((mul_le_mul_of_nonneg_right hpow hK).trans hsmall))

end Euler2D

end
