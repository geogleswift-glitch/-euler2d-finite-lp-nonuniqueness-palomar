module

public import RequestProject.Euler.BanachWeightedTrajectoryEnvelope

/-! Dropping the old parent from one and the same actual family gives
a one-sided reset of the weighted maximum. No equality of maxima over
different index sets and no replacement trajectory are used. -/

@[expose] public section

set_option maxHeartbeats 3000000

noncomputable section

open Set

namespace Euler2D

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem weightedFamilyNorm_reset_le {h : ℝ} (hh : 0 < h) (k : ℕ) (x : ℕ → E) :
    weightedFamilyNorm h (k - 1) x ≤ h * weightedFamilyNorm h k x := by
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg hh.le (norm_nonneg _))).mpr
  intro j
  let jj : Fin k := ⟨j, by omega⟩
  have hn := norm_le_weightedFamilyNorm hh k x jj
  have hw : 0 < h ^ (k - 1 - (j : ℕ)) := pow_pos hh _
  change ‖(h ^ (k - 1 - (j : ℕ)))⁻¹ • x j‖ ≤ _
  rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hw]
  apply (inv_mul_le_iff₀ hw).mpr
  have he : k - (j : ℕ) = (k - 1 - (j : ℕ)) + 1 := by omega
  change ‖x j‖ ≤ h ^ (k - (j : ℕ)) * weightedFamilyNorm h k x at hn
  rw [he, pow_succ] at hn
  change ‖x j‖ ≤ h ^ (k - 1 - (j : ℕ)) * (h * weightedFamilyNorm h k x)
  simpa only [mul_assoc] using hn

theorem weightedFamilyNorm_reset_bound {h K : ℝ} (hh : 0 < h) (k : ℕ) (x : ℕ → E)
    (hbound : weightedFamilyNorm h k x ≤ K) :
    weightedFamilyNorm h (k - 1) x ≤ K * h := by
  exact (weightedFamilyNorm_reset_le hh k x).trans
    (by simpa only [mul_comm] using mul_le_mul_of_nonneg_left hbound hh.le)

theorem norm_ancestor_after_weighted_reset {h K : ℝ} (hh : 0 < h) (k : ℕ) (x : ℕ → E)
    (hbound : weightedFamilyNorm h k x ≤ K) (j : Fin (k - 1)) :
    ‖x j‖ ≤ K * h ^ ((k - 1 - (j : ℕ)) + 1) := by
  let jj : Fin k := ⟨j, by omega⟩
  have hn := norm_le_weightedFamilyNorm hh k x jj
  have he : k - (j : ℕ) = (k - 1 - (j : ℕ)) + 1 := by omega
  change ‖x j‖ ≤ h ^ (k - (j : ℕ)) * weightedFamilyNorm h k x at hn
  exact hn.trans (by simpa only [he, mul_comm] using
    mul_le_mul_of_nonneg_left hbound (pow_pos hh (k - (j : ℕ))).le)

theorem norm_parent_after_weighted_reset {h K : ℝ} (hh : 0 < h) {k : ℕ} (hk : 2 ≤ k)
    (x : ℕ → E) (hbound : weightedFamilyNorm h k x ≤ K) :
    ‖x (k - 2)‖ ≤ K * h ^ 2 := by
  have hn := norm_ancestor_after_weighted_reset hh k x hbound (⟨k - 2, by omega⟩ : Fin (k - 1))
  have he : k - 1 - (k - 2) + 1 = 2 := by omega
  simpa only [he] using hn

end Euler2D

end
