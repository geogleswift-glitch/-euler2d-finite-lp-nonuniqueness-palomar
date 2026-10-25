module

public import RequestProject.Euler.BanachBackwardGraphCommutingInvariance
public import RequestProject.Euler.BanachDoubleReturn

@[expose] public section

set_option maxHeartbeats 1800000

noncomputable section

open Set Filter Topology
open scoped ContDiff

namespace Euler2D

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem iterate_zero_of_map_zero {F : E → E} (hF0 : F 0 = 0) (m : ℕ) : F^[m] 0 = 0 := by
  induction m with
  | zero => rfl
  | succ m ih => rw [Function.iterate_succ_apply', ih, hF0]

theorem contDiffAt_iterate_zero {F : E → E} {n : ℕ∞} (hF0 : F 0 = 0)
    (hf : ContDiffAt ℝ n F 0) (m : ℕ) : ContDiffAt ℝ n F^[m] 0 := by
  induction m with
  | zero => exact contDiffAt_id
  | succ m ih =>
    have ho : ContDiffAt ℝ n F (F^[m] 0) := by rw [iterate_zero_of_map_zero hF0]; exact hf
    simpa only [Function.iterate_succ', Function.comp_def] using ho.comp 0 ih

theorem hasFDerivAt_iterate_zero {F : E → E} {L : E →L[ℝ] E} (hF0 : F 0 = 0)
    (hf : HasFDerivAt F L 0) (m : ℕ) : HasFDerivAt F^[m] (L ^ m) 0 := by
  induction m with
  | zero => simpa only [Function.iterate_zero, pow_zero] using hasFDerivAt_id (𝕜 := ℝ) (0 : E)
  | succ m ih =>
    have ho : HasFDerivAt F L (F^[m] 0) := by rw [iterate_zero_of_map_zero hF0]; exact hf
    simpa only [Function.iterate_succ', Function.comp_def, pow_succ', ContinuousLinearMap.mul_def]
      using ho.comp 0 ih

namespace IsLocalWeightedBackwardGraph

theorem exists_iterate_invariant_radius [CompleteSpace E] {F : E → E}
    {P : E →L[ℝ] E} {ρ r : ℝ} {x : E → ℕ → E}
    (h : IsLocalWeightedBackwardGraph (banachDoubleReturn F) P ρ r x)
    (hρ : 1 ≤ ρ) (hr : 0 < r) (hP : ∀ v, P (P v) = P v)
    (hF0 : F 0 = 0) (hf : ContDiffAt ℝ 1 F 0) (m : ℕ) :
    ∃ η > 0, η ≤ r / 2 ∧ ∀ α, P α = α → ‖α‖ ≤ η →
      ‖P (F^[m] (x α 0))‖ ≤ r / 2 ∧
      x (P (F^[m] (x α 0))) = (fun n => F^[m] (x α n)) := by
  have hFT (z : E) : F (F^[m] z) = F^[m] (F z) := Function.Commute.self_iterate F m z
  have hcomm (z : E) : banachDoubleReturn F (F^[m] z) = F^[m] (banachDoubleReturn F z) := by
    change F (F (F^[m] z)) = F^[m] (F (F z))
    rw [hFT z, hFT (F z)]
  exact h.exists_commuting_map_invariant_radius hρ hr hP (iterate_zero_of_map_zero hF0 m)
    ((contDiffAt_iterate_zero hF0 hf m).differentiableAt (by norm_num))
    (Filter.Eventually.of_forall hcomm)

end IsLocalWeightedBackwardGraph

end Euler2D

end
