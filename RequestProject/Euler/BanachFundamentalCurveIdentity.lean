module

public import Mathlib

/-! The genuine fundamental operator acts on each known directional
variational curve by its actual initial value. The identity follows
from uniqueness for the real time-dependent linear ODE. -/

@[expose] public section

set_option maxHeartbeats 1000000

noncomputable section

open Set Filter Topology Metric
open scoped NNReal

namespace Euler2D

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem eqOn_banachLinearODE_of_same_initial {B : ℝ → E →L[ℝ] E} {T : ℝ}
    (hB : ContinuousOn B (Icc (0 : ℝ) T)) {x y : ℝ → E}
    (hxc : ContinuousOn x (Icc (0 : ℝ) T)) (hyc : ContinuousOn y (Icc (0 : ℝ) T))
    (hxd : ∀ t ∈ Icc (0 : ℝ) T, HasDerivAt x (B t (x t)) t)
    (hyd : ∀ t ∈ Icc (0 : ℝ) T, HasDerivAt y (B t (y t)) t) (hzero : x 0 = y 0) :
    EqOn x y (Icc (0 : ℝ) T) := by
  obtain ⟨M, hM⟩ := (isCompact_Icc.image_of_continuousOn hB).isBounded.exists_norm_le
  let K : ℝ≥0 := ⟨max M 0, le_max_right M 0⟩
  have hbound (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) : ‖B t‖ ≤ K :=
    (hM _ (mem_image_of_mem _ ht)).trans (le_max_left M 0)
  have hLip (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) : LipschitzOnWith K (B t) univ := by
    apply LipschitzOnWith.of_dist_le_mul
    intro u hu v hv
    rw [dist_eq_norm, dist_eq_norm, ← (B t).map_sub]
    exact ((B t).le_opNorm _).trans
      (mul_le_mul_of_nonneg_right (hbound t ht) (norm_nonneg _))
  exact ODE_solution_unique_of_mem_Icc_right
    (v := fun t z => B t z) (s := fun _ => (univ : Set E))
    (fun t ht => hLip t ⟨ht.1, ht.2.le⟩) hxc
    (fun t ht => (hxd t ⟨ht.1, ht.2.le⟩).hasDerivWithinAt) (fun _ _ => mem_univ _)
    hyc (fun t ht => (hyd t ⟨ht.1, ht.2.le⟩).hasDerivWithinAt) (fun _ _ => mem_univ _) hzero

theorem banachFundamentalOperator_apply_eq_curve {B A : ℝ → E →L[ℝ] E} {T : ℝ}
    (hB : ContinuousOn B (Icc (0 : ℝ) T))
    (hAc : ContinuousOn A (Icc (0 : ℝ) T)) (hA0 : A 0 = ContinuousLinearMap.id ℝ E)
    (hAd : ∀ t ∈ Icc (0 : ℝ) T, HasDerivAt A ((B t).comp (A t)) t)
    {Y : ℝ → E} (hYc : ContinuousOn Y (Icc (0 : ℝ) T))
    (hYd : ∀ t ∈ Icc (0 : ℝ) T, HasDerivAt Y (B t (Y t)) t) :
    ∀ t ∈ Icc (0 : ℝ) T, A t (Y 0) = Y t := by
  have hc : ContinuousOn (fun t => A t (Y 0)) (Icc (0 : ℝ) T) := hAc.clm_apply continuousOn_const
  have hd (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) :
      HasDerivAt (fun t => A t (Y 0)) (B t (A t (Y 0))) t := by
    have h := (hAd t ht).clm_apply (hasDerivAt_const t (Y 0))
    simpa only [ContinuousLinearMap.comp_apply, map_zero, add_zero] using h
  have he := eqOn_banachLinearODE_of_same_initial hB hc hYc hd hYd (by rw [hA0, ContinuousLinearMap.id_apply])
  exact he

end Euler2D

end
