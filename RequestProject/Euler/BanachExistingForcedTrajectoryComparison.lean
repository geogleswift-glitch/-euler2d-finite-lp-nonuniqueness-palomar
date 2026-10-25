module

public import RequestProject.Euler.BanachForcedReturnComparison

/-! Compare an already existing actual forced trajectory with the same
given unforced flow. Only forcing values along that actual trajectory
are used; no regularity of an auxiliary forcing on candidate states is
assumed. -/

@[expose] public section

set_option maxHeartbeats 2000000

noncomputable section

open Set Metric
open scoped NNReal ContDiff

namespace Euler2D

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem dist_existing_forcedTrajectory_same_flow_le
    {f : E → E} {D U : Set E} (hD : IsOpen D) (hf : ContDiffOn ℝ 1 f D)
    (hUD : U ⊆ D) {T r δ ε ρ : ℝ} {c : ℝ → E}
    (hc : ContinuousOn c (Icc (0 : ℝ) T))
    (hc' : ∀ t ∈ Icc (0 : ℝ) T, HasDerivAt c (f (c t)) t)
    {K : ℝ≥0} (hT : 0 < T) (hr : 0 < r) (hδ : 0 < δ) (hε : 0 ≤ ε)
    (htube : ∀ t ∈ Icc (0 : ℝ) T, closedBall (c t) r ⊆ U)
    (hLip : LipschitzOnWith K f U)
    (hsmall : δ * Real.exp (2 * (K : ℝ) * T) < r)
    {X : E → ℝ → E} (hX : IsBanachFlowOn f D (ball (c 0) ρ) T X)
    {b : E} (hb : b ∈ ball (c 0) (min ρ δ))
    {y p : ℝ → E} (hy0 : y 0 = b) (hyc : ContinuousOn y (Icc (0 : ℝ) T))
    (hyd : ∀ t ∈ Icc (0 : ℝ) T, HasDerivAt y (f (y t) + p t) t)
    (hym : ∀ t ∈ Icc (0 : ℝ) T, y t ∈ U)
    (hp : ∀ t ∈ Icc (0 : ℝ) T, ‖p t‖ ≤ ε) :
    ∀ t ∈ Icc (0 : ℝ) T, dist (y t) (X b t) ≤ ε * t * Real.exp ((K : ℝ) * t) := by
  obtain ⟨Z, hZ, _hZclose⟩ := exists_nonautonomous_banachFlow_in_reference_tube
    (fun _ x => f x) c (fun t => f (c t)) hT hr hδ (le_refl (0 : ℝ)) hc hc' htube
    (fun _ _ => hLip) (fun _ _ => continuousOn_const)
    (fun _ _ => by simp) (by simpa only [gronwallBound_ε0] using hsmall)
  have hbX : b ∈ ball (c 0) ρ := ball_subset_ball (min_le_left _ _) hb
  have hbδ : b ∈ ball (c 0) δ := ball_subset_ball (min_le_right _ _) hb
  have heq : EqOn (Z b) (X b) (Icc (0 : ℝ) T) :=
    eqOn_of_banachODE_open hD hf (hZ.continuous b hbδ) (hX.continuous b hbX)
      (fun u hu => hUD (hZ.mem b hbδ u hu)) (hX.mem b hbX)
      (fun u hu => hZ.hasDerivAt b hbδ u ⟨hu.1, hu.2.le⟩)
      (fun u hu => hX.hasDerivAt b hbX u ⟨hu.1, hu.2.le⟩)
      (by rw [hZ.initial b hbδ, hX.initial b hbX])
  intro t ht
  have hh := dist_le_of_approx_trajectories_ODE_of_mem
    (v := fun _ z => f z) (s := fun _ => U) (K := K)
    (fun _ _ => hLip) hyc
    (fun u hu => (hyd u ⟨hu.1, hu.2.le⟩).hasDerivWithinAt)
    (εf := ε) (fun u hu => by
      simpa only [dist_eq_norm, add_sub_cancel_left] using hp u ⟨hu.1, hu.2.le⟩)
    (fun u hu => hym u ⟨hu.1, hu.2.le⟩)
    (hZ.continuous b hbδ)
    (fun u hu => (hZ.hasDerivAt b hbδ u ⟨hu.1, hu.2.le⟩).hasDerivWithinAt)
    (εg := 0) (fun _ _ => by simp)
    (fun u hu => hZ.mem b hbδ u ⟨hu.1, hu.2.le⟩)
    (δ := 0) (by rw [hy0, hZ.initial b hbδ]; simp) t ht
  rw [heq ht] at hh
  have hh' : dist (y t) (X b t) ≤ gronwallBound 0 (K : ℝ) ε t := by
    simpa only [add_zero, sub_zero] using hh
  exact hh'.trans (by simpa only [zero_add] using
    gronwallBound_le_add_mul_exp (δ := 0) K.coe_nonneg hε ht.1)

end Euler2D

end
