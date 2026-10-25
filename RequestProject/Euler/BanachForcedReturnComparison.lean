module

public import RequestProject.Euler.NonautonomousBanachReferenceTube
public import RequestProject.Euler.GronwallForcingBound
public import RequestProject.Euler.BanachReferenceContinuation

/-! Whole-interval forced flows, compared to the same pre-existing
autonomous flow. Open-domain ODE uniqueness identifies the constructed
auxiliary solution with that flow; no extra stay-in-a-small-set premise
is imposed on the pre-existing flow. -/

@[expose] public section

set_option maxHeartbeats 2500000

noncomputable section

open Set Filter Topology Metric
open scoped NNReal ContDiff

namespace Euler2D

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem exists_forced_banachFlow_with_same_return_comparison
    {f : E → E} {D U : Set E} (hD : IsOpen D) (hf : ContDiffOn ℝ 1 f D)
    (hUD : U ⊆ D) {T r δ ε : ℝ} {c : ℝ → E} (hc : ContinuousOn c (Icc (0 : ℝ) T))
    (hc' : ∀ t ∈ Icc (0 : ℝ) T, HasDerivAt c (f (c t)) t)
    {K J : ℝ≥0} (hT : 0 < T) (hr : 0 < r) (hδ : 0 < δ) (hε : 0 ≤ ε)
    (htube : ∀ t ∈ Icc (0 : ℝ) T, closedBall (c t) r ⊆ U)
    (hLip : LipschitzOnWith K f U)
    (hsmall₀ : δ * Real.exp (2 * (K : ℝ) * T) < r)
    (hsmall : (δ + ε * T) * Real.exp (2 * ((K : ℝ) + J) * T) < r)
    (q : ℝ → E → E)
    (hqLip : ∀ t ∈ Icc (0 : ℝ) T, LipschitzOnWith J (q t) U)
    (hqc : ∀ y ∈ U, ContinuousOn (fun t => q t y) (Icc (0 : ℝ) T))
    (hqbound : ∀ t ∈ Icc (0 : ℝ) T, ∀ y ∈ U, ‖q t y‖ ≤ ε) :
    ∃ Y : E → ℝ → E,
      IsNonautonomousBanachFlowOn (fun t y => f y + q t y) D (ball (c 0) δ) T Y ∧
      (∀ b ∈ ball (c 0) δ, ∀ t ∈ Icc (0 : ℝ) T, Y b t ∈ ball (c t) r) ∧
      ∀ {ρ : ℝ} {X : E → ℝ → E},
        IsBanachFlowOn f D (ball (c 0) ρ) T X →
        ∀ b ∈ ball (c 0) (min ρ δ), ∀ t ∈ Icc (0 : ℝ) T,
          dist (Y b t) (X b t) ≤ ε * t * Real.exp ((K : ℝ) * t) := by
  have hcU (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) : c t ∈ U :=
    htube t ht (mem_closedBall_self hr.le)
  obtain ⟨Z, hZ, hZmem⟩ := exists_nonautonomous_banachFlow_in_reference_tube
    (fun _ x => f x) c (fun t => f (c t)) hT hr hδ (le_refl (0 : ℝ)) hc hc' htube
    (fun _ _ => hLip) (fun _ _ => continuousOn_const)
    (fun _ _ => by simp) (by simpa only [gronwallBound_ε0] using hsmall₀)
  have htotalLip (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) :
      LipschitzOnWith (K + J) (fun y => f y + q t y) U := hLip.add (hqLip t ht)
  have herror (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) :
      dist (f (c t)) (f (c t) + q t (c t)) ≤ ε := by
    simpa only [dist_eq_norm, sub_add_cancel_left, norm_neg] using hqbound t ht (c t) (hcU t ht)
  have hsmall' : gronwallBound δ (2 * ((K + J : ℝ≥0) : ℝ)) ε T < r :=
    (gronwallBound_le_add_mul_exp (by positivity) hε hT.le).trans_lt
      (by simpa only [NNReal.coe_add] using hsmall)
  obtain ⟨Y, hY, hYmem⟩ := exists_nonautonomous_banachFlow_in_reference_tube
    (fun t y => f y + q t y) c (fun t => f (c t)) hT hr hδ hε hc hc' htube
    htotalLip (fun y hy => continuousOn_const.add (hqc y hy)) herror hsmall'
  refine ⟨Y, ⟨hY.initial, hY.continuous, hY.hasDerivAt,
    fun b hb t ht => hUD (hY.mem b hb t ht)⟩,
    fun b hb t ht => (hYmem b hb t ht).2, ?_⟩
  intro ρ X hX b hb t ht
  have hbX : b ∈ ball (c 0) ρ := ball_subset_ball (min_le_left _ _) hb
  have hbδ : b ∈ ball (c 0) δ := ball_subset_ball (min_le_right _ _) hb
  have heq : EqOn (Z b) (X b) (Icc (0 : ℝ) T) :=
    eqOn_of_banachODE_open hD hf (hZ.continuous b hbδ) (hX.continuous b hbX)
      (fun u hu => hUD (hZ.mem b hbδ u hu)) (hX.mem b hbX)
      (fun u hu => hZ.hasDerivAt b hbδ u ⟨hu.1, hu.2.le⟩)
      (fun u hu => hX.hasDerivAt b hbX u ⟨hu.1, hu.2.le⟩)
      (by rw [hZ.initial b hbδ, hX.initial b hbX])
  have hh := dist_le_of_approx_trajectories_ODE_of_mem
    (v := fun _ y => f y) (s := fun _ => U) (K := K)
    (fun _ _ => hLip) (hY.continuous b hbδ)
    (fun u hu => (hY.hasDerivAt b hbδ u ⟨hu.1, hu.2.le⟩).hasDerivWithinAt)
    (εf := ε) (fun u hu => by
      simpa only [dist_eq_norm, add_sub_cancel_left] using
        hqbound u ⟨hu.1, hu.2.le⟩ (Y b u) (hY.mem b hbδ u ⟨hu.1, hu.2.le⟩))
    (fun u hu => hY.mem b hbδ u ⟨hu.1, hu.2.le⟩)
    (hZ.continuous b hbδ)
    (fun u hu => (hZ.hasDerivAt b hbδ u ⟨hu.1, hu.2.le⟩).hasDerivWithinAt)
    (εg := 0) (fun _ _ => by simp)
    (fun u hu => hZ.mem b hbδ u ⟨hu.1, hu.2.le⟩)
    (δ := 0) (by rw [hY.initial b hbδ, hZ.initial b hbδ]; simp) t ht
  rw [heq ht] at hh
  have hh' : dist (Y b t) (X b t) ≤ gronwallBound 0 (K : ℝ) ε t := by
    simpa only [add_zero, sub_zero] using hh
  exact hh'.trans (by simpa only [zero_add] using
    gronwallBound_le_add_mul_exp (δ := 0) K.coe_nonneg hε ht.1)

end Euler2D

end
