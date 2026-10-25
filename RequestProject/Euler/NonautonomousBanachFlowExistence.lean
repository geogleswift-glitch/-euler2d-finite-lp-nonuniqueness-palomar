module

public import RequestProject.Euler.LocalBanachFlowExistence

/-! A genuine common local flow for time-dependent contour forcing.
Time continuity and a uniform local spatial Lipschitz bound suffice;
the forcing is not assumed differentiable in time. Picard solutions
on a larger interval provide actual derivatives at both end points. -/

@[expose] public section

set_option maxHeartbeats 2500000

noncomputable section

open Set Filter Topology Metric ODE
open scoped NNReal

namespace Euler2D

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

structure IsNonautonomousBanachFlowOn (f : ℝ → E → E) (U V : Set E)
    (T : ℝ) (X : E → ℝ → E) : Prop where
  initial : ∀ b ∈ V, X b 0 = b
  continuous : ∀ b ∈ V, ContinuousOn (X b) (Icc (0 : ℝ) T)
  hasDerivAt : ∀ b ∈ V, ∀ t ∈ Icc (0 : ℝ) T, HasDerivAt (X b) (f t (X b t)) t
  mem : ∀ b ∈ V, ∀ t ∈ Icc (0 : ℝ) T, X b t ∈ U

theorem exists_local_nonautonomous_banachFlow [CompleteSpace E]
    (F : ℝ → E → E) (x : E) {K : ℝ≥0} {U : Set E} {T₀ : ℝ}
    (hT₀ : 0 < T₀) (hU : U ∈ 𝓝 x)
    (hLip : ∀ t ∈ Icc (-T₀) T₀, LipschitzOnWith K (F t) U)
    (hcont : ∀ y ∈ U, ContinuousOn (fun t => F t y) (Icc (-T₀) T₀)) :
    ∃ a > 0, ball x a ⊆ U ∧ ∃ T > 0, T ≤ T₀ ∧ ∃ X : E → ℝ → E,
      IsNonautonomousBanachFlowOn F (ball x a) (ball x (a / 4)) T X := by
  classical
  obtain ⟨a, ha, hball⟩ := Metric.mem_nhds_iff.mp hU
  have hx : x ∈ U := mem_of_mem_nhds hU
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn (hcont x hx)
  let L : ℝ := (K : ℝ) * a + |C| + 1
  have hL : 0 < L := by dsimp only [L]; positivity
  have hb (t : ℝ) (ht : t ∈ Icc (-T₀) T₀) (y : E)
      (hy : y ∈ closedBall x (a / 2)) : ‖F t y‖ ≤ L := by
    have hyU := hball (closedBall_subset_ball (half_lt_self ha) hy)
    have hd := (hLip t ht).dist_le_mul y hyU x hx
    have hdist : dist y x ≤ a := (mem_closedBall.mp hy).trans (half_le_self ha.le)
    calc
      ‖F t y‖ ≤ ‖F t y - F t x‖ + ‖F t x‖ := norm_le_norm_sub_add _ _
      _ ≤ (K : ℝ) * a + |C| := by
        rw [← dist_eq_norm]
        exact add_le_add (hd.trans (mul_le_mul_of_nonneg_left hdist K.coe_nonneg))
          ((hC t ht).trans (le_abs_self C))
      _ ≤ L := le_add_of_nonneg_right zero_le_one
  let T : ℝ := min (T₀ / 4) (a / (8 * L))
  have hT : 0 < T := lt_min (by positivity) (div_pos ha (by positivity))
  have hTmax : T ≤ T₀ := (min_le_left _ _).trans (by linarith)
  have htime : Icc (-(2 * T)) (2 * T) ⊆ Icc (-T₀) T₀ := by
    intro t ht
    have hTs := min_le_left (T₀ / 4) (a / (8 * L))
    change T ≤ T₀ / 4 at hTs
    constructor <;> linarith [ht.1, ht.2]
  let t₀ : Icc (-(2 * T)) (2 * T) := ⟨0, by constructor <;> linarith⟩
  have hpl : IsPicardLindelof F t₀ x
      (NNReal.mk (a / 2) (half_pos ha).le) (NNReal.mk (a / 4) (by positivity))
      (NNReal.mk L hL.le) K := by
    refine ⟨fun t ht => (hLip t (htime ht)).mono
      ((closedBall_subset_ball (half_lt_self ha)).trans hball), ?_,
      fun t ht y hy => hb t (htime ht) y hy, ?_⟩
    · intro y hy
      exact (hcont y (hball (closedBall_subset_ball (half_lt_self ha) hy))).mono htime
    · change L * max (2 * T - 0) (0 - -(2 * T)) ≤ a / 2 - a / 4
      simp only [sub_zero, zero_sub, neg_neg, max_self]
      have hTs : T ≤ a / (8 * L) := min_le_right _ _
      have hm := (le_div_iff₀ (show 0 < 8 * L by positivity)).mp hTs
      nlinarith
  have hex (b : E) (hb : b ∈ closedBall x (a / 4)) := FunSpace.exists_isFixedPt_next hpl hb
  choose β hβ using hex
  let X : E → ℝ → E := fun b =>
    if hb : b ∈ closedBall x (a / 4) then (β b hb).compProj else fun _ => b
  have hd (b : E) (hb : b ∈ closedBall x (a / 4))
      (t : ℝ) (ht : t ∈ Icc (-(2 * T)) (2 * T)) :
      HasDerivWithinAt (β b hb).compProj (F t ((β b hb).compProj t))
        (Icc (-(2 * T)) (2 * T)) t := by
    apply hasDerivWithinAt_picard_Icc t₀.property hpl.continuousOn_uncurry
      (β b hb).continuous_compProj.continuousOn
      (fun _ _ => (β b hb).compProj_mem_closedBall hpl.mul_max_le) b ht |>.congr_of_mem _ ht
    intro t' ht'
    nth_rw 1 [← hβ b hb]
    rw [FunSpace.compProj_of_mem ht']
    exact FunSpace.next_apply hpl hb (β b hb) (t := ⟨t', ht'⟩)
  refine ⟨a, ha, hball, T, hT, hTmax, X, ?_⟩
  constructor
  · intro b hb
    have hbc : b ∈ closedBall x (a / 4) := ball_subset_closedBall hb
    change (if hb : b ∈ closedBall x (a / 4) then (β b hb).compProj else fun _ => b) 0 = b
    rw [dif_pos hbc]
    change (β b hbc).compProj (t₀ : ℝ) = b
    rw [FunSpace.compProj_val, ← hβ b hbc]
    exact FunSpace.next_apply₀ hpl hbc (β b hbc)
  · intro b hb
    have hbc : b ∈ closedBall x (a / 4) := ball_subset_closedBall hb
    have he : X b = (β b hbc).compProj := dif_pos hbc
    rw [he]
    exact (β b hbc).continuous_compProj.continuousOn
  · intro b hb t ht
    have hbc : b ∈ closedBall x (a / 4) := ball_subset_closedBall hb
    have he : X b = (β b hbc).compProj := dif_pos hbc
    rw [he]
    exact (hd b hbc t (by constructor <;> linarith [ht.1, ht.2])).hasDerivAt
      (Icc_mem_nhds (by linarith [ht.1]) (by linarith [ht.2]))
  · intro b hb t _
    have hbc : b ∈ closedBall x (a / 4) := ball_subset_closedBall hb
    have he : X b = (β b hbc).compProj := dif_pos hbc
    rw [he]
    exact closedBall_subset_ball (half_lt_self ha)
      ((β b hbc).compProj_mem_closedBall hpl.mul_max_le)

namespace IsNonautonomousBanachFlowOn

theorem dist_le {f : ℝ → E → E} {U V : Set E} {T : ℝ} {X : E → ℝ → E}
    (hX : IsNonautonomousBanachFlowOn f U V T X) {K : ℝ≥0}
    (hLip : ∀ t ∈ Icc (0 : ℝ) T, LipschitzOnWith K (f t) U)
    {b c : E} (hb : b ∈ V) (hc : c ∈ V) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    dist (X b t) (X c t) ≤ dist b c * Real.exp ((K : ℝ) * t) := by
  have hd := dist_le_of_trajectories_ODE_of_mem
    (v := f) (s := fun _ : ℝ => U) (K := K) (fun t ht => hLip t ⟨ht.1, ht.2.le⟩)
    (hX.continuous b hb)
    (fun u hu => (hX.hasDerivAt b hb u ⟨hu.1, hu.2.le⟩).hasDerivWithinAt)
    (fun u hu => hX.mem b hb u ⟨hu.1, hu.2.le⟩)
    (hX.continuous c hc)
    (fun u hu => (hX.hasDerivAt c hc u ⟨hu.1, hu.2.le⟩).hasDerivWithinAt)
    (fun u hu => hX.mem c hc u ⟨hu.1, hu.2.le⟩)
    (δ := dist b c) (by rw [hX.initial b hb, hX.initial c hc]) t ht
  simpa only [sub_zero] using hd

end IsNonautonomousBanachFlowOn

end Euler2D

end
