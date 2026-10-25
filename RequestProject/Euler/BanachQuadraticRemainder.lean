module

public import RequestProject.Euler.BanachLocalRemainder

/-! A true C² local return map has a quadratic nonlinear remainder
in the original Banach norm. The estimate follows from the derivative
of the actual remainder and the Banach mean-value inequality. -/

@[expose] public section

set_option maxHeartbeats 1500000

noncomputable section

open Set Filter Topology Metric
open scoped ContDiff

namespace Euler2D

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem exists_banachLocalRemainder_quadratic_bound {f : E → F}
    (hf : ContDiffAt ℝ 2 f 0) (hzero : f 0 = 0) :
    ∃ C > 0, ∃ r > 0, ∀ x ∈ closedBall (0 : E) r,
      ‖banachLocalRemainder f x‖ ≤ C * ‖x‖ ^ 2 := by
  let R := banachLocalRemainder f
  let g := fderiv ℝ R
  have hR : ContDiffAt ℝ 2 R 0 := hf.sub (fderiv ℝ f 0).contDiff.contDiffAt
  have hg : ContDiffAt ℝ 1 g 0 := hR.fderiv_right (by norm_num)
  have hgd : DifferentiableAt ℝ g 0 := hg.differentiableAt (by norm_num)
  have hg0 : g 0 = 0 :=
    (hasFDerivAt_banachLocalRemainder_zero (hf.differentiableAt (by norm_num))).fderiv
  obtain ⟨C, hC, hbound⟩ := hgd.isBigO_sub.exists_pos
  have hb : ∀ᶠ x : E in 𝓝 0, ‖g x‖ ≤ C * ‖x‖ := by
    simpa only [hg0, sub_zero] using hbound.bound
  have hd : ∀ᶠ x : E in 𝓝 0, DifferentiableAt ℝ R x :=
    (hR.eventually (by norm_num)).mono (fun _ hx => hx.differentiableAt (by norm_num))
  obtain ⟨s, hs, hlocal⟩ := Metric.eventually_nhds_iff.mp (hb.and hd)
  have hsub : closedBall (0 : E) (s / 2) ⊆ ball 0 s := closedBall_subset_ball (half_lt_self hs)
  refine ⟨C, hC, s / 2, half_pos hs, ?_⟩
  intro x hx
  have hxr : ‖x‖ ≤ s / 2 := by simpa only [mem_closedBall, dist_eq_norm, sub_zero] using hx
  have hinside : closedBall (0 : E) ‖x‖ ⊆ closedBall 0 (s / 2) := closedBall_subset_closedBall hxr
  have hderiv (z : E) (hz : z ∈ closedBall (0 : E) ‖x‖) :
      ‖fderiv ℝ R z‖ ≤ C * ‖x‖ := by
    have hn : ‖z‖ ≤ ‖x‖ := by simpa only [mem_closedBall, dist_eq_norm, sub_zero] using hz
    exact (hlocal (hsub (hinside hz))).1.trans (mul_le_mul_of_nonneg_left hn hC.le)
  have he := (convex_closedBall (0 : E) ‖x‖).norm_image_sub_le_of_norm_fderiv_le
    (fun z hz => (hlocal (hsub (hinside hz))).2) hderiv
    (mem_closedBall_self (norm_nonneg x))
    (show x ∈ closedBall (0 : E) ‖x‖ by simp only [mem_closedBall, dist_eq_norm, sub_zero, le_refl])
  have hR0 : R 0 = 0 := banachLocalRemainder_zero hzero
  simpa only [hR0, sub_zero, pow_two, mul_assoc] using he

end Euler2D

end
