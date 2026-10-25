module

public import RequestProject.Euler.BanachQuadraticRemainder

/-! A C² map's actual nonlinear remainder has a quadratic two-point
bound. This controls differences without assuming a smooth graph. -/

@[expose] public section

set_option maxHeartbeats 2000000

noncomputable section

open Set Filter Topology Metric
open scoped ContDiff

namespace Euler2D

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup H] [NormedSpace ℝ H]

theorem exists_banachLocalRemainder_quadratic_difference_bound {f : E → H}
    (hf : ContDiffAt ℝ 2 f 0) :
    ∃ C > 0, ∃ r > 0, ∀ x ∈ closedBall (0 : E) r, ∀ y ∈ closedBall (0 : E) r,
      ‖banachLocalRemainder f x - banachLocalRemainder f y‖ ≤
        C * (‖x‖ + ‖y‖) * ‖x - y‖ := by
  let R := banachLocalRemainder f
  let g := fderiv ℝ R
  have hR : ContDiffAt ℝ 2 R 0 := hf.sub (fderiv ℝ f 0).contDiff.contDiffAt
  have hg : ContDiffAt ℝ 1 g 0 := hR.fderiv_right (by norm_num)
  have hg0 : g 0 = 0 :=
    (hasFDerivAt_banachLocalRemainder_zero (hf.differentiableAt (by norm_num))).fderiv
  obtain ⟨C, hC, hbound⟩ := (hg.differentiableAt (by norm_num)).isBigO_sub.exists_pos
  have hb : ∀ᶠ z : E in 𝓝 0, ‖g z‖ ≤ C * ‖z‖ := by
    simpa only [hg0, sub_zero] using hbound.bound
  have hd : ∀ᶠ z : E in 𝓝 0, DifferentiableAt ℝ R z :=
    (hR.eventually (by norm_num)).mono (fun _ hz => hz.differentiableAt (by norm_num))
  obtain ⟨s, hs, hlocal⟩ := Metric.eventually_nhds_iff.mp (hb.and hd)
  refine ⟨C, hC, s / 2, half_pos hs, ?_⟩
  intro x hx y hy
  have hxr : ‖x‖ ≤ s / 2 := by simpa only [mem_closedBall, dist_zero_right] using hx
  have hyr : ‖y‖ ≤ s / 2 := by simpa only [mem_closedBall, dist_zero_right] using hy
  let d := max ‖x‖ ‖y‖
  have hdr : d ≤ s / 2 := max_le hxr hyr
  have hds : d < s := lt_of_le_of_lt hdr (half_lt_self hs)
  have hinside : closedBall (0 : E) d ⊆ ball 0 s := closedBall_subset_ball hds
  have hderiv (z : E) (hz : z ∈ closedBall (0 : E) d) :
      ‖fderiv ℝ R z‖ ≤ C * (‖x‖ + ‖y‖) := by
    have hn : ‖z‖ ≤ d := by simpa only [mem_closedBall, dist_zero_right] using hz
    have hm : d ≤ ‖x‖ + ‖y‖ := max_le
      (le_add_of_nonneg_right (norm_nonneg y)) (le_add_of_nonneg_left (norm_nonneg x))
    exact (hlocal (hinside hz)).1.trans
      (mul_le_mul_of_nonneg_left (hn.trans hm) hC.le)
  have he := (convex_closedBall (0 : E) d).norm_image_sub_le_of_norm_fderiv_le
    (fun z hz => (hlocal (hinside hz)).2) hderiv
    (show y ∈ closedBall (0 : E) d by simpa only [mem_closedBall, dist_zero_right] using le_max_right ‖x‖ ‖y‖)
    (show x ∈ closedBall (0 : E) d by simpa only [mem_closedBall, dist_zero_right] using le_max_left ‖x‖ ‖y‖)
  exact he

end Euler2D

end
