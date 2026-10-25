module

public import Mathlib

/-! The genuine nonlinear remainder of a C¹ local map has an
arbitrarily small Lipschitz constant on a sufficiently small closed ball.
This is derived from the actual Fréchet derivative and its continuity. -/

@[expose] public section

set_option maxHeartbeats 1000000

noncomputable section

open Set Filter Topology Metric
open scoped ContDiff

namespace Euler2D

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]

def banachLocalRemainder (f : E → F) (x : E) : F := f x - fderiv ℝ f 0 x

theorem hasFDerivAt_banachLocalRemainder_zero {f : E → F}
    (hf : DifferentiableAt ℝ f 0) :
    HasFDerivAt (banachLocalRemainder f) (0 : E →L[ℝ] F) (0 : E) := by
  unfold banachLocalRemainder
  simpa only [sub_self, banachLocalRemainder, Pi.sub_def] using
    hf.hasFDerivAt.sub (fderiv ℝ f 0).hasFDerivAt

theorem banachLocalRemainder_zero {f : E → F} (hf : f 0 = 0) : banachLocalRemainder f 0 = 0 := by
  rw [banachLocalRemainder, hf, map_zero, sub_self]

theorem exists_closedBall_lipschitz_banachLocalRemainder {f : E → F}
    (hf : ContDiffAt ℝ 1 f 0) {ε : ℝ} (hε : 0 < ε) :
    ∃ r > 0, ∀ x ∈ closedBall (0 : E) r, ∀ y ∈ closedBall (0 : E) r,
      ‖banachLocalRemainder f x - banachLocalRemainder f y‖ ≤ ε * ‖x - y‖ := by
  let R := banachLocalRemainder f
  have hR : ContDiffAt ℝ 1 R 0 := hf.sub (fderiv ℝ f 0).contDiff.contDiffAt
  have hd : HasFDerivAt R (0 : E →L[ℝ] F) (0 : E) :=
    hasFDerivAt_banachLocalRemainder_zero (hf.differentiableAt (by norm_num))
  have hn : ContinuousAt (fun x : E => ‖fderiv ℝ R x‖) 0 :=
    (hR.continuousAt_fderiv (by norm_num)).norm
  have hsmall : ∀ᶠ x : E in 𝓝 0, ‖fderiv ℝ R x‖ < ε :=
    hn.eventually (eventually_lt_nhds (by
      change ‖fderiv ℝ R 0‖ < ε
      rw [hd.fderiv, norm_zero]
      exact hε))
  have hdiff : ∀ᶠ x : E in 𝓝 0, DifferentiableAt ℝ R x :=
    (hR.eventually (by norm_num)).mono (fun x hx => hx.differentiableAt (by norm_num))
  obtain ⟨r, hr, hb⟩ := Metric.eventually_nhds_iff.mp (hsmall.and hdiff)
  refine ⟨r / 2, half_pos hr, ?_⟩
  have hsub : closedBall (0 : E) (r / 2) ⊆ ball 0 r := closedBall_subset_ball (by linarith)
  intro x hx y hy
  exact (convex_closedBall (0 : E) (r / 2)).norm_image_sub_le_of_norm_fderiv_le
    (fun z hz => (hb (hsub hz)).2)
    (fun z hz => (hb (hsub hz)).1.le) hy hx

theorem exists_closedBall_banachLocalRemainder_bounds {f : E → F}
    (hf : ContDiffAt ℝ 1 f 0) (hzero : f 0 = 0) {ε : ℝ} (hε : 0 < ε) :
    ∃ r > 0,
      (∀ x ∈ closedBall (0 : E) r, ‖banachLocalRemainder f x‖ ≤ ε * ‖x‖) ∧
      ∀ x ∈ closedBall (0 : E) r, ∀ y ∈ closedBall (0 : E) r,
        ‖banachLocalRemainder f x - banachLocalRemainder f y‖ ≤ ε * ‖x - y‖ := by
  obtain ⟨r, hr, hLip⟩ := exists_closedBall_lipschitz_banachLocalRemainder hf hε
  refine ⟨r, hr, ?_, hLip⟩
  intro x hx
  have h := hLip x hx 0 (mem_closedBall_self hr.le)
  simpa only [banachLocalRemainder_zero hzero, sub_zero] using h

end Euler2D

end
