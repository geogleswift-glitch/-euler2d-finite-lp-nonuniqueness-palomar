module

public import RequestProject.Euler.BanachCompactLipschitzNeighborhood

/-! A genuine uniform quadratic Taylor estimate on a compact
reference set in an arbitrary Banach space. The actual first derivative
is Lipschitz on a proved open neighborhood of that compact set. -/

@[expose] public section

set_option maxHeartbeats 1500000

noncomputable section

open Set Filter Topology Metric
open scoped ContDiff NNReal

namespace Euler2D

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem exists_uniform_quadratic_taylor_on_compact
    {f : E → F} {U C : Set E} (hU : IsOpen U) (hf : ContDiffOn ℝ 2 f U)
    (hC : IsCompact C) (hCU : C ⊆ U) :
    ∃ K : ℝ≥0, ∃ r > 0, ∀ x ∈ C, ∀ d : E, ‖d‖ ≤ r →
      x + d ∈ U ∧ ‖f (x + d) - f x - fderiv ℝ f x d‖ ≤ (K : ℝ) * ‖d‖ ^ 2 := by
  let g := fderiv ℝ f
  have hg : ContDiffOn ℝ 1 g U := hf.fderiv_of_isOpen hU (by norm_num)
  obtain ⟨W, hW, hCW, hWU, K, hLip⟩ :=
    exists_lipschitz_open_neighborhood_of_compact hU hg hC hCU
  obtain ⟨r, hr, hthick⟩ := hC.exists_cthickening_subset_open hW hCW
  refine ⟨K, r, hr, ?_⟩
  intro x hx d hd
  have hBW : closedBall x ‖d‖ ⊆ W := fun y hy =>
    hthick (closedBall_subset_cthickening hx r (closedBall_subset_closedBall hd hy))
  have hxB : x ∈ closedBall x ‖d‖ := mem_closedBall_self (norm_nonneg d)
  have htip : x + d ∈ closedBall x ‖d‖ := by
    simp only [mem_closedBall_iff_norm, add_sub_cancel_left, le_refl]
  let R : E → F := fun y => f y - g x y
  have hgd (y : E) (hy : y ∈ closedBall x ‖d‖) :
      HasFDerivWithinAt R (g y - g x) (closedBall x ‖d‖) y := by
    have hyU := hWU (hBW hy)
    have hfy : DifferentiableAt ℝ f y :=
      ((hf y hyU).contDiffAt (hU.mem_nhds hyU)).differentiableAt (by norm_num)
    exact (hfy.hasFDerivAt.sub (g x).hasFDerivAt).hasFDerivWithinAt
  have hbound (y : E) (hy : y ∈ closedBall x ‖d‖) : ‖g y - g x‖ ≤ (K : ℝ) * ‖d‖ := by
    have he := hLip.dist_le_mul y (hBW hy) x (hBW hxB)
    rw [dist_eq_norm] at he
    exact he.trans (mul_le_mul_of_nonneg_left (mem_closedBall.mp hy) K.coe_nonneg)
  have hm := Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le hgd hbound
    (convex_closedBall x ‖d‖) hxB htip
  have he : R (x + d) - R x = f (x + d) - f x - g x d := by
    simp only [R, map_add]
    abel
  refine ⟨hWU (hBW htip), ?_⟩
  simpa only [he, add_sub_cancel_left, pow_two, mul_assoc] using hm

end Euler2D

end
