module

public import RequestProject.Euler.ContourBanachCompactSmoothIntegral
public import Mathlib.Analysis.Calculus.MeanValue

/-! Genuine uniform Taylor estimates along a compact trajectory in an
arbitrary normed space. Compactness is used only for the trajectory
parameter, through a tube neighborhood; no finite-dimensional balls or
smooth bump functions are used. -/

@[expose] public section

noncomputable section

open Set Filter Topology Metric
open scoped ContDiff

namespace Euler2D

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem banachFlow_uniform_derivative_neighborhood
    {U : Set E} (hU : IsOpen U) {f : E → F} (hf : ContDiffOn ℝ 1 f U)
    {S : Set ℝ} (hS : IsCompact S) {x : ℝ → E} (hx : Continuous x)
    (hpath : ∀ t ∈ S, x t ∈ U) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ t ∈ S, ∀ y ∈ closedBall (x t) δ,
      y ∈ U ∧ ‖fderiv ℝ f y - fderiv ℝ f (x t)‖ ≤ ε := by
  letI : CompactSpace S := isCompact_iff_compactSpace.mp hS
  let D : E → E →L[ℝ] F := fderiv ℝ f
  have hD : ContinuousOn D U := (hf.fderiv_of_isOpen hU (m := 0) (by norm_num)).continuousOn
  let G : E × S → E →L[ℝ] F := fun q => D (x q.2 + q.1) - D (x q.2)
  let A : Set (E × S) := {q | x q.2 + q.1 ∈ U ∧ ‖G q‖ < ε}
  have hnhds (t : S) : A ∈ 𝓝 ((0 : E), t) := by
    have hxt := hpath t t.property
    have hDa : ContinuousAt D (x t) := (hD (x t) hxt).continuousAt (hU.mem_nhds hxt)
    have hxp : Continuous (fun q : E × S => x q.2 + q.1) :=
      (hx.comp (continuous_subtype_val.comp continuous_snd)).add continuous_fst
    have hxb : Continuous (fun q : E × S => x q.2) :=
      hx.comp (continuous_subtype_val.comp continuous_snd)
    have hDa' : ContinuousAt D (x t + 0) := by simpa only [add_zero] using hDa
    have hGa : ContinuousAt G ((0 : E), t) :=
      (hDa'.comp (f := fun q : E × S => x q.2 + q.1) hxp.continuousAt).sub
        (hDa.comp (f := fun q : E × S => x q.2) hxb.continuousAt)
    have hmem : ∀ᶠ q : E × S in 𝓝 ((0 : E), t), x q.2 + q.1 ∈ U :=
      hxp.continuousAt (by simpa only [add_zero] using hU.mem_nhds hxt)
    have hsmall : ∀ᶠ q : E × S in 𝓝 ((0 : E), t), ‖G q‖ < ε :=
      hGa.norm (Iio_mem_nhds (by simpa only [G, add_zero, sub_self, norm_zero] using hε))
    exact hmem.and hsmall
  have hin : ({(0 : E)} ×ˢ (univ : Set S)) ⊆ interior A := by
    intro q hq
    have hz : q.1 = 0 := hq.1
    change (q.1, q.2) ∈ interior A
    rw [hz]
    exact mem_interior_iff_mem_nhds.mpr (hnhds q.2)
  obtain ⟨V, W, hV, _, h0, hW, hVW⟩ :=
    generalized_tube_lemma isCompact_singleton isCompact_univ isOpen_interior hin
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (hV.mem_nhds (h0 (mem_singleton _)))
  refine ⟨r / 2, half_pos hr, ?_⟩
  intro t ht y hy
  let d := y - x t
  have hd : d ∈ ball (0 : E) r := by
    rw [mem_ball, dist_zero_right]
    exact (mem_closedBall_iff_norm.mp hy).trans_lt (half_lt_self hr)
  have hA : (d, (⟨t, ht⟩ : S)) ∈ A :=
    interior_subset (hVW ⟨hball hd, hW (mem_univ _)⟩)
  have he : x t + d = y := by dsimp only [d]; abel
  change x t + d ∈ U ∧ ‖D (x t + d) - D (x t)‖ < ε at hA
  rw [he] at hA
  exact ⟨hA.1, hA.2.le⟩

theorem banachFlow_uniform_taylor_remainder
    {U : Set E} (hU : IsOpen U) {f : E → F} (hf : ContDiffOn ℝ 1 f U)
    {S : Set ℝ} (hS : IsCompact S) {x : ℝ → E} (hx : Continuous x)
    (hpath : ∀ t ∈ S, x t ∈ U) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ t ∈ S, ∀ d : E, ‖d‖ ≤ δ →
      x t + d ∈ U ∧ ‖f (x t + d) - f (x t) - fderiv ℝ f (x t) d‖ ≤ ε * ‖d‖ := by
  obtain ⟨δ, hδ, hnear⟩ := banachFlow_uniform_derivative_neighborhood hU hf hS hx hpath hε
  refine ⟨δ, hδ, ?_⟩
  intro t ht d hd
  have hbase : x t ∈ closedBall (x t) δ := mem_closedBall_self hδ.le
  have htip : x t + d ∈ closedBall (x t) δ := by
    simpa only [mem_closedBall_iff_norm, add_sub_cancel_left] using hd
  let D : E → E →L[ℝ] F := fderiv ℝ f
  let g : E → F := fun y => f y - D (x t) y
  have hgd (y : E) (hy : y ∈ closedBall (x t) δ) :
      HasFDerivWithinAt g (D y - D (x t)) (closedBall (x t) δ) y := by
    have hyU := (hnear t ht y hy).1
    have hfy : DifferentiableAt ℝ f y :=
      ((hf y hyU).contDiffAt (hU.mem_nhds hyU)).differentiableAt (by norm_num)
    exact (hfy.hasFDerivAt.sub (D (x t)).hasFDerivAt).hasFDerivWithinAt
  have hm := Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le hgd
    (fun y hy => (hnear t ht y hy).2) (convex_closedBall (x t) δ) hbase htip
  have he : g (x t + d) - g (x t) = f (x t + d) - f (x t) - D (x t) d := by
    simp only [g, map_add]
    abel
  refine ⟨(hnear t ht (x t + d) htip).1, ?_⟩
  simpa only [he, add_sub_cancel_left] using hm

end Euler2D

end
