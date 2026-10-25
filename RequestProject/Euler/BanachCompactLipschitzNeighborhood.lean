module

public import RequestProject.Euler.BanachFlowTaylor
public import Mathlib.Topology.MetricSpace.Thickening

/-! An open C¹ field admits a genuinely Lipschitz open neighborhood of
each compact subset. Neither compact Banach balls nor bump functions are used. -/

@[expose] public section

noncomputable section

open Set Filter Topology Metric
open scoped NNReal ContDiff

namespace Euler2D

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem exists_lipschitz_open_neighborhood_of_compact
    {f : E → F} {U C : Set E} (hU : IsOpen U) (hf : ContDiffOn ℝ 1 f U)
    (hC : IsCompact C) (hCU : C ⊆ U) :
    ∃ W : Set E, IsOpen W ∧ C ⊆ W ∧ W ⊆ U ∧ ∃ K : ℝ≥0, LipschitzOnWith K f W := by
  have hD : ContinuousOn (fderiv ℝ f) U :=
    (hf.fderiv_of_isOpen hU (m := 0) (by norm_num)).continuousOn
  obtain ⟨M₀, hM₀⟩ := (hC.image_of_continuousOn (hD.mono hCU)).isBounded.exists_norm_le
  obtain ⟨N₀, hN₀⟩ := (hC.image_of_continuousOn (hf.continuousOn.mono hCU)).isBounded.exists_norm_le
  let M : ℝ := max M₀ 0 + 1
  let N : ℝ := max N₀ 0 + 1
  have hM : 0 < M := by dsimp only [M]; linarith [le_max_right M₀ 0]
  have hN : 0 < N := by dsimp only [N]; linarith [le_max_right N₀ 0]
  let V : Set E := (U ∩ (fun x => ‖fderiv ℝ f x‖) ⁻¹' Iio M) ∩
    (fun x => ‖f x‖) ⁻¹' Iio N
  have hV : IsOpen V :=
    (hf.continuousOn.norm.mono inter_subset_left).isOpen_inter_preimage
      (hD.norm.isOpen_inter_preimage hU isOpen_Iio) isOpen_Iio
  have hCV : C ⊆ V := by
    intro x hx
    refine ⟨⟨hCU hx, ?_⟩, ?_⟩
    · have hb := hM₀ (fderiv ℝ f x) (mem_image_of_mem _ hx)
      exact hb.trans_lt (by dsimp only [M]; linarith [le_max_left M₀ 0])
    · have hb := hN₀ (f x) (mem_image_of_mem _ hx)
      exact hb.trans_lt (by dsimp only [N]; linarith [le_max_left N₀ 0])
  obtain ⟨δ, hδ, hδV⟩ := hC.exists_cthickening_subset_open hV hCV
  let W : Set E := thickening (δ / 4) C
  have hWV : W ⊆ V :=
    (thickening_subset_cthickening_of_le (by linarith : δ / 4 ≤ δ) C).trans hδV
  let K : ℝ≥0 := ⟨M + 4 * N / δ, by positivity⟩
  refine ⟨W, isOpen_thickening, self_subset_thickening (by positivity) C,
    fun x hx => (hWV hx).1.1, K, ?_⟩
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  by_cases hxy : dist x y ≤ δ / 2
  · obtain ⟨z, hz, hxz⟩ := mem_thickening_iff.mp hx
    have hxB : x ∈ closedBall z δ := mem_closedBall.mpr (by linarith)
    have hyB : y ∈ closedBall z δ := mem_closedBall.mpr (by
      have htri := dist_triangle y x z
      rw [dist_comm y x] at htri
      linarith)
    have hBU : closedBall z δ ⊆ U :=
      fun q hq => (hδV (closedBall_subset_cthickening hz δ hq)).1.1
    have hbound (q : E) (hq : q ∈ closedBall z δ) : ‖fderiv ℝ f q‖ ≤ M :=
      (hδV (closedBall_subset_cthickening hz δ hq)).1.2.le
    have hd (q : E) (hq : q ∈ closedBall z δ) : DifferentiableAt ℝ f q :=
      ((hf q (hBU hq)).contDiffAt (hU.mem_nhds (hBU hq))).differentiableAt (by norm_num)
    have hb := (convex_closedBall z δ).norm_image_sub_le_of_norm_fderiv_le
      hd hbound hyB hxB
    rw [← dist_eq_norm, ← dist_eq_norm] at hb
    exact hb.trans (mul_le_mul_of_nonneg_right (by
      change M ≤ M + 4 * N / δ
      exact le_add_of_nonneg_right (by positivity)) dist_nonneg)
  · have hb : dist (f x) (f y) ≤ 2 * N := by
      calc
        _ ≤ ‖f x‖ + ‖f y‖ := by simpa only [dist_eq_norm] using norm_sub_le (f x) (f y)
        _ ≤ 2 * N := by
          have hfx : ‖f x‖ < N := (hWV hx).2
          have hfy : ‖f y‖ < N := (hWV hy).2
          linarith
    have hxy' : δ / 2 ≤ dist x y := (lt_of_not_ge hxy).le
    apply hb.trans
    change 2 * N ≤ (M + 4 * N / δ) * dist x y
    have hquot : 2 * N ≤ (4 * N / δ) * dist x y := by
      have he : (4 * N / δ) * (δ / 2) = 2 * N := by field_simp; ring
      rw [← he]
      exact mul_le_mul_of_nonneg_left hxy' (by positivity)
    nlinarith [mul_nonneg hM.le (dist_nonneg (x := x) (y := y))]

end Euler2D

end
