module

public import RequestProject.Euler.SmoothFlowEstimates
public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.Topology.UniformSpace.HeineCantor

/-!
# Uniform spatial Taylor remainders along a compact trajectory
-/

@[expose] public section

noncomputable section

open Set Filter Topology Metric
open scoped ContDiff

namespace Euler2D

lemma continuous_spatialVelocityDerivative {v : ℝ → R2 → R2}
    (hv : ContDiff ℝ 1 (Function.uncurry v)) :
    Continuous (fun p : ℝ × R2 => fderiv ℝ (v p.1) p.2) := by
  exact Continuous.fderiv_one
    (hv.comp (contDiff_fst.fst.prodMk contDiff_snd)) continuous_snd

/-- The first-order remainder is uniformly small at all times in a compact
time interval, for a continuous reference trajectory. -/
theorem uniform_spatialTaylor_remainder {v : ℝ → R2 → R2}
    (hv : ContDiff ℝ 1 (Function.uncurry v)) {x : ℝ → R2} (hx : Continuous x)
    {T : ℝ} (hT : 0 ≤ T) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ t ∈ Icc (0 : ℝ) T, ∀ d : R2, ‖d‖ ≤ δ →
      ‖v t (x t + d) - v t (x t) - fderiv ℝ (v t) (x t) d‖ ≤ ε * ‖d‖ := by
  let D : ℝ × R2 → R2 →L[ℝ] R2 := fun p => fderiv ℝ (v p.1) p.2
  have hDc : Continuous D := continuous_spatialVelocityDerivative hv
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hx.continuousOn
    (s := Icc (0 : ℝ) T)
  have hC0 : 0 ≤ C := (norm_nonneg (x 0)).trans (hC 0 ⟨le_rfl, hT⟩)
  have hcompact : IsCompact (Icc (0 : ℝ) T ×ˢ closedBall (0 : R2) (C + 1)) :=
    isCompact_Icc.prod (isCompact_closedBall _ _)
  obtain ⟨η, hη, hηD⟩ := Metric.uniformContinuousOn_iff.mp
    (hcompact.uniformContinuousOn_of_continuous hDc.continuousOn) ε hε
  let δ : ℝ := min 1 (η / 2)
  have hδ : 0 < δ := lt_min (by norm_num) (half_pos hη)
  have hδ1 : δ ≤ 1 := min_le_left _ _
  have hδη : δ < η := (min_le_right _ _).trans_lt (half_lt_self hη)
  refine ⟨δ, hδ, ?_⟩
  intro t ht d hd
  have hbase : (t, x t) ∈ Icc (0 : ℝ) T ×ˢ closedBall (0 : R2) (C + 1) :=
    ⟨ht, by simpa only [mem_closedBall, dist_zero_right] using (hC t ht).trans (by linarith : C ≤ C + 1)⟩
  have hnear (y : R2) (hy : y ∈ closedBall (x t) δ) :
      ‖D (t, y) - D (t, x t)‖ ≤ ε := by
    have hnorm : ‖y‖ ≤ C + 1 := by
      calc
        ‖y‖ ≤ ‖y - x t‖ + ‖x t‖ := by simpa only [add_comm] using norm_le_insert' y (x t)
        _ ≤ δ + C := add_le_add (mem_closedBall_iff_norm.mp hy) (hC t ht)
        _ ≤ C + 1 := by linarith
    have hs : (t, y) ∈ Icc (0 : ℝ) T ×ˢ closedBall (0 : R2) (C + 1) :=
      ⟨ht, by simpa only [mem_closedBall, dist_zero_right] using hnorm⟩
    have hdist : dist (t, y) (t, x t) < η := by
      simpa only [Prod.dist_eq, dist_self, max_eq_right dist_nonneg] using
        (mem_closedBall.mp hy).trans_lt hδη
    simpa only [dist_eq_norm] using (hηD (t, y) hs (t, x t) hbase hdist).le
  let g : R2 → R2 := fun y => v t y - D (t, x t) y
  have hvg : Differentiable ℝ (v t) :=
    (hv.comp (contDiff_const.prodMk contDiff_id)).differentiable one_ne_zero
  have hgd (y : R2) : HasFDerivAt g (D (t, y) - D (t, x t)) y :=
    (hvg y).hasFDerivAt.sub (D (t, x t)).hasFDerivAt
  have hm := Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le
    (fun y hy => (hgd y).hasFDerivWithinAt) hnear (convex_closedBall (x t) δ)
    (mem_closedBall_self hδ.le) (show x t + d ∈ closedBall (x t) δ by
      simpa only [mem_closedBall_iff_norm, add_sub_cancel_left] using hd)
  have heq : g (x t + d) - g (x t) =
      v t (x t + d) - v t (x t) - D (t, x t) d := by
    simp only [g, map_add]
    abel
  simpa only [heq, add_sub_cancel_left] using hm

end Euler2D

end
