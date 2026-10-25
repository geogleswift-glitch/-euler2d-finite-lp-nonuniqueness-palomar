module

public import RequestProject.Euler.NonautonomousBanachFlowExistence

/-! Uniform local Lipschitz control in the state and continuity in
time give joint continuity at the actual state. -/

@[expose] public section

noncomputable section

open Set Filter Topology
open scoped NNReal

namespace Euler2D

theorem continuousAt_timeState_of_lipschitzOn
    {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    {f : ℝ → X → Y} {U : Set X} {K : ℝ≥0} {t : ℝ} {x : X}
    (hU : U ∈ 𝓝 x) (hLip : ∀ s, LipschitzOnWith K (f s) U)
    (hc : ContinuousAt (fun s => f s x) t) :
    ContinuousAt (fun p : ℝ × X => f p.1 p.2) (t, x) := by
  have hx : x ∈ U := mem_of_mem_nhds hU
  have hmem : ∀ᶠ p : ℝ × X in 𝓝 (t, x), p.2 ∈ U :=
    continuous_snd.continuousAt.eventually hU
  have hbound : ∀ᶠ p : ℝ × X in 𝓝 (t, x),
      dist (f p.1 p.2) (f t x) ≤
        (K : ℝ) * dist p.2 x + dist (f p.1 x) (f t x) := by
    filter_upwards [hmem] with p hp
    exact (dist_triangle _ (f p.1 x) _).trans
      (add_le_add ((hLip p.1).dist_le_mul p.2 hp x hx) (le_refl _))
  have hfirst : ContinuousAt (fun p : ℝ × X => (K : ℝ) * dist p.2 x) (t, x) :=
    continuousAt_const.mul (continuous_snd.continuousAt.dist continuousAt_const)
  have hcenter : ContinuousAt (fun p : ℝ × X => f p.1 x) (t, x) :=
    by
      have hp : Tendsto (fun p : ℝ × X => p.1) (𝓝 (t, x)) (𝓝 t) :=
        continuous_fst.continuousAt
      exact hc.tendsto.comp hp
  have hsecond : ContinuousAt (fun p : ℝ × X => dist (f p.1 x) (f t x)) (t, x) :=
    hcenter.dist continuousAt_const
  have hlim : Tendsto (fun p : ℝ × X =>
      (K : ℝ) * dist p.2 x + dist (f p.1 x) (f t x)) (𝓝 (t, x)) (𝓝 0) := by
    simpa only [Pi.add_def, dist_self, mul_zero, add_zero] using (hfirst.add hsecond).tendsto
  exact tendsto_iff_dist_tendsto_zero.mpr
    (squeeze_zero' (Eventually.of_forall (fun _ => dist_nonneg)) hbound hlim)

end Euler2D

end
