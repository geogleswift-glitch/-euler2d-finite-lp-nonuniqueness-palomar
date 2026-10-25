module

public import RequestProject.Euler.ComplexPlanarBiotSavart

/-! Strong L1 continuity of the actual transported planar density.
The ambient measure is infinite planar volume. Compact-open
convergence of genuine continuous measure-preserving maps suffices. -/

@[expose] public section

set_option maxHeartbeats 2000000

noncomputable section

open MeasureTheory Set Filter Topology

namespace Euler2D

theorem ae_planarTransport_L1 {w : R2 → ℝ} (hw : Integrable w)
    (g : C(R2, R2)) (hgm : MeasurePreserving g volume volume) :
    Lp.compMeasurePreserving g hgm (hw.toL1 w) =ᵐ[volume] fun x => w (g x) :=
  (Lp.coeFn_compMeasurePreserving (hw.toL1 w) hgm).trans
    (hgm.quasiMeasurePreserving.ae_eq_comp hw.coeFn_toL1)

theorem planarTransport_L1_dist_eq_integral {w f : R2 → ℝ}
    (hw : Integrable w) (hf : Integrable f) (g h : C(R2, R2))
    (hgm : MeasurePreserving g volume volume) (hhm : MeasurePreserving h volume volume) :
    dist (Lp.compMeasurePreserving g hgm (hw.toL1 w))
      (Lp.compMeasurePreserving h hhm (hf.toL1 f)) =
      ∫ x, ‖w (g x) - f (h x)‖ := by
  rw [L1.dist_eq_integral_dist]
  apply integral_congr_ae
  filter_upwards [ae_planarTransport_L1 hw g hgm, ae_planarTransport_L1 hf h hhm] with x hx hy
  rw [hx, hy, dist_eq_norm]

theorem tendsto_integral_norm_planarTransport_sub
    {α : Type*} {l : Filter α} {g : α → C(R2, R2)} {g₀ : C(R2, R2)}
    {w : R2 → ℝ} (hw : Integrable w) (hg : Tendsto g l (𝓝 g₀))
    (hgm : ∀ a, MeasurePreserving (g a) volume volume)
    (hgm₀ : MeasurePreserving g₀ volume volume) :
    Tendsto (fun a => ∫ x, ‖w (g a x) - w (g₀ x)‖) l (𝓝 (0 : ℝ)) := by
  have hL : Tendsto (fun a => Lp.compMeasurePreserving (g a) (hgm a) (hw.toL1 w)) l
      (𝓝 (Lp.compMeasurePreserving g₀ hgm₀ (hw.toL1 w))) :=
    tendsto_const_nhds.compMeasurePreservingLp hg hgm hgm₀ (by simp)
  have hd := hL.dist (tendsto_const_nhds (x := Lp.compMeasurePreserving g₀ hgm₀ (hw.toL1 w)))
  simpa only [dist_self, planarTransport_L1_dist_eq_integral hw hw] using hd

theorem continuous_planarTransport_L1
    {Z : Type*} [TopologicalSpace Z] {g : Z → C(R2, R2)}
    {w : R2 → ℝ} (hw : Integrable w) (hg : Continuous g)
    (hgm : ∀ z, MeasurePreserving (g z) volume volume) :
    Continuous (fun z => Lp.compMeasurePreserving (g z) (hgm z) (hw.toL1 w)) :=
  continuous_const.compMeasurePreservingLp hg hgm (by simp)

theorem tendsto_integral_norm_planarTransport_time
    {Z : Type*} [TopologicalSpace Z] {g : Z → C(R2, R2)}
    {w : R2 → ℝ} (hw : Integrable w) (hg : Continuous g)
    (hgm : ∀ z, MeasurePreserving (g z) volume volume) (z : Z) :
    Tendsto (fun s => ∫ x, ‖w (g s x) - w (g z x)‖) (𝓝 z) (𝓝 (0 : ℝ)) :=
  tendsto_integral_norm_planarTransport_sub hw (hg.tendsto z) hgm (hgm z)

end Euler2D

end
