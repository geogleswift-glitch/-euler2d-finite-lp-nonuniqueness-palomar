module

public import RequestProject.Euler.PlanarBiotSavartLogBounds

/-! Strong L1 stability of the actual singular planar Biot--Savart
integral under a common density bound, uniformly on the entire plane. -/

@[expose] public section

set_option maxHeartbeats 2200000

noncomputable section

open MeasureTheory Set Filter Topology

namespace Euler2D

theorem norm_planarBiotSavart_le_mass_amplitude {w : R2 → ℝ} {M : ℝ}
    (hw : Integrable w) (hM : ∀ y, ‖w y‖ ≤ M) (x : R2) :
    ‖planarKernelVelocity kernelK w x‖ ≤ 2 * Real.sqrt (∫ y, ‖w y‖) * Real.sqrt M := by
  let wc : ℂ → ℝ := fun z => w (complexPhysicalPlane z)
  have hwc : Integrable wc := complexPhysicalPlane.measurePreserving.integrable_comp_of_integrable hw
  have hMc (z : ℂ) : |wc z| ≤ M := by simpa only [Real.norm_eq_abs] using hM (complexPhysicalPlane z)
  have hAc : (∫ z, |wc z|) = ∫ y, ‖w y‖ := by
    simpa only [Real.norm_eq_abs] using complexPhysicalPlane.measurePreserving.integral_comp
      complexPhysicalPlane.toHomeomorph.measurableEmbedding (fun a : R2 => ‖w a‖)
  have he : planarKernelVelocity kernelK w x =
      complexPhysicalPlane (velocityC wc (complexPhysicalPlane.symm x)) := by
    simpa only [wc, LinearIsometryEquiv.apply_symm_apply] using (complexPhysicalPlane_velocityC wc x).symm
  rw [he, LinearIsometryEquiv.norm_map]
  simpa only [hAc] using velocity_mass_amplitude hwc hMc (complexPhysicalPlane.symm x)

theorem planarBiotSavart_sub {w f : R2 → ℝ} {M N : ℝ}
    (hw : Integrable w) (hf : Integrable f)
    (hM : ∀ y, ‖w y‖ ≤ M) (hN : ∀ y, ‖f y‖ ≤ N) (x : R2) :
    planarKernelVelocity kernelK (w - f) x =
      planarKernelVelocity kernelK w x - planarKernelVelocity kernelK f x := by
  unfold planarKernelVelocity
  rw [← integral_sub (integrable_planarBiotSavart_integrand hw hM x)
    (integrable_planarBiotSavart_integrand hf hN x)]
  apply integral_congr_ae
  exact ae_of_all _ (fun y => sub_smul (w y) (f y) (kernelK (x - y)))

theorem norm_planarBiotSavart_sub_le_L1 {w f : R2 → ℝ} {M : ℝ}
    (hw : Integrable w) (hf : Integrable f)
    (hM : ∀ y, ‖w y‖ ≤ M) (hN : ∀ y, ‖f y‖ ≤ M) (x : R2) :
    ‖planarKernelVelocity kernelK w x - planarKernelVelocity kernelK f x‖ ≤
      2 * Real.sqrt (∫ y, ‖w y - f y‖) * Real.sqrt (2 * M) := by
  rw [← planarBiotSavart_sub hw hf hM hN]
  apply norm_planarBiotSavart_le_mass_amplitude (hw.sub hf)
  intro y
  exact (norm_sub_le _ _).trans ((add_le_add (hM y) (hN y)).trans_eq (by ring))

theorem tendstoUniformly_planarBiotSavart_of_L1
    {α : Type*} {l : Filter α} {w : α → R2 → ℝ} {w₀ : R2 → ℝ} {M : ℝ}
    (hw : ∀ a, Integrable (w a)) (hw₀ : Integrable w₀)
    (hM : ∀ a y, ‖w a y‖ ≤ M) (hM₀ : ∀ y, ‖w₀ y‖ ≤ M)
    (hL : Tendsto (fun a => ∫ y, ‖w a y - w₀ y‖) l (𝓝 (0 : ℝ))) :
    TendstoUniformly (fun a => planarKernelVelocity kernelK (w a))
      (planarKernelVelocity kernelK w₀) l := by
  have hb : Tendsto (fun a => 2 * Real.sqrt (∫ y, ‖w a y - w₀ y‖) * Real.sqrt (2 * M))
      l (𝓝 (0 : ℝ)) := by
    simpa only [Real.sqrt_zero, mul_zero, zero_mul] using
      (((Real.continuous_sqrt.tendsto 0).comp hL).const_mul 2).mul_const (Real.sqrt (2 * M))
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  filter_upwards [hb.eventually (eventually_lt_nhds hε)] with a ha x
  rw [dist_eq_norm, norm_sub_rev]
  exact (norm_planarBiotSavart_sub_le_L1 (hw a) hw₀ (hM a) hM₀ x).trans_lt ha

theorem tendsto_planarBiotSavart_apply_of_L1
    {α : Type*} {l : Filter α} {w : α → R2 → ℝ} {w₀ : R2 → ℝ} {M : ℝ}
    (hw : ∀ a, Integrable (w a)) (hw₀ : Integrable w₀)
    (hM : ∀ a y, ‖w a y‖ ≤ M) (hM₀ : ∀ y, ‖w₀ y‖ ≤ M)
    (hL : Tendsto (fun a => ∫ y, ‖w a y - w₀ y‖) l (𝓝 (0 : ℝ)))
    {x : α → R2} {x₀ : R2} (hx : Tendsto x l (𝓝 x₀)) :
    Tendsto (fun a => planarKernelVelocity kernelK (w a) (x a)) l
      (𝓝 (planarKernelVelocity kernelK w₀ x₀)) := by
  have hb : Tendsto (fun a => 2 * Real.sqrt (∫ y, ‖w a y - w₀ y‖) * Real.sqrt (2 * M))
      l (𝓝 (0 : ℝ)) := by
    simpa only [Real.sqrt_zero, mul_zero, zero_mul] using
      (((Real.continuous_sqrt.tendsto 0).comp hL).const_mul 2).mul_const (Real.sqrt (2 * M))
  have herr : Tendsto (fun a => planarKernelVelocity kernelK (w a) (x a) -
      planarKernelVelocity kernelK w₀ (x a)) l (𝓝 (0 : R2)) :=
    squeeze_zero_norm (fun a => norm_planarBiotSavart_sub_le_L1 (hw a) hw₀ (hM a) hM₀ (x a)) hb
  have href := ((uniformContinuous_planarBiotSavart hw₀ hM₀).continuous.tendsto x₀).comp hx
  simpa only [Function.comp_apply, sub_add_cancel, zero_add] using herr.add href

end Euler2D

end
