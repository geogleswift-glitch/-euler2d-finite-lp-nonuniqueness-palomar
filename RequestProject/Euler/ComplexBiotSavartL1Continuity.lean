module

public import RequestProject.Euler.PlanarBiotSavartL1Stability

/-! The original complex singular velocity is jointly continuous under
actual source L1 convergence and a common pointwise amplitude bound. -/

@[expose] public section

set_option maxHeartbeats 2500000

noncomputable section

open Set Filter Topology MeasureTheory

namespace Euler2D

theorem tendsto_velocityC_apply_of_L1
    {α : Type*} {l : Filter α} {w : α → ℂ → ℝ} {w₀ : ℂ → ℝ} {M : ℝ}
    (hw : ∀ a, Integrable (w a)) (hw₀ : Integrable w₀)
    (hM : ∀ a z, ‖w a z‖ ≤ M) (hM₀ : ∀ z, ‖w₀ z‖ ≤ M)
    (hL : Tendsto (fun a => ∫ z : ℂ, |w a z - w₀ z|) l (𝓝 0))
    {x : α → ℂ} {x₀ : ℂ} (hx : Tendsto x l (𝓝 x₀)) :
    Tendsto (fun a => velocityC (w a) (x a)) l (𝓝 (velocityC w₀ x₀)) := by
  have hwr (a : α) : Integrable (fun y : R2 => w a (complexPhysicalPlane.symm y)) :=
    complexPhysicalPlane.symm.measurePreserving.integrable_comp_of_integrable (hw a)
  have hw₀r : Integrable (fun y : R2 => w₀ (complexPhysicalPlane.symm y)) :=
    complexPhysicalPlane.symm.measurePreserving.integrable_comp_of_integrable hw₀
  have he (a : α) : (∫ y : R2, ‖w a (complexPhysicalPlane.symm y) -
      w₀ (complexPhysicalPlane.symm y)‖) = ∫ z : ℂ, |w a z - w₀ z| := by
    simpa only [Real.norm_eq_abs] using
      complexPhysicalPlane.symm.measurePreserving.integral_comp
        complexPhysicalPlane.symm.toHomeomorph.measurableEmbedding (fun z : ℂ => ‖w a z - w₀ z‖)
  have hLr : Tendsto (fun a => ∫ y : R2, ‖w a (complexPhysicalPlane.symm y) -
      w₀ (complexPhysicalPlane.symm y)‖) l (𝓝 0) := by
    simpa only [he] using hL
  have hreal := tendsto_planarBiotSavart_apply_of_L1 hwr hw₀r
    (fun a y => hM a (complexPhysicalPlane.symm y))
    (fun y => hM₀ (complexPhysicalPlane.symm y)) hLr
    ((complexPhysicalPlane.continuous.tendsto x₀).comp hx)
  have hc := (complexPhysicalPlane.symm.continuous.tendsto
    (planarKernelVelocity kernelK (fun y : R2 => w₀ (complexPhysicalPlane.symm y))
      (complexPhysicalPlane x₀))).comp hreal
  simpa only [Function.comp_def, ← complexPhysicalPlane_velocityC,
    LinearIsometryEquiv.symm_apply_apply] using hc

end Euler2D

end
