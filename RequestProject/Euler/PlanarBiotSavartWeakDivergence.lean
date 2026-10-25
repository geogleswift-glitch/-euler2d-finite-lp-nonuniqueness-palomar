module

public import RequestProject.Euler.PlanarBiotSavartIntegrability
public import RequestProject.Euler.PlanarWeakDivergenceLimit

/-! The original singular planar Biot--Savart velocity is genuinely
distributionally incompressible for every bounded integrable vorticity.
The actual expanding integrable kernels and their actual uniform
velocity limit supply the proof. -/

@[expose] public section

set_option maxHeartbeats 2000000

noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal ContDiff

namespace Euler2D

theorem aestronglyMeasurable_planarBiotSavart {w : R2 → ℝ} {M : ℝ}
    (hw : Integrable w) (hM : ∀ y, ‖w y‖ ≤ M) :
    AEStronglyMeasurable (planarKernelVelocity kernelK w) volume := by
  have hn (n : ℕ) : AEStronglyMeasurable (planarKernelVelocity (planarExpandingKernelCutoff n) w) volume := by
    have hbase : AEStronglyMeasurable
        (fun p : R2 × R2 => w p.2 • planarExpandingKernelCutoff n (p.1 - p.2)) (volume.prod volume) :=
      hw.aestronglyMeasurable.convolution_integrand (ContinuousLinearMap.lsmul ℝ ℝ)
        (integrable_planarExpandingKernelCutoff n).aestronglyMeasurable
    exact hbase.integral_prod_right'
  exact aestronglyMeasurable_of_tendsto_ae atTop hn (ae_of_all _ (fun x =>
    (tendstoUniformly_planarBiotSavart_cutoff_velocity hw hM).tendsto_at x))

theorem isPlanarWeaklyDivergenceFree_planarBiotSavart {w : R2 → ℝ} {M : ℝ}
    (hw : Integrable w) (hM : ∀ y, ‖w y‖ ≤ M) :
    IsPlanarWeaklyDivergenceFree (planarKernelVelocity kernelK w) := by
  have hn (n : ℕ) : AEStronglyMeasurable (planarKernelVelocity (planarExpandingKernelCutoff n) w) volume := by
    have hbase : AEStronglyMeasurable
        (fun p : R2 × R2 => w p.2 • planarExpandingKernelCutoff n (p.1 - p.2)) (volume.prod volume) :=
      hw.aestronglyMeasurable.convolution_integrand (ContinuousLinearMap.lsmul ℝ ℝ)
        (integrable_planarExpandingKernelCutoff n).aestronglyMeasurable
    exact hbase.integral_prod_right'
  exact isPlanarWeaklyDivergenceFree_of_bounded_pointwise_limit hn
    (aestronglyMeasurable_planarBiotSavart hw hM)
    (fun n x => norm_planarKernelVelocity_le_planarBiotSavartBound hw hM
      (norm_planarExpandingKernelCutoff_le n) x)
    (fun x => (tendstoUniformly_planarBiotSavart_cutoff_velocity hw hM).tendsto_at x)
    (fun n => isPlanarWeaklyDivergenceFree_planarKernelVelocity (integrable_planarExpandingKernelCutoff n)
      (planarExpandingKernelCutoff_weakly_divergenceFree n) hw hM)

end Euler2D

end
