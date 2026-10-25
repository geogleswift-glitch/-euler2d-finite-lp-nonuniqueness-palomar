module

public import RequestProject.Euler.PlanarBiotSavartAbsoluteBound

/-! Compact smoothing of the genuine singular kernel commutes
with its actual bounded-vorticity convolution. The real two-variable
absolute integral supplies the Fubini argument at every spatial point. -/

@[expose] public section

set_option maxHeartbeats 2500000

noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal ContDiff Convolution

namespace Euler2D

theorem integrable_planarBiotSavart_smoothing_pair
    {φ w : R2 → ℝ} {M : ℝ} (hφ : Integrable φ) (hw : Integrable w)
    (hM : ∀ y, ‖w y‖ ≤ M) (x : R2) :
    Integrable (fun p : R2 × R2 => φ p.1 • (w p.2 • kernelK (x - p.1 - p.2))) (volume.prod volume) := by
  let F : R2 → R2 → R2 := fun z y => φ z • (w y • kernelK (x - z - y))
  have hKmeas : Measurable (fun p : R2 × R2 => kernelK (x - p.1 - p.2)) :=
    measurable_kernelK.comp ((measurable_const.sub measurable_fst).sub measurable_snd)
  have hFmeas : AEStronglyMeasurable (Function.uncurry F) (volume.prod volume) :=
    hφ.aestronglyMeasurable.comp_fst.smul (hw.aestronglyMeasurable.comp_snd.smul hKmeas.aestronglyMeasurable)
  have hsection (z : R2) : Integrable (F z) :=
    (ContinuousLinearMap.lsmul ℝ ℝ (φ z) : R2 →L[ℝ] R2).integrable_comp
      (integrable_planarBiotSavart_integrand hw hM (x - z))
  have hI (z : R2) : (∫ y, ‖F z y‖) ≤ ‖φ z‖ * planarBiotSavartBound w M := by
    calc
      _ = ‖φ z‖ * (∫ y, ‖w y • kernelK ((x - z) - y)‖) := by
        simp only [F, norm_smul]
        rw [integral_const_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_left (integral_norm_planarBiotSavart_integrand_le hw hM (x - z)) (norm_nonneg _)
  have houter : Integrable (fun z => ∫ y, ‖F z y‖) := by
    apply (hφ.norm.mul_const (planarBiotSavartBound w M)).mono' hFmeas.norm.integral_prod_right'
    exact ae_of_all _ (fun z => by
      rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg (fun y => norm_nonneg (F z y)))]
      exact hI z)
  exact (integrable_prod_iff hFmeas).mpr ⟨ae_of_all _ hsection, houter⟩

theorem planarBiotSavart_smoothing_convolution
    {φ w : R2 → ℝ} {M : ℝ} (hφ : Integrable φ) (hw : Integrable w)
    (hM : ∀ y, ‖w y‖ ≤ M) (x : R2) :
    planarKernelVelocity (planarKernelVelocity kernelK φ) w x =
      planarKernelVelocity (planarKernelVelocity kernelK w) φ x := by
  let F : R2 → R2 → R2 := fun z y => φ z • (w y • kernelK (x - z - y))
  have hF : Integrable (Function.uncurry F) (volume.prod volume) :=
    integrable_planarBiotSavart_smoothing_pair hφ hw hM x
  calc
    _ = ∫ y, ∫ z, F z y := by
      unfold planarKernelVelocity
      apply integral_congr_ae
      exact ae_of_all _ (fun y => by
        dsimp only
        rw [← integral_smul]
        apply integral_congr_ae
        exact ae_of_all _ (fun z => by
          dsimp only [F]
          rw [show x - y - z = x - z - y by abel]
          exact smul_comm (w y) (φ z) (kernelK (x - z - y))))
    _ = ∫ z, ∫ y, F z y := (integral_integral_swap hF).symm
    _ = _ := by
      unfold planarKernelVelocity
      apply integral_congr_ae
      exact ae_of_all _ (fun z => by
        dsimp only [F]
        rw [integral_smul])

end Euler2D

end
