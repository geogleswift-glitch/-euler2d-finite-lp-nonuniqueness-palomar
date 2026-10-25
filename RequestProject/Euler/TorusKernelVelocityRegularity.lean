module

public import RequestProject.Euler.TorusKernelConvolution
public import RequestProject.Euler.TorusKernelTranslation

/-! Actual continuity and logarithmic spatial regularity of the velocity integral. -/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology Metric Real
open scoped ContDiff ENNReal

namespace Euler2D

lemma isTorusPeriodic_kernelNormDifference (h : R2) :
    IsTorusPeriodic (fun x => ‖torusBiotSavartKernel (x + h) - torusBiotSavartKernel x‖) := by
  intro x i
  have he : x + EuclideanSpace.single i (2 * π) + h =
      (x + h) + EuclideanSpace.single i (2 * π) := by abel
  dsimp only
  rw [he, isTorusPeriodic_torusBiotSavartKernel, isTorusPeriodic_torusBiotSavartKernel]

lemma integral_norm_torusKernel_two_centers (x z : R2) :
    (∫ y in torusBox, ‖torusBiotSavartKernel (x - y + torusCenter) -
      torusBiotSavartKernel (z - y + torusCenter)‖) = torusKernelTranslationError (x - z) := by
  have he := (torusAreaPreserving_sub_left (z + torusCenter)).integral_comp
    (integrable_torusBiotSavartKernel_translation_difference (x - z)).norm.aestronglyMeasurable
    (isTorusPeriodic_kernelNormDifference (x - z))
  calc
    _ = ∫ y in torusBox, ‖torusBiotSavartKernel ((z + torusCenter - y) + (x - z)) -
        torusBiotSavartKernel (z + torusCenter - y)‖ := by
      congr 1
      funext y
      have hx : x - y + torusCenter = (z + torusCenter - y) + (x - z) := by abel
      have hz : z - y + torusCenter = z + torusCenter - y := by abel
      rw [hx, hz]
    _ = _ := he

theorem norm_torusKernelVelocity_sub_le {w : R2 → ℝ}
    (hw : AEStronglyMeasurable w μT) {M : ℝ} (hM : ∀ᵐ y ∂μT, ‖w y‖ ≤ M) (x z : R2) :
    ‖torusKernelVelocity w x - torusKernelVelocity w z‖ ≤
      M * torusKernelTranslationError (x - z) := by
  have hix := integrable_torusKernelVelocity_integrand hw hM x
  have hiz := integrable_torusKernelVelocity_integrand hw hM z
  have hi : Integrable (fun y => M * ‖torusBiotSavartKernel (x - y + torusCenter) -
      torusBiotSavartKernel (z - y + torusCenter)‖) μT :=
    ((integrable_torusBiotSavartKernel_sub_left x).sub
      (integrable_torusBiotSavartKernel_sub_left z)).norm.const_mul M
  change ‖(∫ y in torusBox, w y • torusBiotSavartKernel (x - y + torusCenter)) -
    ∫ y in torusBox, w y • torusBiotSavartKernel (z - y + torusCenter)‖ ≤ _
  rw [← integral_sub hix hiz]
  calc
    _ ≤ ∫ y in torusBox, M * ‖torusBiotSavartKernel (x - y + torusCenter) -
        torusBiotSavartKernel (z - y + torusCenter)‖ := by
      apply norm_integral_le_of_norm_le hi
      filter_upwards [hM] with y hy
      rw [← smul_sub, norm_smul]
      exact mul_le_mul_of_nonneg_right hy (norm_nonneg _)
    _ = _ := by rw [integral_const_mul, integral_norm_torusKernel_two_centers]

theorem continuous_torusKernelVelocity {w : R2 → ℝ}
    (hw : AEStronglyMeasurable w μT) {M : ℝ} (hM : ∀ᵐ y ∂μT, ‖w y‖ ≤ M) :
    Continuous (torusKernelVelocity w) := by
  rw [continuous_iff_continuousAt]
  intro a
  have hsub : Tendsto (fun x : R2 => x - a) (𝓝 a) (𝓝 0) := by
    have hc : Continuous (fun x : R2 => x - a) := continuous_id.sub continuous_const
    simpa only [sub_self] using hc.tendsto a
  have hlim : Tendsto (fun x : R2 => M * torusKernelTranslationError (x - a))
      (𝓝 a) (𝓝 0) := by
    simpa only [mul_zero] using (tendsto_torusKernelTranslationError_zero.comp hsub).const_mul M
  have hdiff : Tendsto (fun x => torusKernelVelocity w x - torusKernelVelocity w a)
      (𝓝 a) (𝓝 0) :=
    squeeze_zero_norm (fun x => norm_torusKernelVelocity_sub_le hw hM x a) hlim
  simpa only [sub_add_cancel, zero_add] using hdiff.add_const (torusKernelVelocity w a)

theorem exists_logLip_torusKernelVelocity {w : R2 → ℝ}
    (hw : AEStronglyMeasurable w μT) {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ᵐ y ∂μT, ‖w y‖ ≤ M) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x z : R2, ‖x - z‖ ≤ 1 / 2 →
      ‖torusKernelVelocity w x - torusKernelVelocity w z‖ ≤ C * logFlowModulus ‖x - z‖ := by
  obtain ⟨L, hL, hbound⟩ := exists_torusKernelTranslationError_le_logFlowModulus
  refine ⟨M * L, mul_nonneg hM0 hL, fun x z hxz => ?_⟩
  exact (norm_torusKernelVelocity_sub_le hw hM x z).trans
    (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (hbound (x - z) hxz) hM0)

theorem exists_uniform_logLip_torusKernelVelocity {ι : Type*} {w : ι → R2 → ℝ}
    (hw : ∀ t, AEStronglyMeasurable (w t) μT) {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ t, ∀ᵐ y ∂μT, ‖w t y‖ ≤ M) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t x z, ‖x - z‖ ≤ 1 / 2 →
      ‖torusKernelVelocity (w t) x - torusKernelVelocity (w t) z‖ ≤
        C * logFlowModulus ‖x - z‖ := by
  obtain ⟨L, hL, hbound⟩ := exists_torusKernelTranslationError_le_logFlowModulus
  refine ⟨M * L, mul_nonneg hM0 hL, fun t x z hxz => ?_⟩
  exact (norm_torusKernelVelocity_sub_le (hw t) (hM t) x z).trans
    (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (hbound (x - z) hxz) hM0)

end Euler2D

end
