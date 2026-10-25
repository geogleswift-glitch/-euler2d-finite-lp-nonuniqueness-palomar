module

public import RequestProject.Euler.TorusMollificationApproximation

/-! Uniform bounds for the actual velocities obtained from the smooth kernels. -/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology Metric Real
open scoped ContDiff ENNReal

namespace Euler2D

lemma integrable_torusKernelAverage_integrand {w : R2 → ℝ} {g : R2 → R2}
    (hw : AEStronglyMeasurable w μT) {M : ℝ} (hM : ∀ᵐ y ∂μT, ‖w y‖ ≤ M)
    (hg : Integrable g μT) (hp : IsTorusPeriodic g) (x : R2) :
    Integrable (fun y => w y • g (x - y + torusCenter)) μT :=
  (integrable_periodicKernel_sub_left hg hp x).bdd_smul M hw hM

theorem norm_torusKernelAverage_le {w : R2 → ℝ} {g : R2 → R2}
    {M : ℝ} (hM : ∀ᵐ y ∂μT, ‖w y‖ ≤ M)
    (hg : Integrable g μT) (hp : IsTorusPeriodic g) (x : R2) :
    ‖torusKernelAverage w g x‖ ≤ M * ∫ y in torusBox, ‖g y‖ := by
  calc
    _ ≤ ∫ y in torusBox, M * ‖g (x - y + torusCenter)‖ := by
      apply norm_integral_le_of_norm_le ((integrable_periodicKernel_sub_left hg hp x).norm.const_mul M)
      filter_upwards [hM] with y hy
      rw [norm_smul]
      exact mul_le_mul_of_nonneg_right hy (norm_nonneg _)
    _ = _ := by rw [integral_const_mul, integral_norm_periodicKernel_sub_left hg hp]

lemma torusKernelAverage_sub_kernel {w : R2 → ℝ} {f g : R2 → R2}
    (hw : AEStronglyMeasurable w μT) {M : ℝ} (hM : ∀ᵐ y ∂μT, ‖w y‖ ≤ M)
    (hf : Integrable f μT) (hfp : IsTorusPeriodic f)
    (hg : Integrable g μT) (hgp : IsTorusPeriodic g) (x : R2) :
    torusKernelAverage w f x - torusKernelAverage w g x =
      torusKernelAverage w (fun y => f y - g y) x := by
  unfold torusKernelAverage
  rw [← integral_sub (integrable_torusKernelAverage_integrand hw hM hf hfp x)
    (integrable_torusKernelAverage_integrand hw hM hg hgp x)]
  apply integral_congr_ae
  exact Eventually.of_forall fun y => (smul_sub _ _ _).symm

lemma integrable_regularizedTorusKernel {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    Integrable (regularizedTorusKernel ε hε) μT :=
  memLp_one_iff_integrable.mp (continuous_vector_memLp_torus
    (regularizedTorusKernel_smooth hε hε1).continuous 1)

theorem norm_regularizedTorusVelocity_le {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    {w : R2 → ℝ} {M : ℝ} (hM0 : 0 ≤ M) (hM : ∀ᵐ y ∂μT, ‖w y‖ ≤ M) (x : R2) :
    ‖torusKernelAverage w (regularizedTorusKernel ε hε) x‖ ≤
      M * ∫ y in torusBox, ‖torusBiotSavartKernel y‖ :=
  (norm_torusKernelAverage_le hM (integrable_regularizedTorusKernel hε hε1)
    (regularizedTorusKernel_periodic ε hε) x).trans
      (mul_le_mul_of_nonneg_left (integral_norm_regularizedTorusKernel_le hε hε1) hM0)

lemma torusKernelAverage_sub_spatial {w : R2 → ℝ} {g : R2 → R2}
    (hw : AEStronglyMeasurable w μT) {M : ℝ} (hM : ∀ᵐ y ∂μT, ‖w y‖ ≤ M)
    (hg : Integrable g μT) (hp : IsTorusPeriodic g) (x z : R2) :
    torusKernelAverage w g x - torusKernelAverage w g z =
      torusKernelAverage w (fun y => g (y + (x - z)) - g y) z := by
  unfold torusKernelAverage
  rw [← integral_sub (integrable_torusKernelAverage_integrand hw hM hg hp x)
    (integrable_torusKernelAverage_integrand hw hM hg hp z)]
  apply integral_congr_ae
  exact Eventually.of_forall fun y => by
    dsimp only
    rw [← smul_sub]
    congr 2
    abel

theorem norm_regularizedTorusVelocity_sub_le {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    {w : R2 → ℝ} (hw : AEStronglyMeasurable w μT) {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ᵐ y ∂μT, ‖w y‖ ≤ M) (x z : R2) :
    ‖torusKernelAverage w (regularizedTorusKernel ε hε) x -
      torusKernelAverage w (regularizedTorusKernel ε hε) z‖ ≤
        M * torusKernelTranslationError (x - z) := by
  let g := regularizedTorusKernel ε hε
  have hgc : Continuous g := (regularizedTorusKernel_smooth hε hε1).continuous
  have hgp : IsTorusPeriodic g := regularizedTorusKernel_periodic ε hε
  have hdiffp : IsTorusPeriodic (fun y => g (y + (x - z)) - g y) := by
    intro y i
    have he : y + EuclideanSpace.single i (2 * π) + (x - z) =
        (y + (x - z)) + EuclideanSpace.single i (2 * π) := by abel
    dsimp only
    rw [he, hgp, hgp]
  have hdiffi : Integrable (fun y => g (y + (x - z)) - g y) μT :=
    memLp_one_iff_integrable.mp (continuous_vector_memLp_torus
      ((hgc.comp (continuous_id.add continuous_const)).sub hgc) 1)
  rw [torusKernelAverage_sub_spatial hw hM (integrable_regularizedTorusKernel hε hε1) hgp]
  exact (norm_torusKernelAverage_le hM hdiffi hdiffp z).trans
    (mul_le_mul_of_nonneg_left (integral_norm_regularizedTorusKernel_translation_le hε hε1 (x - z)) hM0)

theorem norm_regularizedTorusVelocity_error_le {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    {w : R2 → ℝ} (hw : AEStronglyMeasurable w μT) {M : ℝ}
    (hM : ∀ᵐ y ∂μT, ‖w y‖ ≤ M) (x : R2) :
    ‖torusKernelAverage w (regularizedTorusKernel ε hε) x - torusKernelVelocity w x‖ ≤
      M * regularizedTorusKernelL1Error ε hε := by
  have hi := (integrable_regularizedTorusKernel hε hε1).sub integrable_torusBiotSavartKernel
  have hp : IsTorusPeriodic (fun y => regularizedTorusKernel ε hε y - torusBiotSavartKernel y) :=
    fun y i => by
      dsimp only
      rw [regularizedTorusKernel_periodic ε hε, isTorusPeriodic_torusBiotSavartKernel]
  change ‖torusKernelAverage w (regularizedTorusKernel ε hε) x -
    torusKernelAverage w torusBiotSavartKernel x‖ ≤ _
  rw [torusKernelAverage_sub_kernel hw hM (integrable_regularizedTorusKernel hε hε1)
    (regularizedTorusKernel_periodic ε hε) integrable_torusBiotSavartKernel
    isTorusPeriodic_torusBiotSavartKernel]
  exact norm_torusKernelAverage_le hM hi hp x

end Euler2D

end
