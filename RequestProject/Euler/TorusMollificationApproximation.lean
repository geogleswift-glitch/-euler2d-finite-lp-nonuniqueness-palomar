module

public import RequestProject.Euler.TorusMollificationL1

/-! The actual smooth kernels converge to the singular kernel in physical `L¹`. -/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology Metric Real
open scoped ContDiff ENNReal

namespace Euler2D

def regularizedTorusKernelL1Error (ε : ℝ) (hε : 0 < ε) : ℝ :=
  ∫ x in torusBox, ‖regularizedTorusKernel ε hε x - torusBiotSavartKernel x‖

lemma regularizedTorusKernelL1Error_nonneg (ε : ℝ) (hε : 0 < ε) :
    0 ≤ regularizedTorusKernelL1Error ε hε := integral_nonneg (fun _ => norm_nonneg _)

lemma regularizedTorusKernel_error_eq_integral {ε : ℝ} (hε : 0 < ε)
    (hε1 : ε ≤ 1) (x : R2) :
    regularizedTorusKernel ε hε x - torusBiotSavartKernel x =
      ∫ y in torusBox, torusKernelMollifier ε hε y •
        (torusBiotSavartKernel (x - y + torusCenter) - torusBiotSavartKernel x) := by
  have hw := (torusKernelMollifier_test hε hε1).1.continuous
  have hwi := integrable_torusBox_of_continuous hw
  obtain ⟨M, hM⟩ := bound_on_box hw
  have hb : ∀ᵐ y ∂μT, ‖torusKernelMollifier ε hε y‖ ≤ M := by
    filter_upwards [ae_restrict_mem measurableSet_torusBox] with y hy
    simpa only [Real.norm_eq_abs] using hM y hy
  have hconst : (∫ y in torusBox, torusKernelMollifier ε hε y • torusBiotSavartKernel x) =
      torusBiotSavartKernel x := by
    rw [integral_smul_const, torusKernelMollifier_integral hε hε1, one_smul]
  conv_lhs => rw [← hconst]
  change (∫ y in torusBox, torusKernelMollifier ε hε y •
      torusBiotSavartKernel (x - y + torusCenter)) - _ = _
  rw [← integral_sub (integrable_torusKernelVelocity_integrand hw.aestronglyMeasurable hb x)
    (hwi.smul_const _)]
  apply integral_congr_ae
  exact Eventually.of_forall fun y => (smul_sub _ _ _).symm

lemma integrable_regularizedTorusKernel_error_prod {ε : ℝ} (hε : 0 < ε)
    (hε1 : ε ≤ 1) :
    Integrable (fun p : R2 × R2 => torusKernelMollifier ε hε p.2 •
      (torusBiotSavartKernel (p.1 - p.2 + torusCenter) - torusBiotSavartKernel p.1))
      (μT.prod μT) := by
  have hw := (torusKernelMollifier_test hε hε1).1.continuous
  have ha := integrable_torusKernelAverage_prod hw integrable_torusBiotSavartKernel
    measurable_torusBiotSavartKernel isTorusPeriodic_torusBiotSavartKernel
  have hb := ((integrable_torusBox_of_continuous hw).smul_prod
    integrable_torusBiotSavartKernel).swap
  convert ha.sub hb using 1
  funext p
  exact smul_sub _ _ _

lemma integral_norm_regularizedTorusKernel_error_inner {ε : ℝ} (hε : 0 < ε) (y : R2) :
    (∫ x in torusBox, ‖torusKernelMollifier ε hε y •
      (torusBiotSavartKernel (x - y + torusCenter) - torusBiotSavartKernel x)‖) =
      torusKernelMollifier ε hε y * torusKernelTranslationError (torusCenter - y) := by
  simp_rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (torusKernelMollifier_nonneg ε hε y)]
  rw [integral_const_mul]
  congr 1
  unfold torusKernelTranslationError
  congr 1
  funext x
  congr 3
  abel

theorem exists_regularizedTorusKernelL1Error_le_logFlowModulus :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (ε : ℝ) (hε : 0 < ε), ε ≤ 1 / 2 →
      regularizedTorusKernelL1Error ε hε ≤ C * logFlowModulus ε := by
  obtain ⟨C, hC, hbound⟩ := exists_torusKernelTranslationError_le_logFlowModulus
  refine ⟨C, hC, fun ε hε hεhalf => ?_⟩
  have hε1 : ε ≤ 1 := by linarith
  have hw := (torusKernelMollifier_test hε hε1).1.continuous
  have hwi := integrable_torusBox_of_continuous hw
  have hprod := integrable_regularizedTorusKernel_error_prod hε hε1
  have herror : Integrable (fun x => regularizedTorusKernel ε hε x - torusBiotSavartKernel x) μT :=
    (memLp_one_iff_integrable.mp (continuous_vector_memLp_torus
      (regularizedTorusKernel_smooth hε hε1).continuous 1)).sub
      integrable_torusBiotSavartKernel
  have hpt (y : R2) (hy : y ∈ torusBox) :
      torusKernelMollifier ε hε y * torusKernelTranslationError (torusCenter - y) ≤
        torusKernelMollifier ε hε y * (C * logFlowModulus ε) := by
    by_cases hzero : ε ≤ ‖y - torusCenter‖
    · rw [torusKernelMollifier_eq_zero_on_box hε hε1 hy hzero, zero_mul, zero_mul]
    · have hn : ‖torusCenter - y‖ ≤ ε := by
        rw [norm_sub_rev]
        exact (lt_of_not_ge hzero).le
      have hlog := monotoneOn_logFlowModulus
        (show ‖torusCenter - y‖ ∈ Icc 0 1 from ⟨norm_nonneg _, hn.trans hε1⟩)
        (show ε ∈ Icc 0 1 from ⟨hε.le, hε1⟩) hn
      exact mul_le_mul_of_nonneg_left
        ((hbound (torusCenter - y) (hn.trans hεhalf)).trans
          (mul_le_mul_of_nonneg_left hlog hC)) (torusKernelMollifier_nonneg ε hε y)
  calc
    _ ≤ ∫ x in torusBox, ∫ y in torusBox, ‖torusKernelMollifier ε hε y •
        (torusBiotSavartKernel (x - y + torusCenter) - torusBiotSavartKernel x)‖ := by
      apply integral_mono herror.norm hprod.integral_norm_prod_left
      intro x
      dsimp only
      rw [regularizedTorusKernel_error_eq_integral hε hε1]
      exact norm_integral_le_integral_norm _
    _ = ∫ y in torusBox, ∫ x in torusBox, ‖torusKernelMollifier ε hε y •
        (torusBiotSavartKernel (x - y + torusCenter) - torusBiotSavartKernel x)‖ :=
      integral_integral_swap hprod.norm
    _ ≤ ∫ y in torusBox, torusKernelMollifier ε hε y * (C * logFlowModulus ε) := by
      apply integral_mono_ae hprod.integral_norm_prod_right (hwi.mul_const _)
      filter_upwards [ae_restrict_mem measurableSet_torusBox] with y hy
      rw [integral_norm_regularizedTorusKernel_error_inner]
      exact hpt y hy
    _ = C * logFlowModulus ε := by
      rw [integral_mul_const, torusKernelMollifier_integral hε hε1, one_mul]

theorem tendsto_regularizedTorusKernel_L1 {ι : Type*} {l : Filter ι}
    (ε : ι → ℝ) (hε : ∀ i, 0 < ε i) (hlim : Tendsto ε l (𝓝 0)) :
    Tendsto (fun i => regularizedTorusKernelL1Error (ε i) (hε i)) l (𝓝 0) := by
  obtain ⟨C, hC, hbound⟩ := exists_regularizedTorusKernelL1Error_le_logFlowModulus
  have he : ∀ᶠ i in l, ε i ≤ 1 / 2 := by
    filter_upwards [hlim.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))] with i hi
    exact hi.le
  have hm : Tendsto (fun i => C * logFlowModulus (ε i)) l (𝓝 0) := by
    simpa only [Function.comp_def, logFlowModulus, log_zero, mul_zero, sub_zero] using
      (continuous_logFlowModulus.tendsto 0 |>.comp hlim).const_mul C
  apply squeeze_zero' (Eventually.of_forall fun i => regularizedTorusKernelL1Error_nonneg _ _) ?_ hm
  filter_upwards [he] with i hi
  exact hbound (ε i) (hε i) hi

end Euler2D

end
