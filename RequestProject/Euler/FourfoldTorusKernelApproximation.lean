module

public import RequestProject.Euler.FourfoldTorusKernelMollification
public import RequestProject.Euler.TorusRegularizedVelocityBounds

/-! The actual smooth kernels converge to the singular kernel in physical `L¹`. -/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology Metric Real
open scoped ContDiff ENNReal

namespace Euler2D

def fourfoldRegularizedTorusKernelL1Error (ε : ℝ) (hε : 0 < ε) : ℝ :=
  ∫ x in torusBox, ‖fourfoldRegularizedTorusKernel ε hε x - torusBiotSavartKernel x‖

lemma fourfoldRegularizedTorusKernelL1Error_nonneg (ε : ℝ) (hε : 0 < ε) :
    0 ≤ fourfoldRegularizedTorusKernelL1Error ε hε := integral_nonneg (fun _ => norm_nonneg _)

lemma fourfoldRegularizedTorusKernel_error_eq_integral {ε : ℝ} (hε : 0 < ε)
    (hε1 : ε ≤ 1) (x : R2) :
    fourfoldRegularizedTorusKernel ε hε x - torusBiotSavartKernel x =
      ∫ y in torusBox, fourfoldTorusKernelMollifier ε hε y •
        (torusBiotSavartKernel (x - y + torusCenter) - torusBiotSavartKernel x) := by
  have hw := (fourfoldTorusKernelMollifier_test hε hε1).1.continuous
  have hwi := integrable_torusBox_of_continuous hw
  obtain ⟨M, hM⟩ := bound_on_box hw
  have hb : ∀ᵐ y ∂μT, ‖fourfoldTorusKernelMollifier ε hε y‖ ≤ M := by
    filter_upwards [ae_restrict_mem measurableSet_torusBox] with y hy
    simpa only [Real.norm_eq_abs] using hM y hy
  have hconst : (∫ y in torusBox, fourfoldTorusKernelMollifier ε hε y • torusBiotSavartKernel x) =
      torusBiotSavartKernel x := by
    rw [integral_smul_const, fourfoldTorusKernelMollifier_integral hε hε1, one_smul]
  conv_lhs => rw [← hconst]
  change (∫ y in torusBox, fourfoldTorusKernelMollifier ε hε y •
      torusBiotSavartKernel (x - y + torusCenter)) - _ = _
  rw [← integral_sub (integrable_torusKernelVelocity_integrand hw.aestronglyMeasurable hb x)
    (hwi.smul_const _)]
  apply integral_congr_ae
  exact Eventually.of_forall fun y => (smul_sub _ _ _).symm

lemma integrable_fourfoldRegularizedTorusKernel_error_prod {ε : ℝ} (hε : 0 < ε)
    (hε1 : ε ≤ 1) :
    Integrable (fun p : R2 × R2 => fourfoldTorusKernelMollifier ε hε p.2 •
      (torusBiotSavartKernel (p.1 - p.2 + torusCenter) - torusBiotSavartKernel p.1))
      (μT.prod μT) := by
  have hw := (fourfoldTorusKernelMollifier_test hε hε1).1.continuous
  have ha := integrable_torusKernelAverage_prod hw integrable_torusBiotSavartKernel
    measurable_torusBiotSavartKernel isTorusPeriodic_torusBiotSavartKernel
  have hb := ((integrable_torusBox_of_continuous hw).smul_prod
    integrable_torusBiotSavartKernel).swap
  convert ha.sub hb using 1
  funext p
  exact smul_sub _ _ _

lemma integral_norm_fourfoldRegularizedTorusKernel_error_inner {ε : ℝ} (hε : 0 < ε) (y : R2) :
    (∫ x in torusBox, ‖fourfoldTorusKernelMollifier ε hε y •
      (torusBiotSavartKernel (x - y + torusCenter) - torusBiotSavartKernel x)‖) =
      fourfoldTorusKernelMollifier ε hε y * torusKernelTranslationError (torusCenter - y) := by
  simp_rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (fourfoldTorusKernelMollifier_nonneg ε hε y)]
  rw [integral_const_mul]
  congr 1
  unfold torusKernelTranslationError
  congr 1
  funext x
  congr 3
  abel

theorem exists_fourfoldRegularizedTorusKernelL1Error_le_logFlowModulus :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (ε : ℝ) (hε : 0 < ε), ε ≤ 1 / 2 →
      fourfoldRegularizedTorusKernelL1Error ε hε ≤ C * logFlowModulus ε := by
  obtain ⟨C, hC, hbound⟩ := exists_torusKernelTranslationError_le_logFlowModulus
  refine ⟨C, hC, fun ε hε hεhalf => ?_⟩
  have hε1 : ε ≤ 1 := by linarith
  have hw := (fourfoldTorusKernelMollifier_test hε hε1).1.continuous
  have hwi := integrable_torusBox_of_continuous hw
  have hprod := integrable_fourfoldRegularizedTorusKernel_error_prod hε hε1
  have herror : Integrable (fun x => fourfoldRegularizedTorusKernel ε hε x - torusBiotSavartKernel x) μT :=
    (memLp_one_iff_integrable.mp (continuous_vector_memLp_torus
      (fourfoldRegularizedTorusKernel_smooth hε hε1).continuous 1)).sub
      integrable_torusBiotSavartKernel
  have hpt (y : R2) (hy : y ∈ torusBox) :
      fourfoldTorusKernelMollifier ε hε y * torusKernelTranslationError (torusCenter - y) ≤
        fourfoldTorusKernelMollifier ε hε y * (C * logFlowModulus ε) := by
    by_cases hzero : ε ≤ ‖y - torusCenter‖
    · rw [fourfoldTorusKernelMollifier_eq_zero_on_box hε hε1 hy hzero, zero_mul, zero_mul]
    · have hn : ‖torusCenter - y‖ ≤ ε := by
        rw [norm_sub_rev]
        exact (lt_of_not_ge hzero).le
      have hlog := monotoneOn_logFlowModulus
        (show ‖torusCenter - y‖ ∈ Icc 0 1 from ⟨norm_nonneg _, hn.trans hε1⟩)
        (show ε ∈ Icc 0 1 from ⟨hε.le, hε1⟩) hn
      exact mul_le_mul_of_nonneg_left
        ((hbound (torusCenter - y) (hn.trans hεhalf)).trans
          (mul_le_mul_of_nonneg_left hlog hC)) (fourfoldTorusKernelMollifier_nonneg ε hε y)
  calc
    _ ≤ ∫ x in torusBox, ∫ y in torusBox, ‖fourfoldTorusKernelMollifier ε hε y •
        (torusBiotSavartKernel (x - y + torusCenter) - torusBiotSavartKernel x)‖ := by
      apply integral_mono herror.norm hprod.integral_norm_prod_left
      intro x
      dsimp only
      rw [fourfoldRegularizedTorusKernel_error_eq_integral hε hε1]
      exact norm_integral_le_integral_norm _
    _ = ∫ y in torusBox, ∫ x in torusBox, ‖fourfoldTorusKernelMollifier ε hε y •
        (torusBiotSavartKernel (x - y + torusCenter) - torusBiotSavartKernel x)‖ :=
      integral_integral_swap hprod.norm
    _ ≤ ∫ y in torusBox, fourfoldTorusKernelMollifier ε hε y * (C * logFlowModulus ε) := by
      apply integral_mono_ae hprod.integral_norm_prod_right (hwi.mul_const _)
      filter_upwards [ae_restrict_mem measurableSet_torusBox] with y hy
      rw [integral_norm_fourfoldRegularizedTorusKernel_error_inner]
      exact hpt y hy
    _ = C * logFlowModulus ε := by
      rw [integral_mul_const, fourfoldTorusKernelMollifier_integral hε hε1, one_mul]

theorem tendsto_fourfoldRegularizedTorusKernel_L1 {ι : Type*} {l : Filter ι}
    (ε : ι → ℝ) (hε : ∀ i, 0 < ε i) (hlim : Tendsto ε l (𝓝 0)) :
    Tendsto (fun i => fourfoldRegularizedTorusKernelL1Error (ε i) (hε i)) l (𝓝 0) := by
  obtain ⟨C, hC, hbound⟩ := exists_fourfoldRegularizedTorusKernelL1Error_le_logFlowModulus
  have he : ∀ᶠ i in l, ε i ≤ 1 / 2 := by
    filter_upwards [hlim.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))] with i hi
    exact hi.le
  have hm : Tendsto (fun i => C * logFlowModulus (ε i)) l (𝓝 0) := by
    simpa only [Function.comp_def, logFlowModulus, log_zero, mul_zero, sub_zero] using
      (continuous_logFlowModulus.tendsto 0 |>.comp hlim).const_mul C
  apply squeeze_zero' (Eventually.of_forall fun i => fourfoldRegularizedTorusKernelL1Error_nonneg _ _) ?_ hm
  filter_upwards [he] with i hi
  exact hbound (ε i) (hε i) hi

theorem integral_norm_fourfoldRegularizedTorusKernel_le {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    (∫ x in torusBox, ‖fourfoldRegularizedTorusKernel ε hε x‖) ≤
      ∫ x in torusBox, ‖torusBiotSavartKernel x‖ := by
  have h := integral_norm_torusKernelAverage_le
    (fourfoldTorusKernelMollifier_test hε hε1).1.continuous (fourfoldTorusKernelMollifier_nonneg ε hε)
    integrable_torusBiotSavartKernel measurable_torusBiotSavartKernel
    isTorusPeriodic_torusBiotSavartKernel
  change (∫ x in torusBox,
    ‖torusKernelAverage (fourfoldTorusKernelMollifier ε hε) torusBiotSavartKernel x‖) ≤
      ∫ x in torusBox, ‖torusBiotSavartKernel x‖
  simpa only [fourfoldTorusKernelMollifier_integral hε hε1, one_mul] using h

lemma fourfoldRegularizedTorusKernel_sub_eq_average {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (x h : R2) :
    fourfoldRegularizedTorusKernel ε hε (x + h) - fourfoldRegularizedTorusKernel ε hε x =
      torusKernelAverage (fourfoldTorusKernelMollifier ε hε)
        (fun z => torusBiotSavartKernel (z + h) - torusBiotSavartKernel z) x := by
  have hw := (fourfoldTorusKernelMollifier_test hε hε1).1.continuous
  obtain ⟨M, hM⟩ := bound_on_box hw
  have hb : ∀ᵐ y ∂μT, ‖fourfoldTorusKernelMollifier ε hε y‖ ≤ M := by
    filter_upwards [ae_restrict_mem measurableSet_torusBox] with y hy
    simpa only [Real.norm_eq_abs] using hM y hy
  have he := torusKernelAverage_sub_spatial hw.aestronglyMeasurable hb
    integrable_torusBiotSavartKernel isTorusPeriodic_torusBiotSavartKernel (x + h) x
  change torusKernelAverage (fourfoldTorusKernelMollifier ε hε) torusBiotSavartKernel (x + h) -
    torusKernelAverage (fourfoldTorusKernelMollifier ε hε) torusBiotSavartKernel x = _
  simpa only [add_sub_cancel_left] using he

theorem integral_norm_fourfoldRegularizedTorusKernel_translation_le {ε : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1) (h : R2) :
    (∫ x in torusBox, ‖fourfoldRegularizedTorusKernel ε hε (x + h) -
      fourfoldRegularizedTorusKernel ε hε x‖) ≤ torusKernelTranslationError h := by
  let g := fun z => torusBiotSavartKernel (z + h) - torusBiotSavartKernel z
  have hgm : Measurable g :=
    (measurable_torusBiotSavartKernel.comp (measurable_id.add_const h)).sub
      measurable_torusBiotSavartKernel
  have hgp : IsTorusPeriodic g := by
    intro x i
    dsimp only [g]
    have he : x + EuclideanSpace.single i (2 * Real.pi) + h =
        (x + h) + EuclideanSpace.single i (2 * Real.pi) := by abel
    rw [he, isTorusPeriodic_torusBiotSavartKernel, isTorusPeriodic_torusBiotSavartKernel]
  simp_rw [fourfoldRegularizedTorusKernel_sub_eq_average hε hε1]
  have hb := integral_norm_torusKernelAverage_le
    (fourfoldTorusKernelMollifier_test hε hε1).1.continuous (fourfoldTorusKernelMollifier_nonneg ε hε)
    (integrable_torusBiotSavartKernel_translation_difference h) hgm hgp
  unfold torusKernelTranslationError
  simpa only [fourfoldTorusKernelMollifier_integral hε hε1, one_mul] using hb

theorem exists_uniform_fourfoldRegularizedKernel_translation_le_logFlowModulus :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (ε : ℝ) (hε : 0 < ε), ε ≤ 1 →
      ∀ h : R2, ‖h‖ ≤ 1 / 2 →
      (∫ x in torusBox, ‖fourfoldRegularizedTorusKernel ε hε (x + h) -
        fourfoldRegularizedTorusKernel ε hε x‖) ≤ C * logFlowModulus ‖h‖ := by
  obtain ⟨C, hC, hbound⟩ := exists_torusKernelTranslationError_le_logFlowModulus
  exact ⟨C, hC, fun ε hε hε1 h hh =>
    (integral_norm_fourfoldRegularizedTorusKernel_translation_le hε hε1 h).trans (hbound h hh)⟩

lemma integrable_fourfoldRegularizedTorusKernel {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    Integrable (fourfoldRegularizedTorusKernel ε hε) μT :=
  memLp_one_iff_integrable.mp (continuous_vector_memLp_torus
    (fourfoldRegularizedTorusKernel_smooth hε hε1).continuous 1)

theorem norm_fourfoldRegularizedTorusVelocity_le {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    {w : R2 → ℝ} {M : ℝ} (hM0 : 0 ≤ M) (hM : ∀ᵐ y ∂μT, ‖w y‖ ≤ M) (x : R2) :
    ‖torusKernelAverage w (fourfoldRegularizedTorusKernel ε hε) x‖ ≤
      M * ∫ y in torusBox, ‖torusBiotSavartKernel y‖ :=
  (norm_torusKernelAverage_le hM (integrable_fourfoldRegularizedTorusKernel hε hε1)
    (fourfoldRegularizedTorusKernel_periodic ε hε) x).trans
      (mul_le_mul_of_nonneg_left (integral_norm_fourfoldRegularizedTorusKernel_le hε hε1) hM0)

theorem norm_fourfoldRegularizedTorusVelocity_sub_le {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    {w : R2 → ℝ} (hw : AEStronglyMeasurable w μT) {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ᵐ y ∂μT, ‖w y‖ ≤ M) (x z : R2) :
    ‖torusKernelAverage w (fourfoldRegularizedTorusKernel ε hε) x -
      torusKernelAverage w (fourfoldRegularizedTorusKernel ε hε) z‖ ≤
        M * torusKernelTranslationError (x - z) := by
  let g := fourfoldRegularizedTorusKernel ε hε
  have hgc : Continuous g := (fourfoldRegularizedTorusKernel_smooth hε hε1).continuous
  have hgp : IsTorusPeriodic g := fourfoldRegularizedTorusKernel_periodic ε hε
  have hdiffp : IsTorusPeriodic (fun y => g (y + (x - z)) - g y) := by
    intro y i
    have he : y + EuclideanSpace.single i (2 * Real.pi) + (x - z) =
        (y + (x - z)) + EuclideanSpace.single i (2 * Real.pi) := by abel
    dsimp only
    rw [he, hgp, hgp]
  have hdiffi : Integrable (fun y => g (y + (x - z)) - g y) μT :=
    memLp_one_iff_integrable.mp (continuous_vector_memLp_torus
      ((hgc.comp (continuous_id.add continuous_const)).sub hgc) 1)
  rw [torusKernelAverage_sub_spatial hw hM (integrable_fourfoldRegularizedTorusKernel hε hε1) hgp]
  exact (norm_torusKernelAverage_le hM hdiffi hdiffp z).trans
    (mul_le_mul_of_nonneg_left (integral_norm_fourfoldRegularizedTorusKernel_translation_le hε hε1 (x - z)) hM0)

theorem norm_fourfoldRegularizedTorusVelocity_error_le {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    {w : R2 → ℝ} (hw : AEStronglyMeasurable w μT) {M : ℝ}
    (hM : ∀ᵐ y ∂μT, ‖w y‖ ≤ M) (x : R2) :
    ‖torusKernelAverage w (fourfoldRegularizedTorusKernel ε hε) x - torusKernelVelocity w x‖ ≤
      M * fourfoldRegularizedTorusKernelL1Error ε hε := by
  have hi := (integrable_fourfoldRegularizedTorusKernel hε hε1).sub integrable_torusBiotSavartKernel
  have hp : IsTorusPeriodic (fun y => fourfoldRegularizedTorusKernel ε hε y - torusBiotSavartKernel y) :=
    fun y i => by
      dsimp only
      rw [fourfoldRegularizedTorusKernel_periodic ε hε, isTorusPeriodic_torusBiotSavartKernel]
  change ‖torusKernelAverage w (fourfoldRegularizedTorusKernel ε hε) x -
    torusKernelAverage w torusBiotSavartKernel x‖ ≤ _
  rw [torusKernelAverage_sub_kernel hw hM (integrable_fourfoldRegularizedTorusKernel hε hε1)
    (fourfoldRegularizedTorusKernel_periodic ε hε) integrable_torusBiotSavartKernel
    isTorusPeriodic_torusBiotSavartKernel]
  exact norm_torusKernelAverage_le hM hi hp x

end Euler2D

end

