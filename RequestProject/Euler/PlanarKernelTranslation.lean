module

public import RequestProject.Euler.PlanarKernelIntegrals
public import RequestProject.Euler.Osgood

/-! Actual `L¹` translation bounds for the fixed singular local kernel. -/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology Metric Real
open scoped ContDiff

namespace Euler2D

def localKernelTranslationError (h : R2) : ℝ :=
  ∫ x, ‖localPlanarKernel (x + h) - localPlanarKernel x‖

lemma integrable_localPlanarKernel_translation_difference (h : R2) :
    Integrable (fun x => localPlanarKernel (x + h) - localPlanarKernel x) :=
  (integrable_localPlanarKernel.comp_add_right h).sub integrable_localPlanarKernel

lemma integrable_norm_localPlanarKernel_translation_difference (h : R2) :
    Integrable (fun x => ‖localPlanarKernel (x + h) - localPlanarKernel x‖) :=
  (integrable_localPlanarKernel_translation_difference h).norm

lemma localKernelTranslationError_nonneg (h : R2) : 0 ≤ localKernelTranslationError h :=
  integral_nonneg (fun _ => norm_nonneg _)

@[simp] lemma localKernelTranslationError_zero : localKernelTranslationError 0 = 0 := by
  simp [localKernelTranslationError]

lemma localKernelTranslationError_le_two (h : R2) : localKernelTranslationError h ≤ 2 := by
  calc
    _ ≤ ∫ x, ‖localPlanarKernel (x + h)‖ + ‖localPlanarKernel x‖ := by
      apply integral_mono (integrable_norm_localPlanarKernel_translation_difference h)
        ((integrable_localPlanarKernel.comp_add_right h).norm.add integrable_localPlanarKernel.norm)
      exact fun x => norm_sub_le _ _
    _ = 2 * (∫ x, ‖localPlanarKernel x‖) := by
      rw [integral_add (integrable_localPlanarKernel.comp_add_right h).norm integrable_localPlanarKernel.norm]
      have he : (∫ x : R2, ‖localPlanarKernel (x + h)‖) = ∫ x : R2, ‖localPlanarKernel x‖ :=
        integral_add_right_eq_self (μ := volume) (fun x : R2 => ‖localPlanarKernel x‖) h
      rw [he]
      ring
    _ ≤ 2 := by linarith [integral_norm_localPlanarKernel_le_one]

theorem integral_norm_localPlanarKernel_add_closedBall_le (h : R2) {r : ℝ} (hr : 0 ≤ r) :
    (∫ x in closedBall (0 : R2) r, ‖localPlanarKernel (x + h)‖) ≤ r + ‖h‖ := by
  have hleft : Integrable (fun x => (closedBall (0 : R2) r).indicator
      (fun x => ‖localPlanarKernel (x + h)‖) x) :=
    ((integrable_localPlanarKernel.comp_add_right h).norm).indicator measurableSet_closedBall
  have hright : Integrable (fun x => (closedBall (0 : R2) (r + ‖h‖)).indicator
      (fun x => ‖localPlanarKernel x‖) (x + h)) :=
    (integrable_localPlanarKernel.norm.indicator measurableSet_closedBall).comp_add_right h
  rw [← integral_indicator measurableSet_closedBall]
  calc
    _ ≤ ∫ x, (closedBall (0 : R2) (r + ‖h‖)).indicator
        (fun x => ‖localPlanarKernel x‖) (x + h) := by
      apply integral_mono hleft hright
      intro x
      change (closedBall (0 : R2) r).indicator (fun x => ‖localPlanarKernel (x + h)‖) x ≤
        (closedBall (0 : R2) (r + ‖h‖)).indicator (fun x => ‖localPlanarKernel x‖) (x + h)
      by_cases hx : x ∈ closedBall (0 : R2) r
      · have hxh : x + h ∈ closedBall (0 : R2) (r + ‖h‖) :=
          mem_closedBall_zero_iff.mpr ((norm_add_le _ _).trans
            (by have := mem_closedBall_zero_iff.mp hx; linarith))
        rw [Set.indicator_of_mem hx, Set.indicator_of_mem hxh]
      · rw [Set.indicator_of_notMem hx]
        exact Set.indicator_nonneg (fun _ _ => norm_nonneg _) _
    _ = ∫ x in closedBall (0 : R2) (r + ‖h‖), ‖localPlanarKernel x‖ := by
      rw [integral_add_right_eq_self, integral_indicator measurableSet_closedBall]
    _ ≤ r + ‖h‖ := integral_norm_localPlanarKernel_closedBall_le (add_nonneg hr (norm_nonneg _))

theorem integral_translation_difference_near_le (h : R2) {r : ℝ} (hr : 0 ≤ r) :
    (∫ x in closedBall (0 : R2) r, ‖localPlanarKernel (x + h) - localPlanarKernel x‖) ≤
      (r + ‖h‖) + r := by
  calc
    _ ≤ ∫ x in closedBall (0 : R2) r,
        ‖localPlanarKernel (x + h)‖ + ‖localPlanarKernel x‖ := by
      apply integral_mono (integrable_norm_localPlanarKernel_translation_difference h).integrableOn
        (((integrable_localPlanarKernel.comp_add_right h).norm.add integrable_localPlanarKernel.norm).integrableOn)
      intro x
      exact norm_sub_le _ _
    _ = (∫ x in closedBall (0 : R2) r, ‖localPlanarKernel (x + h)‖) +
        (∫ x in closedBall (0 : R2) r, ‖localPlanarKernel x‖) :=
      integral_add (integrable_localPlanarKernel.comp_add_right h).norm.integrableOn
        integrable_localPlanarKernel.norm.integrableOn
    _ ≤ _ := add_le_add (integral_norm_localPlanarKernel_add_closedBall_le h hr)
      (integral_norm_localPlanarKernel_closedBall_le hr)

lemma translation_difference_eq_zero_of_two_lt_norm {h x : R2}
    (hh : ‖h‖ ≤ 1 / 4) (hx : 2 < ‖x‖) :
    localPlanarKernel (x + h) - localPlanarKernel x = 0 := by
  have htri : ‖x‖ ≤ ‖x + h‖ + ‖h‖ := by
    simpa only [add_sub_cancel_right] using norm_sub_le (x + h) h
  rw [localPlanarKernel_eq_zero_of_one_le_norm (by linarith : 1 ≤ ‖x + h‖),
    localPlanarKernel_eq_zero_of_one_le_norm (by linarith : 1 ≤ ‖x‖), sub_self]

theorem integral_translation_difference_far_le {C : ℝ} (hC : 0 ≤ C)
    (hderiv : ∀ x : R2, x ≠ 0 → ‖fderiv ℝ localPlanarKernel x‖ ≤ C * (‖x‖ ^ 2)⁻¹)
    {h : R2} (hh0 : h ≠ 0) (hh : ‖h‖ ≤ 1 / 4) :
    (∫ x in closedBall (0 : R2) 2 \ closedBall (0 : R2) (2 * ‖h‖),
      ‖localPlanarKernel (x + h) - localPlanarKernel x‖) ≤
      (8 * Real.pi * C) * ‖h‖ * (-Real.log ‖h‖) := by
  have hd : 0 < ‖h‖ := norm_pos_iff.mpr hh0
  have hR : 2 * ‖h‖ ≤ 2 := by linarith
  let s := closedBall (0 : R2) 2 \ closedBall (0 : R2) (2 * ‖h‖)
  have hs : MeasurableSet s := measurableSet_closedBall.diff measurableSet_closedBall
  calc
    _ ≤ ∫ x in s, (4 * C * ‖h‖) * (‖x‖ ^ 2)⁻¹ := by
      apply integral_mono_ae (integrable_norm_localPlanarKernel_translation_difference h).integrableOn
        ((integrableOn_inverse_sq_annulus (by positivity : 0 < 2 * ‖h‖)).const_mul _)
      filter_upwards [ae_restrict_mem hs] with x hx
      have hxn : 2 * ‖h‖ < ‖x‖ :=
        lt_of_not_ge (fun hb => hx.2 (mem_closedBall_zero_iff.mpr hb))
      have hx0 : x ≠ 0 := norm_pos_iff.mp (by linarith)
      have hxy : ‖(x + h) - x‖ ≤ ‖x‖ / 2 := by simp only [add_sub_cancel_left]; linarith
      have hb := norm_localPlanarKernel_sub_le hC hderiv hx0 hxy
      simpa only [add_sub_cancel_left, mul_assoc, mul_left_comm, mul_comm] using hb
    _ = (4 * C * ‖h‖) * ((2 * Real.pi) * Real.log (2 / (2 * ‖h‖))) := by
      rw [integral_const_mul]
      congr 1
      exact integral_inverse_sq_annulus (by positivity) hR
    _ = _ := by
      rw [show (2 : ℝ) / (2 * ‖h‖) = ‖h‖⁻¹ by field_simp, Real.log_inv]
      ring

theorem localKernelTranslationError_le_raw {C : ℝ} (hC : 0 ≤ C)
    (hderiv : ∀ x : R2, x ≠ 0 → ‖fderiv ℝ localPlanarKernel x‖ ≤ C * (‖x‖ ^ 2)⁻¹)
    {h : R2} (hh0 : h ≠ 0) (hh : ‖h‖ ≤ 1 / 4) :
    localKernelTranslationError h ≤
      5 * ‖h‖ + (8 * Real.pi * C) * ‖h‖ * (-Real.log ‖h‖) := by
  have houter : (∫ x in closedBall (0 : R2) 2,
      ‖localPlanarKernel (x + h) - localPlanarKernel x‖) = localKernelTranslationError h := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    rw [translation_difference_eq_zero_of_two_lt_norm hh
      (lt_of_not_ge (fun hb => hx (mem_closedBall_zero_iff.mpr hb))), norm_zero]
  have hmeas : MeasurableSet (closedBall (0 : R2) (2 * ‖h‖)) := measurableSet_closedBall
  have hsplit := integral_diff hmeas
    (integrable_norm_localPlanarKernel_translation_difference h).integrableOn
    (closedBall_subset_closedBall (by linarith : 2 * ‖h‖ ≤ 2))
  have hnear := integral_translation_difference_near_le h (by positivity : 0 ≤ 2 * ‖h‖)
  have hfar := integral_translation_difference_far_le hC hderiv hh0 hh
  rw [houter] at hsplit
  linarith

theorem exists_localKernelTranslationError_le_logFlowModulus :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ h : R2, ‖h‖ ≤ 1 / 4 →
      localKernelTranslationError h ≤ C * logFlowModulus ‖h‖ := by
  obtain ⟨D, hD, hderiv⟩ := exists_norm_fderiv_localPlanarKernel_le
  refine ⟨5 + 8 * Real.pi * D, by positivity, fun h hh => ?_⟩
  rcases eq_or_ne h 0 with rfl | hh0
  · simp [logFlowModulus]
  · have hd : 0 ≤ ‖h‖ := norm_nonneg h
    have hlog : Real.log ‖h‖ ≤ 0 := Real.log_nonpos hd (by linarith)
    have hmod1 : ‖h‖ ≤ logFlowModulus ‖h‖ := by
      unfold logFlowModulus
      nlinarith [mul_nonpos_of_nonneg_of_nonpos hd hlog]
    have hmod2 : ‖h‖ * (-Real.log ‖h‖) ≤ logFlowModulus ‖h‖ := by
      unfold logFlowModulus
      nlinarith
    calc
      _ ≤ 5 * ‖h‖ + (8 * Real.pi * D) * (‖h‖ * (-Real.log ‖h‖)) := by
        simpa only [mul_assoc] using localKernelTranslationError_le_raw hD.le hderiv hh0 hh
      _ ≤ 5 * logFlowModulus ‖h‖ + (8 * Real.pi * D) * logFlowModulus ‖h‖ := by
        exact add_le_add (mul_le_mul_of_nonneg_left hmod1 (by norm_num))
          (mul_le_mul_of_nonneg_left hmod2 (by positivity))
      _ = _ := by ring

/-- The half-unit version matches the radius used by the particle-flow
Osgood uniqueness theorem; larger shifts use the genuine global `L¹` bound. -/
theorem exists_localKernelTranslationError_le_logFlowModulus_half :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ h : R2, ‖h‖ ≤ 1 / 2 →
      localKernelTranslationError h ≤ C * logFlowModulus ‖h‖ := by
  obtain ⟨C, hC, hbound⟩ := exists_localKernelTranslationError_le_logFlowModulus
  refine ⟨C + 8, by positivity, fun h hh => ?_⟩
  have hd : 0 ≤ ‖h‖ := norm_nonneg h
  have hlog : Real.log ‖h‖ ≤ 0 := Real.log_nonpos hd (by linarith)
  have hmod : ‖h‖ ≤ logFlowModulus ‖h‖ := by
    unfold logFlowModulus
    nlinarith [mul_nonpos_of_nonneg_of_nonpos hd hlog]
  have hmod0 : 0 ≤ logFlowModulus ‖h‖ := hd.trans hmod
  by_cases hsmall : ‖h‖ ≤ 1 / 4
  · exact (hbound h hsmall).trans (mul_le_mul_of_nonneg_right (by linarith) hmod0)
  · have hlarge : 1 / 4 < ‖h‖ := lt_of_not_ge hsmall
    calc
      _ ≤ 2 := localKernelTranslationError_le_two h
      _ ≤ 8 * logFlowModulus ‖h‖ := by linarith
      _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) hmod0

theorem tendsto_localKernelTranslationError_zero :
    Tendsto localKernelTranslationError (𝓝 (0 : R2)) (𝓝 0) := by
  obtain ⟨C, hC, hbound⟩ := exists_localKernelTranslationError_le_logFlowModulus
  have hsmall : ∀ᶠ h : R2 in 𝓝 0, ‖h‖ ≤ 1 / 4 := by
    filter_upwards [Metric.ball_mem_nhds (0 : R2) (by norm_num : (0 : ℝ) < 1 / 4)] with h hh
    exact (mem_ball_zero_iff.mp hh).le
  have hlim : Tendsto (fun h : R2 => C * logFlowModulus ‖h‖) (𝓝 0) (𝓝 0) := by
    have hc : Continuous (fun h : R2 => C * logFlowModulus ‖h‖) :=
      continuous_const.mul (continuous_logFlowModulus.comp continuous_norm)
    simpa only [norm_zero, logFlowModulus, zero_mul, mul_zero, sub_zero] using
      hc.tendsto (0 : R2)
  apply squeeze_zero' (Eventually.of_forall localKernelTranslationError_nonneg) ?_ hlim
  filter_upwards [hsmall] with h hh
  exact hbound h hh

lemma integral_norm_translation_two_shifts (h a : R2) :
    (∫ x, ‖localPlanarKernel (x + h) - localPlanarKernel (x + a)‖) =
      localKernelTranslationError (h - a) := by
  have he : (fun x => ‖localPlanarKernel (x + h) - localPlanarKernel (x + a)‖) =
      (fun x => ‖localPlanarKernel ((x + a) + (h - a)) - localPlanarKernel (x + a)‖) := by
    funext x
    rw [show x + h = (x + a) + (h - a) by abel]
  rw [he]
  exact integral_add_right_eq_self (μ := volume)
    (fun x : R2 => ‖localPlanarKernel (x + (h - a)) - localPlanarKernel x‖) a

lemma abs_localKernelTranslationError_sub_le (h a : R2) :
    |localKernelTranslationError h - localKernelTranslationError a| ≤
      localKernelTranslationError (h - a) := by
  have hI := integrable_norm_localPlanarKernel_translation_difference h
  have hJ := integrable_norm_localPlanarKernel_translation_difference a
  have hR : Integrable (fun x => ‖localPlanarKernel (x + h) - localPlanarKernel (x + a)‖) :=
    ((integrable_localPlanarKernel.comp_add_right h).sub
      (integrable_localPlanarKernel.comp_add_right a)).norm
  change |(∫ x, ‖localPlanarKernel (x + h) - localPlanarKernel x‖) -
    (∫ x, ‖localPlanarKernel (x + a) - localPlanarKernel x‖)| ≤ _
  rw [← integral_sub hI hJ]
  calc
    _ ≤ ∫ x, |‖localPlanarKernel (x + h) - localPlanarKernel x‖ -
        ‖localPlanarKernel (x + a) - localPlanarKernel x‖| := by
      simpa only [Real.norm_eq_abs] using
        norm_integral_le_integral_norm (fun x : R2 =>
          ‖localPlanarKernel (x + h) - localPlanarKernel x‖ -
            ‖localPlanarKernel (x + a) - localPlanarKernel x‖)
    _ ≤ ∫ x, ‖localPlanarKernel (x + h) - localPlanarKernel (x + a)‖ := by
      apply integral_mono (hI.sub hJ).norm hR
      intro x
      simpa only [Pi.sub_apply, Real.norm_eq_abs, sub_sub_sub_cancel_right] using
        abs_norm_sub_norm_le (localPlanarKernel (x + h) - localPlanarKernel x)
          (localPlanarKernel (x + a) - localPlanarKernel x)
    _ = _ := integral_norm_translation_two_shifts h a

theorem continuous_localKernelTranslationError : Continuous localKernelTranslationError := by
  rw [continuous_iff_continuousAt]
  intro a
  have hs : Tendsto (fun h : R2 => h - a) (𝓝 a) (𝓝 0) := by
    have hc : Continuous (fun h : R2 => h - a) := continuous_id.sub continuous_const
    simpa only [sub_self] using hc.tendsto a
  have hlim := tendsto_localKernelTranslationError_zero.comp hs
  have hdiff : Tendsto (fun h => localKernelTranslationError h - localKernelTranslationError a)
      (𝓝 a) (𝓝 0) := by
    apply squeeze_zero_norm (fun h => ?_) hlim
    simpa only [Real.norm_eq_abs, Function.comp_def] using abs_localKernelTranslationError_sub_le h a
  simpa only [ContinuousAt, sub_add_cancel, zero_add] using hdiff.add_const (localKernelTranslationError a)

end Euler2D

end
