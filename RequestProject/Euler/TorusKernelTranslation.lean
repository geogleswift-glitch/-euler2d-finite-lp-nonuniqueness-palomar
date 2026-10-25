module

public import RequestProject.Euler.TorusBiotSavartKernel
public import RequestProject.Euler.PlanarKernelTranslation
public import RequestProject.Euler.TorusSmoothKernelBounds

/-! The actual torus kernel has a proved `L¹` logarithmic translation modulus. -/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology Metric Real
open scoped ContDiff ENNReal

namespace Euler2D

lemma periodicLocalKernel_add_eq_on_box {x h : R2} (hx : x ∈ torusBox)
    (hh : ‖h‖ ≤ 1 / 2) :
    periodicLocalKernel (x + h) = localPlanarKernel (x + h - torusCenter) := by
  have hz (k : Fin 2 → ℤ) (hk : k ≠ 0) :
      localPlanarKernel (x + h + torusLatticeShift k - torusCenter) = 0 := by
    obtain ⟨i, hi⟩ : ∃ i, k i ≠ 0 := by
      by_contra hn
      push_neg at hn
      exact hk (funext hn)
    have hhi : -(1 / 2 : ℝ) ≤ h i ∧ h i ≤ 1 / 2 :=
      abs_le.mp ((abs_coord_le h i).trans hh)
    have hcoord : (1 : ℝ) ≤ |(x + h + torusLatticeShift k - torusCenter) i| := by
      have hxi := hx i
      have hsplit : k i ≤ -1 ∨ 1 ≤ k i := by omega
      rcases hsplit with hki | hki
      · have hki' : (k i : ℝ) ≤ -1 := by exact_mod_cast hki
        have hs : 2 * π * (k i : ℝ) ≤ -2 * π := by nlinarith [pi_pos]
        simp only [PiLp.sub_apply, PiLp.add_apply, torusLatticeShift_apply, torusCenter_apply]
        rw [abs_of_nonpos (by linarith [pi_gt_three, hhi.2, hxi.2])]
        linarith [pi_gt_three, hhi.2, hxi.2]
      · have hki' : (1 : ℝ) ≤ (k i : ℝ) := by exact_mod_cast hki
        have hs : 2 * π ≤ 2 * π * (k i : ℝ) := by nlinarith [pi_pos]
        simp only [PiLp.sub_apply, PiLp.add_apply, torusLatticeShift_apply, torusCenter_apply]
        rw [abs_of_nonneg (by linarith [pi_gt_three, hhi.1, hxi.1])]
        linarith [pi_gt_three, hhi.1, hxi.1]
    exact localPlanarKernel_eq_zero_of_one_le_norm (hcoord.trans (abs_coord_le _ i))
  change (∑' k, localPlanarKernel (x + h + torusLatticeShift k - torusCenter)) = _
  rw [tsum_eq_single 0 hz, torusLatticeShift_zero, add_zero]

def torusKernelTranslationError (h : R2) : ℝ :=
  ∫ x in torusBox, ‖torusBiotSavartKernel (x + h) - torusBiotSavartKernel x‖

lemma integrable_torusBiotSavartKernel_translation_difference (h : R2) :
    Integrable (fun x => torusBiotSavartKernel (x + h) - torusBiotSavartKernel x) μT := by
  have hi := (torusAreaPreserving_add_right h).integrable_comp_of_integrable
    integrable_torusBiotSavartKernel
  have he : torusBiotSavartKernel ∘ (torusWrap ∘ fun x => x + h) =
      fun x => torusBiotSavartKernel (x + h) := by
    funext x
    exact isTorusPeriodic_torusBiotSavartKernel.eq_torusWrap _
  rw [he] at hi
  exact hi.sub integrable_torusBiotSavartKernel

lemma torusKernelTranslationError_nonneg (h : R2) : 0 ≤ torusKernelTranslationError h :=
  integral_nonneg fun _ => norm_nonneg _

@[simp] lemma torusKernelTranslationError_zero : torusKernelTranslationError 0 = 0 := by
  simp [torusKernelTranslationError]

lemma integral_periodicLocalKernel_translation_le {h : R2} (hh : ‖h‖ ≤ 1 / 2) :
    (∫ x in torusBox, ‖periodicLocalKernel (x + h) - periodicLocalKernel x‖) ≤
      localKernelTranslationError h := by
  have hi : Integrable (fun x => ‖localPlanarKernel (x + h - torusCenter) -
      localPlanarKernel (x - torusCenter)‖) := by
    convert (integrable_norm_localPlanarKernel_translation_difference h).comp_sub_right torusCenter using 1
    funext x
    congr 2
    abel_nf
  calc
    _ = ∫ x in torusBox, ‖localPlanarKernel (x + h - torusCenter) -
        localPlanarKernel (x - torusCenter)‖ := by
      apply setIntegral_congr_fun measurableSet_torusBox
      intro x hx
      dsimp only
      rw [periodicLocalKernel_add_eq_on_box hx hh, periodicLocalKernel_eq_on_box hx]
    _ ≤ ∫ x : R2, ‖localPlanarKernel (x + h - torusCenter) -
        localPlanarKernel (x - torusCenter)‖ :=
      setIntegral_le_integral hi (Eventually.of_forall fun _ => norm_nonneg _)
    _ = localKernelTranslationError h := by
      rw [← integral_add_right_eq_self _ torusCenter]
      simp only [add_sub_cancel_right]
      congr 1
      funext x
      congr 2
      abel_nf

theorem exists_torusKernelTranslationError_le_logFlowModulus :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ h : R2, ‖h‖ ≤ 1 / 2 →
      torusKernelTranslationError h ≤ C * logFlowModulus ‖h‖ := by
  obtain ⟨L, hL, hlocal⟩ := exists_localKernelTranslationError_le_logFlowModulus_half
  obtain ⟨C, _, _, hLip⟩ := exists_torusGreenCorrection_perpGradient_bounds
  refine ⟨L + ((2 * π) ^ 2) * C, by positivity, fun h hh => ?_⟩
  have hIL : Integrable (fun x => ‖periodicLocalKernel (x + h) - periodicLocalKernel x‖) μT := by
    have hi := (torusAreaPreserving_add_right h).integrable_comp_of_integrable
      integrable_periodicLocalKernel
    have he : periodicLocalKernel ∘ (torusWrap ∘ fun x => x + h) =
        fun x => periodicLocalKernel (x + h) := by
      funext x
      exact isTorusPeriodic_periodicLocalKernel.eq_torusWrap _
    rw [he] at hi
    exact (hi.sub integrable_periodicLocalKernel).norm
  have hpt (x : R2) : ‖torusBiotSavartKernel (x + h) - torusBiotSavartKernel x‖ ≤
      ‖periodicLocalKernel (x + h) - periodicLocalKernel x‖ + C * ‖h‖ := by
    have hb := hLip.dist_le_mul (x + h) x
    rw [dist_eq_norm, dist_eq_norm, add_sub_cancel_left] at hb
    change ‖(periodicLocalKernel (x + h) + perpGradient torusGreenCorrection (x + h)) -
      (periodicLocalKernel x + perpGradient torusGreenCorrection x)‖ ≤ _
    rw [add_sub_add_comm]
    exact (norm_add_le _ _).trans (add_le_add (le_refl _) hb)
  have hdmod : ‖h‖ ≤ logFlowModulus ‖h‖ := by
    have hl : log ‖h‖ ≤ 0 := log_nonpos (norm_nonneg h) (by linarith)
    unfold logFlowModulus
    nlinarith [mul_nonpos_of_nonneg_of_nonpos (norm_nonneg h) hl]
  calc
    _ ≤ ∫ x in torusBox, ‖periodicLocalKernel (x + h) - periodicLocalKernel x‖ + C * ‖h‖ :=
      integral_mono (integrable_torusBiotSavartKernel_translation_difference h).norm
        (hIL.add (integrable_const _)) hpt
    _ = (∫ x in torusBox, ‖periodicLocalKernel (x + h) - periodicLocalKernel x‖) +
        ((2 * π) ^ 2) * C * ‖h‖ := by
      rw [integral_add hIL (integrable_const _), integral_const, smul_eq_mul, measureReal_def,
        torus_area_toReal]
      ring
    _ ≤ L * logFlowModulus ‖h‖ + ((2 * π) ^ 2) * C * logFlowModulus ‖h‖ :=
      add_le_add ((integral_periodicLocalKernel_translation_le hh).trans (hlocal h hh))
        (mul_le_mul_of_nonneg_left hdmod (by positivity))
    _ = _ := by ring

theorem tendsto_torusKernelTranslationError_zero :
    Tendsto torusKernelTranslationError (𝓝 (0 : R2)) (𝓝 0) := by
  obtain ⟨C, hC, hbound⟩ := exists_torusKernelTranslationError_le_logFlowModulus
  have hsmall : ∀ᶠ h : R2 in 𝓝 0, ‖h‖ ≤ 1 / 2 := by
    filter_upwards [ball_mem_nhds (0 : R2) (by norm_num : (0 : ℝ) < 1 / 2)] with h hh
    exact (mem_ball_zero_iff.mp hh).le
  have hlim : Tendsto (fun h : R2 => C * logFlowModulus ‖h‖) (𝓝 0) (𝓝 0) := by
    have hc : Continuous (fun h : R2 => C * logFlowModulus ‖h‖) :=
      continuous_const.mul (continuous_logFlowModulus.comp continuous_norm)
    simpa only [norm_zero, logFlowModulus, zero_mul, mul_zero, sub_zero] using hc.tendsto (0 : R2)
  apply squeeze_zero' (Eventually.of_forall torusKernelTranslationError_nonneg) ?_ hlim
  filter_upwards [hsmall] with h hh
  exact hbound h hh

end Euler2D

end
