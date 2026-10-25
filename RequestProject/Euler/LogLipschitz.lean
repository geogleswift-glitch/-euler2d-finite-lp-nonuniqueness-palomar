module

public import Mathlib
public import RequestProject.Euler.KernelTail
public import RequestProject.Euler.FieldContinuity

/-!
# Log-Lipschitz modulus of the planar velocity (Lemma `bv:kernel`, estimate `bv:loglip`)

For `f ∈ L¹(ℝ²)` with `|f| ≤ M` everywhere and `0 < h = |x − y| ≤ 1/4`,
`|K * f(x) − K * f(y)| ≤ 5 (M + ‖f‖₁) h (1 + log(1/h))` (`velocity_log_lipschitz`).

The proof follows the paper: the kernel difference is split into the region `|x − w| < 2h`
(where each kernel is integrated separately), the annulus `2h ≤ |x − w| < 1` (where
`|K(x−w) − K(y−w)| ≤ h/(π|x−w|²)`), and the far region (bounded kernel).
-/

@[expose] public section

open MeasureTheory Complex ComplexConjugate Set

namespace Euler2D

/-- The annular kernel `|z|⁻² 1_{2h ≤ |z| < 1}`. -/
noncomputable def annKernel (h : ℝ) (z : ℂ) : ℝ := if 2 * h ≤ ‖z‖ ∧ ‖z‖ < 1 then (‖z‖ ^ 2)⁻¹ else 0

lemma annKernel_nonneg (h : ℝ) (z : ℂ) : 0 ≤ annKernel h z := by
  unfold annKernel; split_ifs <;> positivity

lemma truncInvNorm_nonneg (d : ℝ) (z : ℂ) : 0 ≤ truncInvNorm d z := by
  unfold truncInvNorm; split_ifs <;> positivity

/-- Radial profile of the annular kernel. -/
lemma annKernel_aux (h : ℝ) :
    EqOn (fun y : ℝ => y ^ (Module.finrank ℝ ℂ - 1) •
      (if 2 * h ≤ y ∧ y < 1 then (y ^ 2)⁻¹ else 0))
      (indicator (Ico (2 * h) 1) (fun y => y⁻¹)) (Ioi 0) := by
  intro y hy
  have hy0 : 0 < y := hy
  simp only [Complex.finrank_real_complex, smul_eq_mul, indicator, mem_Ico]
  split_ifs
  · rw [show (2 : ℕ) - 1 = 1 from rfl, pow_one]; field_simp
  · simp

lemma Ico_inter_Ioi {h : ℝ} (hh : 0 < h) : Ico (2 * h) 1 ∩ Ioi 0 = Ico (2 * h) 1 :=
  inter_eq_left.mpr fun y hy => lt_of_lt_of_le (by positivity) hy.1

/-- Integrability of the annular kernel. -/
lemma integrable_annKernel {h : ℝ} (hh : 0 < h) : Integrable (annKernel h) := by
  have := (integrable_fun_norm_addHaar (volume : Measure ℂ)
    (f := fun y : ℝ => if 2 * h ≤ y ∧ y < 1 then (y ^ 2)⁻¹ else 0)).mpr ?_
  · exact this
  rw [IntegrableOn, integrable_congr ((ae_restrict_mem measurableSet_Ioi).mono
    fun y hy => annKernel_aux h hy)]
  refine (integrable_indicator_iff measurableSet_Ico).mpr ?_
  rw [IntegrableOn, Measure.restrict_restrict measurableSet_Ico, Ico_inter_Ioi hh]
  exact (ContinuousOn.integrableOn_Icc (continuousOn_inv₀.mono fun y hy =>
    ne_of_gt (lt_of_lt_of_le (by positivity) hy.1))).mono_set Ico_subset_Icc_self

/-- `∫ |z|⁻² 1_{2h ≤ |z| < 1} dz = 2π log(1/(2h))` for `0 < 2h ≤ 1`. -/
lemma integral_annKernel {h : ℝ} (hh : 0 < h) (h1 : 2 * h ≤ 1) :
    ∫ z, annKernel h z = 2 * Real.pi * Real.log (1 / (2 * h)) := by
  have hI := integral_fun_norm_addHaar (volume : Measure ℂ)
    (fun y : ℝ => if 2 * h ≤ y ∧ y < 1 then (y ^ 2)⁻¹ else 0)
  have h2 : (volume : Measure ℂ).real (Metric.ball 0 1) = Real.pi := by
    simp [Measure.real, Complex.volume_ball]
  rw [h2, setIntegral_congr_fun measurableSet_Ioi (annKernel_aux h),
    integral_indicator measurableSet_Ico, Measure.restrict_restrict measurableSet_Ico,
    Ico_inter_Ioi hh, integral_Ico_eq_integral_Ioo, ← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le h1, integral_inv_of_pos (by positivity) one_pos] at hI
  simp only [Complex.finrank_real_complex, smul_eq_mul] at hI
  rw [show annKernel h = fun z => (fun y : ℝ => if 2 * h ≤ y ∧ y < 1 then (y ^ 2)⁻¹ else 0) ‖z‖
    from rfl, hI]
  ring

/-- Pointwise splitting of the kernel difference. -/
lemma kernel_diff_split {x y w : ℂ} (hh : 0 < ‖x - y‖) :
    ‖I * (x - w) / (2 * Real.pi * ‖x - w‖ ^ 2) - I * (y - w) / (2 * Real.pi * ‖y - w‖ ^ 2)‖ ≤
      (truncInvNorm (2 * ‖x - y‖) (x - w) + truncInvNorm (3 * ‖x - y‖) (y - w)) / (2 * Real.pi) +
        ‖x - y‖ / Real.pi * annKernel ‖x - y‖ (x - w) + ‖x - y‖ / Real.pi := by
  have hpi : 0 < Real.pi := Real.pi_pos
  set h := ‖x - y‖ with hhdef
  set a := x - w with ha
  set b := y - w with hb
  have hab : a - b = x - y := by rw [ha, hb]; ring
  have hnab : ‖a - b‖ = h := by rw [hab]
  rw [kernel_eq_inv_conj, kernel_eq_inv_conj]
  have h2 : ‖(2 * (Real.pi : ℂ))‖ = 2 * Real.pi := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpi]; norm_num
  have hK : ∀ z : ℂ, ‖I / (2 * Real.pi) * (conj z)⁻¹‖ = ‖z‖⁻¹ / (2 * Real.pi) := by
    intro z
    rw [norm_mul, norm_div, Complex.norm_I, h2, norm_inv, Complex.norm_conj]; ring
  have hT1 := truncInvNorm_nonneg (2 * h) a
  have hT2 := truncInvNorm_nonneg (3 * h) b
  have hA := annKernel_nonneg h a
  have hhp : 0 ≤ h / Real.pi := by positivity
  by_cases hnear : ‖a‖ < 2 * h
  · have hbnear : ‖b‖ < 3 * h := by
      have : ‖b‖ ≤ ‖a‖ + ‖a - b‖ := by
        calc ‖b‖ = ‖a - (a - b)‖ := by ring_nf
          _ ≤ ‖a‖ + ‖a - b‖ := norm_sub_le _ _
      rw [hnab] at this; linarith
    have e1 : truncInvNorm (2 * h) a = ‖a‖⁻¹ := by simp [truncInvNorm, hnear]
    have e2 : truncInvNorm (3 * h) b = ‖b‖⁻¹ := by simp [truncInvNorm, hbnear]
    calc ‖I / (2 * Real.pi) * (conj a)⁻¹ - I / (2 * Real.pi) * (conj b)⁻¹‖
        ≤ ‖I / (2 * Real.pi) * (conj a)⁻¹‖ + ‖I / (2 * Real.pi) * (conj b)⁻¹‖ := norm_sub_le _ _
      _ = (truncInvNorm (2 * h) a + truncInvNorm (3 * h) b) / (2 * Real.pi) := by
          rw [hK, hK, e1, e2]; ring
      _ ≤ _ := by
          have := mul_nonneg hhp hA
          linarith
  · push_neg at hnear
    have hh0 : 0 < h := hh
    have hapos : 0 < ‖a‖ := by linarith
    have hbge : ‖a‖ / 2 ≤ ‖b‖ := by
      have : ‖a‖ ≤ ‖b‖ + ‖a - b‖ := by
        calc ‖a‖ = ‖b + (a - b)‖ := by ring_nf
          _ ≤ ‖b‖ + ‖a - b‖ := norm_add_le _ _
      rw [hnab] at this; linarith
    have hbpos : 0 < ‖b‖ := by linarith
    have hca : conj a ≠ 0 := (map_ne_zero _).mpr (norm_pos_iff.mp hapos)
    have hcb : conj b ≠ 0 := (map_ne_zero _).mpr (norm_pos_iff.mp hbpos)
    have hdiff : ‖I / (2 * Real.pi) * (conj a)⁻¹ - I / (2 * Real.pi) * (conj b)⁻¹‖ =
        h / (2 * Real.pi * (‖a‖ * ‖b‖)) := by
      rw [← mul_sub, inv_sub_inv hca hcb, show conj b - conj a = conj (b - a) from (map_sub (starRingEnd ℂ) b a).symm,
        norm_mul, norm_div, norm_div, Complex.norm_I, h2, norm_mul, Complex.norm_conj,
        Complex.norm_conj, Complex.norm_conj, norm_sub_rev, hnab]
      field_simp
    have hmain : h / (2 * Real.pi * (‖a‖ * ‖b‖)) ≤ h / Real.pi * (‖a‖ ^ 2)⁻¹ := by
      have hab2 : ‖a‖ ^ 2 / 2 ≤ ‖a‖ * ‖b‖ := by nlinarith
      calc h / (2 * Real.pi * (‖a‖ * ‖b‖)) ≤ h / (2 * Real.pi * (‖a‖ ^ 2 / 2)) :=
            div_le_div_of_nonneg_left hh0.le (by positivity)
              (mul_le_mul_of_nonneg_left hab2 (by positivity))
        _ = h / Real.pi * (‖a‖ ^ 2)⁻¹ := by field_simp
    rw [hdiff]
    refine hmain.trans ?_
    by_cases hfar : ‖a‖ < 1
    · have e3 : annKernel h a = (‖a‖ ^ 2)⁻¹ := by simp [annKernel, hnear, hfar]
      rw [e3]
      have : 0 ≤ (truncInvNorm (2 * h) a + truncInvNorm (3 * h) b) / (2 * Real.pi) := by
        positivity
      linarith
    · push_neg at hfar
      have : (‖a‖ ^ 2)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by nlinarith)
      have h3 : h / Real.pi * (‖a‖ ^ 2)⁻¹ ≤ h / Real.pi := by
        simpa using mul_le_mul_of_nonneg_left this hhp
      have : 0 ≤ (truncInvNorm (2 * h) a + truncInvNorm (3 * h) b) / (2 * Real.pi) := by
        positivity
      have := mul_nonneg hhp hA
      linarith

/-- Integrability of the Biot–Savart integrand for bounded integrable sources. -/
lemma integrable_velocity_integrand {f : ℂ → ℝ} {M : ℝ} (hf : Integrable f)
    (hM : ∀ w, |f w| ≤ M) (z : ℂ) :
    Integrable (fun w => (f w : ℂ) * (I * (z - w) / (2 * Real.pi * ‖z - w‖ ^ 2))) := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have hg : Integrable (fun w => (M * truncInvNorm 1 (z - w) + |f w|) / (2 * Real.pi)) :=
    ((((integrable_truncInvNorm 1).comp_sub_left z).const_mul M).add hf.abs).div_const _
  refine Integrable.mono' hg (aestronglyMeasurable_velocity_integrand hf z)
    (Filter.Eventually.of_forall fun w => ?_)
  rw [norm_velocity_integrand]
  simp only [truncInvNorm]
  rw [div_mul_eq_div_div_swap]
  refine div_le_div_of_nonneg_right ?_ (by positivity)
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  have hdw : 0 ≤ ‖z - w‖ := norm_nonneg _
  split_ifs with hlt
  · rcases eq_or_lt_of_le hdw with h0 | hpos
    · rw [← h0]; simp
    calc |f w| / ‖z - w‖ ≤ M * ‖z - w‖⁻¹ := by
          rw [div_eq_mul_inv]; exact mul_le_mul_of_nonneg_right (hM w) (by positivity)
      _ ≤ _ := le_add_of_nonneg_right (abs_nonneg _)
  · rw [mul_zero, zero_add]
    exact div_le_self (abs_nonneg _) (not_lt.mp hlt)

/-- **Estimate `bv:loglip`.** -/
theorem velocity_log_lipschitz {f : ℂ → ℝ} {M : ℝ} (hf : Integrable f) (hM : ∀ w, |f w| ≤ M)
    {x y : ℂ} (h0 : 0 < ‖x - y‖) (h1 : ‖x - y‖ ≤ 1 / 4) :
    ‖velocityC f x - velocityC f y‖ ≤
      5 * (M + ∫ w, |f w|) * ‖x - y‖ * (1 + Real.log (1 / ‖x - y‖)) := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  set h := ‖x - y‖ with hhdef
  set A := ∫ w, |f w| with hAdef
  have hA0 : 0 ≤ A := integral_nonneg fun w => abs_nonneg _
  set Kx : ℂ → ℂ := fun w => I * (x - w) / (2 * Real.pi * ‖x - w‖ ^ 2) with hKx
  set Ky : ℂ → ℂ := fun w => I * (y - w) / (2 * Real.pi * ‖y - w‖ ^ 2) with hKy
  have hdiff : velocityC f x - velocityC f y = ∫ w, (f w : ℂ) * (Kx w - Ky w) := by
    unfold velocityC
    rw [← integral_sub (integrable_velocity_integrand hf hM x)
      (integrable_velocity_integrand hf hM y)]
    congr 1; funext w; simp only [hKx, hKy]; ring
  set G : ℂ → ℝ := fun w => M / (2 * Real.pi) * truncInvNorm (2 * h) (x - w) +
    M / (2 * Real.pi) * truncInvNorm (3 * h) (y - w) +
    M * h / Real.pi * annKernel h (x - w) + h / Real.pi * |f w| with hG
  have i1 : Integrable (fun w => M / (2 * Real.pi) * truncInvNorm (2 * h) (x - w)) :=
    ((integrable_truncInvNorm _).comp_sub_left x).const_mul _
  have i2 : Integrable (fun w => M / (2 * Real.pi) * truncInvNorm (3 * h) (y - w)) :=
    ((integrable_truncInvNorm _).comp_sub_left y).const_mul _
  have i3 : Integrable (fun w => M * h / Real.pi * annKernel h (x - w)) :=
    ((integrable_annKernel h0).comp_sub_left x).const_mul _
  have i4 : Integrable (fun w => h / Real.pi * |f w|) := hf.abs.const_mul _
  have i12 : Integrable (fun w => M / (2 * Real.pi) * truncInvNorm (2 * h) (x - w) +
      M / (2 * Real.pi) * truncInvNorm (3 * h) (y - w)) := i1.add i2
  have i123 : Integrable (fun w => M / (2 * Real.pi) * truncInvNorm (2 * h) (x - w) +
      M / (2 * Real.pi) * truncInvNorm (3 * h) (y - w) +
      M * h / Real.pi * annKernel h (x - w)) := i12.add i3
  have hGint : Integrable G := i123.add i4
  have hbound : ∀ w, ‖(f w : ℂ) * (Kx w - Ky w)‖ ≤ G w := by
    intro w
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have hk := kernel_diff_split (w := w) h0
    have hT1 := truncInvNorm_nonneg (2 * h) (x - w)
    have hT2 := truncInvNorm_nonneg (3 * h) (y - w)
    have hAk := annKernel_nonneg h (x - w)
    have hP : 0 ≤ (truncInvNorm (2 * h) (x - w) + truncInvNorm (3 * h) (y - w)) / (2 * Real.pi) +
        h / Real.pi * annKernel h (x - w) := by positivity
    have hfw := hM w
    have hfa := abs_nonneg (f w)
    calc |f w| * ‖Kx w - Ky w‖
        ≤ |f w| * ((truncInvNorm (2 * h) (x - w) + truncInvNorm (3 * h) (y - w)) / (2 * Real.pi) +
            h / Real.pi * annKernel h (x - w) + h / Real.pi) :=
          mul_le_mul_of_nonneg_left hk hfa
      _ ≤ M * ((truncInvNorm (2 * h) (x - w) + truncInvNorm (3 * h) (y - w)) / (2 * Real.pi) +
            h / Real.pi * annKernel h (x - w)) + h / Real.pi * |f w| := by
          nlinarith [mul_le_mul_of_nonneg_right hfw hP]
      _ = G w := by simp only [hG]; ring
  have hIG : ∫ w, G w = M * (5 * h + 2 * h * Real.log (1 / (2 * h))) + h / Real.pi * A := by
    have e1 : ∫ w, truncInvNorm (2 * h) (x - w) = 2 * Real.pi * (2 * h) := by
      rw [integral_sub_left_eq_self (fun v => truncInvNorm (2 * h) v)]
      exact integral_truncInvNorm (by positivity)
    have e2 : ∫ w, truncInvNorm (3 * h) (y - w) = 2 * Real.pi * (3 * h) := by
      rw [integral_sub_left_eq_self (fun v => truncInvNorm (3 * h) v)]
      exact integral_truncInvNorm (by positivity)
    have e3 : ∫ w, annKernel h (x - w) = 2 * Real.pi * Real.log (1 / (2 * h)) := by
      rw [integral_sub_left_eq_self (fun v => annKernel h v)]
      exact integral_annKernel h0 (by linarith)
    simp only [hG]
    rw [integral_add i123 i4, integral_add i12 i3, integral_add i1 i2,
      integral_const_mul, integral_const_mul, integral_const_mul, integral_const_mul, e1, e2, e3]
    field_simp
    ring
  have hlog : Real.log (1 / (2 * h)) ≤ Real.log (1 / h) :=
    Real.log_le_log (by positivity) (one_div_le_one_div_of_le h0 (by linarith))
  have hlog0 : 0 ≤ Real.log (1 / h) :=
    Real.log_nonneg (by rw [le_div_iff₀ h0]; linarith)
  rw [hdiff]
  refine (norm_integral_le_of_norm_le hGint (Filter.Eventually.of_forall hbound)).trans ?_
  rw [hIG]
  have hpi1 : 1 ≤ Real.pi := by linarith [Real.pi_gt_three]
  have hAπ : h / Real.pi * A ≤ h * A := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hpi]
    nlinarith [mul_nonneg h0.le hA0]
  nlinarith [mul_nonneg hM0 h0.le, mul_nonneg hA0 h0.le, mul_nonneg (mul_nonneg hM0 h0.le) hlog0,
    mul_nonneg (mul_nonneg hA0 h0.le) hlog0, mul_le_mul_of_nonneg_left hlog (mul_nonneg hM0 h0.le)]

end Euler2D
