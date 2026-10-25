module

public import RequestProject.Euler.ContourJointSpace
public import RequestProject.Euler.ContourDensityIncrement

/-! A genuinely integrable bilinear remainder kernel on the joint
circle-times-increment Hölder space. -/

@[expose] public section

noncomputable section

open Set Filter Topology MeasureTheory
open scoped NNReal

namespace Euler2D

def contourJointResidualIntegrand {γ : ℝ≥0} (r : ContourJointHolderSpace γ)
    (f : ContourHolderSpace γ) (x : ContourCircle) (τ : ℝ) : ℂ :=
  (τ⁻¹ : ℝ) • ((contourJointSample r x τ - contourJointSample r x 0) * contourDensityIncrement f x τ)

@[simp] theorem contourJointResidualIntegrand_zero {γ : ℝ≥0}
    (r : ContourJointHolderSpace γ) (f : ContourHolderSpace γ) (x : ContourCircle) :
    contourJointResidualIntegrand r f x 0 = 0 := by
  simp only [contourJointResidualIntegrand, inv_zero, zero_smul]

theorem measurable_contourJointResidualIntegrand {γ : ℝ≥0}
    (r : ContourJointHolderSpace γ) (f : ContourHolderSpace γ) (x : ContourCircle) :
    Measurable (contourJointResidualIntegrand r f x) := by
  have hr : Continuous (fun τ : ℝ => contourJointSample r x τ) :=
    (continuous_contourJointSample r).comp (continuous_const.prodMk continuous_id)
  have hf : Continuous (fun τ : ℝ => contourDensityIncrement f x τ) :=
    (continuous_contourDensityIncrement f).comp (continuous_const.prodMk continuous_id)
  exact measurable_inv.smul ((hr.measurable.sub measurable_const).mul hf.measurable)

theorem norm_contourJointResidualIntegrand_le {γ : ℝ≥0}
    (r : ContourJointHolderSpace γ) (f : ContourHolderSpace γ) (x : ContourCircle) (τ : ℝ) :
    ‖contourJointResidualIntegrand r f x τ‖ ≤
      (2 * ‖r‖ * ‖f‖) * |τ| ^ ((γ : ℝ) - 1) := by
  by_cases hτ : τ = 0
  · subst τ
    rw [contourJointResidualIntegrand_zero, norm_zero]
    positivity
  have ht : 0 < |τ| := abs_pos.mpr hτ
  have hr : ‖contourJointSample r x τ - contourJointSample r x 0‖ ≤ 2 * ‖r‖ := by
    exact (norm_sub_le _ _).trans ((add_le_add (norm_contourJointSample_le r x τ)
      (norm_contourJointSample_le r x 0)).trans_eq (by ring))
  rw [contourJointResidualIntegrand, norm_smul, Real.norm_eq_abs, abs_inv, norm_mul]
  calc
    _ ≤ |τ|⁻¹ * ((2 * ‖r‖) * (‖f‖ * |τ| ^ (γ : ℝ))) := by
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr ht.le)
      exact mul_le_mul hr (norm_contourDensityIncrement_le f x τ) (norm_nonneg _) (by positivity)
    _ = _ := by rw [Real.rpow_sub_one ht.ne']; ring

theorem norm_contourJointResidualIntegrand_parameter_sub_le {γ : ℝ≥0}
    (r : ContourJointHolderSpace γ) (f : ContourHolderSpace γ) (x y : ContourCircle)
    (τ : ℝ) (hτπ : |τ| ≤ Real.pi) :
    ‖contourJointResidualIntegrand r f x τ - contourJointResidualIntegrand r f y τ‖ ≤
      (4 * ‖r‖ * ‖f‖ * dist x y ^ (γ : ℝ)) * |τ| ^ ((γ : ℝ) - 1) := by
  by_cases hτ : τ = 0
  · subst τ
    simp only [contourJointResidualIntegrand_zero, sub_self, norm_zero]
    positivity
  have ht : 0 < |τ| := abs_pos.mpr hτ
  let a := contourJointSample r x τ - contourJointSample r x 0
  let b := contourJointSample r y τ - contourJointSample r y 0
  have hab : ‖a - b‖ ≤ 2 * ‖r‖ * dist x y ^ (γ : ℝ) := by
    have he : a - b = (contourJointSample r x τ - contourJointSample r y τ) -
        (contourJointSample r x 0 - contourJointSample r y 0) := by dsimp only [a, b]; ring
    rw [he]
    exact (norm_sub_le _ _).trans ((add_le_add (norm_contourJointSample_sub_theta_le r x y τ)
      (norm_contourJointSample_sub_theta_le r x y 0)).trans_eq (by ring))
  have hb : ‖b‖ ≤ ‖r‖ * |τ| ^ (γ : ℝ) := norm_contourJointSample_sub_zero_le r y τ hτπ
  have he : contourJointResidualIntegrand r f x τ - contourJointResidualIntegrand r f y τ =
      (τ⁻¹ : ℝ) • ((a - b) * contourDensityIncrement f x τ +
        b * (contourDensityIncrement f x τ - contourDensityIncrement f y τ)) := by
    simp only [contourJointResidualIntegrand, ← smul_sub]
    congr 1
    dsimp only [a, b]
    ring
  rw [he, norm_smul, Real.norm_eq_abs, abs_inv]
  calc
    _ ≤ |τ|⁻¹ * (‖a - b‖ * ‖contourDensityIncrement f x τ‖ +
        ‖b‖ * ‖contourDensityIncrement f x τ - contourDensityIncrement f y τ‖) := by
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr ht.le)
      simpa only [norm_mul] using norm_add_le ((a - b) * contourDensityIncrement f x τ)
        (b * (contourDensityIncrement f x τ - contourDensityIncrement f y τ))
    _ ≤ |τ|⁻¹ * (((2 * ‖r‖ * dist x y ^ (γ : ℝ)) * (‖f‖ * |τ| ^ (γ : ℝ))) +
        (‖r‖ * |τ| ^ (γ : ℝ)) * (2 * ‖f‖ * dist x y ^ (γ : ℝ))) := by
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr ht.le)
      exact add_le_add
        (mul_le_mul hab (norm_contourDensityIncrement_le f x τ) (norm_nonneg _) (by positivity))
        (mul_le_mul hb (norm_contourDensityIncrement_parameter_sub_le f x y τ) (norm_nonneg _)
          (by positivity))
    _ = _ := by rw [Real.rpow_sub_one ht.ne']; ring

theorem integrableOn_contourJointResidualIntegrand {γ : ℝ≥0} (hγ : 0 < (γ : ℝ))
    (r : ContourJointHolderSpace γ) (f : ContourHolderSpace γ) (x : ContourCircle) :
    IntegrableOn (contourJointResidualIntegrand r f x) (Icc (-Real.pi) Real.pi) := by
  apply ((integrableOn_abs_rpow_sub_one hγ Real.pi_pos.le).const_mul (2 * ‖r‖ * ‖f‖)).mono'
    (measurable_contourJointResidualIntegrand r f x).aestronglyMeasurable
  exact ae_of_all _ (norm_contourJointResidualIntegrand_le r f x)

def contourJointResidualIntegral {γ : ℝ≥0} (r : ContourJointHolderSpace γ)
    (f : ContourHolderSpace γ) (x : ContourCircle) : ℂ :=
  ∫ τ in Icc (-Real.pi) Real.pi, contourJointResidualIntegrand r f x τ

theorem norm_contourJointResidualIntegral_le {γ : ℝ≥0} (hγ : 0 < (γ : ℝ))
    (r : ContourJointHolderSpace γ) (f : ContourHolderSpace γ) (x : ContourCircle) :
    ‖contourJointResidualIntegral r f x‖ ≤ (2 * ‖r‖ * ‖f‖) *
      (2 * Real.pi ^ (γ : ℝ) / (γ : ℝ)) := by
  calc
    _ ≤ ∫ τ in Icc (-Real.pi) Real.pi, (2 * ‖r‖ * ‖f‖) * |τ| ^ ((γ : ℝ) - 1) :=
      norm_integral_le_of_norm_le
        ((integrableOn_abs_rpow_sub_one hγ Real.pi_pos.le).const_mul _) (ae_of_all _
          (norm_contourJointResidualIntegrand_le r f x))
    _ = _ := by rw [integral_const_mul, integral_abs_rpow_sub_one hγ Real.pi_pos.le]

theorem norm_contourJointResidualIntegral_parameter_sub_le {γ : ℝ≥0} (hγ : 0 < (γ : ℝ))
    (r : ContourJointHolderSpace γ) (f : ContourHolderSpace γ) (x y : ContourCircle) :
    ‖contourJointResidualIntegral r f x - contourJointResidualIntegral r f y‖ ≤
      ((4 * ‖r‖ * ‖f‖) * (2 * Real.pi ^ (γ : ℝ) / (γ : ℝ))) * dist x y ^ (γ : ℝ) := by
  rw [contourJointResidualIntegral, contourJointResidualIntegral,
    ← integral_sub (integrableOn_contourJointResidualIntegrand hγ r f x)
      (integrableOn_contourJointResidualIntegrand hγ r f y)]
  calc
    _ ≤ ∫ τ in Icc (-Real.pi) Real.pi,
        (4 * ‖r‖ * ‖f‖ * dist x y ^ (γ : ℝ)) * |τ| ^ ((γ : ℝ) - 1) := by
      apply norm_integral_le_of_norm_le ((integrableOn_abs_rpow_sub_one hγ Real.pi_pos.le).const_mul _)
      filter_upwards [ae_restrict_mem measurableSet_Icc] with τ hτ
      exact norm_contourJointResidualIntegrand_parameter_sub_le r f x y τ (abs_le.mpr hτ)
    _ = _ := by rw [integral_const_mul, integral_abs_rpow_sub_one hγ Real.pi_pos.le]; ring

end Euler2D

end
