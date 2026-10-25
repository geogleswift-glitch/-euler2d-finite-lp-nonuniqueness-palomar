module

public import RequestProject.Euler.ContourTaylor
public import RequestProject.Euler.ContourCauchyIncrement

/-!
# Genuine cancellation of the principal contour pole

The actual Cauchy kernel has leading pole `-1/τ`. Its remainder is
integrable, by the actual derivative Taylor estimate and the true chord
lower bound. No value of a principal value integral is assumed.
-/

@[expose] public section

noncomputable section

open MeasureTheory Complex Set Filter Topology

namespace Euler2D

def contourCauchyPoleIntegrand (z dz : ℝ → ℂ) (θ τ : ℝ) : ℂ :=
  dz (θ + τ) / (z θ - z (θ + τ)) + (τ : ℂ)⁻¹

lemma measurable_contourCauchyPoleIntegrand {z dz : ℝ → ℂ}
    (hz : Measurable z) (hdz : Measurable dz) (θ : ℝ) :
    Measurable (contourCauchyPoleIntegrand z dz θ) :=
  ((hdz.comp (measurable_const.add measurable_id)).div
    (measurable_const.sub (hz.comp (measurable_const.add measurable_id)))).add
      Complex.continuous_ofReal.measurable.inv

theorem norm_contourCauchyPoleIntegrand_le {z dz : ℝ → ℂ} {γ H c θ τ : ℝ}
    (hγ : 0 ≤ γ) (hH : 0 ≤ H) (hc : 0 < c)
    (hz : ∀ s, HasDerivAt z (dz s) s)
    (hd : ∀ s t, ‖dz s - dz t‖ ≤ H * |s - t| ^ γ)
    (hchord : c * |τ| ≤ ‖z θ - z (θ + τ)‖) :
    ‖contourCauchyPoleIntegrand z dz θ τ‖ ≤ (2 * H / c) * |τ| ^ (γ - 1) := by
  by_cases hzero : τ = 0
  · subst τ
    simp only [contourCauchyPoleIntegrand, add_zero, sub_self, div_zero,
      Complex.ofReal_zero, inv_zero, norm_zero]
    exact mul_nonneg (div_nonneg (mul_nonneg (by norm_num) hH) hc.le)
      (Real.rpow_nonneg (abs_nonneg _) _)
  have ht : 0 < |τ| := abs_pos.mpr hzero
  have hden : 0 < ‖z θ - z (θ + τ)‖ := (mul_pos hc ht).trans_le hchord
  have hden0 : z θ - z (θ + τ) ≠ 0 := norm_pos_iff.mp hden
  have htC : (τ : ℂ) ≠ 0 := by exact_mod_cast hzero
  have hTaylor := norm_holder_derivative_taylor hγ hH hz hd θ τ
  rw [Complex.real_smul] at hTaylor
  have hlocal : ‖dz (θ + τ) - dz θ‖ ≤ H * |τ| ^ γ := by
    simpa only [add_sub_cancel_left] using hd (θ + τ) θ
  have hnum : ‖(τ : ℂ) * (dz (θ + τ) - dz θ) -
      (z (θ + τ) - z θ - (τ : ℂ) * dz θ)‖ ≤ 2 * H * |τ| ^ γ * |τ| := by
    calc
      _ ≤ ‖(τ : ℂ) * (dz (θ + τ) - dz θ)‖ +
          ‖z (θ + τ) - z θ - (τ : ℂ) * dz θ‖ := norm_sub_le _ _
      _ = |τ| * ‖dz (θ + τ) - dz θ‖ +
          ‖z (θ + τ) - z θ - (τ : ℂ) * dz θ‖ := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      _ ≤ |τ| * (H * |τ| ^ γ) + (H * |τ| ^ γ) * |τ| :=
        add_le_add (mul_le_mul_of_nonneg_left hlocal ht.le) hTaylor
      _ = _ := by ring
  have he : contourCauchyPoleIntegrand z dz θ τ =
      ((τ : ℂ) * (dz (θ + τ) - dz θ) -
        (z (θ + τ) - z θ - (τ : ℂ) * dz θ)) /
          ((τ : ℂ) * (z θ - z (θ + τ))) := by
    unfold contourCauchyPoleIntegrand
    field_simp [htC, hden0]
    ring
  calc
    _ = ‖(τ : ℂ) * (dz (θ + τ) - dz θ) -
        (z (θ + τ) - z θ - (τ : ℂ) * dz θ)‖ /
          (|τ| * ‖z θ - z (θ + τ)‖) := by
      rw [he, norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    _ ≤ (2 * H * |τ| ^ γ * |τ|) / (|τ| * ‖z θ - z (θ + τ)‖) :=
      div_le_div_of_nonneg_right hnum (mul_nonneg ht.le hden.le)
    _ ≤ (2 * H * |τ| ^ γ * |τ|) / (|τ| * (c * |τ|)) :=
      div_le_div_of_nonneg_left (by positivity) (mul_pos ht (mul_pos hc ht))
        (mul_le_mul_of_nonneg_left hchord ht.le)
    _ = (2 * H / c) * |τ| ^ (γ - 1) := by
      rw [Real.rpow_sub ht, Real.rpow_one]
      field_simp
      <;> ring

theorem integrableOn_contourCauchyPoleIntegrand {z dz : ℝ → ℂ} {γ H c r : ℝ}
    (hzc : Continuous z) (hdzc : Continuous dz) (hγ : 0 < γ) (hH : 0 ≤ H)
    (hc : 0 < c) (hr : 0 ≤ r) (hz : ∀ s, HasDerivAt z (dz s) s)
    (hd : ∀ s t, ‖dz s - dz t‖ ≤ H * |s - t| ^ γ)
    (hchord : ∀ θ τ : ℝ, |τ| ≤ r → c * |τ| ≤ ‖z θ - z (θ + τ)‖) (θ : ℝ) :
    IntegrableOn (contourCauchyPoleIntegrand z dz θ) (Icc (-r) r) := by
  apply ((integrableOn_abs_rpow_sub_one hγ hr).const_mul (2 * H / c)).mono'
    (measurable_contourCauchyPoleIntegrand hzc.measurable hdzc.measurable θ).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Icc] with τ hτ
  exact norm_contourCauchyPoleIntegrand_le hγ.le hH hc hz hd
    (hchord θ τ (abs_le.mpr hτ))

theorem integral_norm_contourCauchyPoleIntegrand_le {z dz : ℝ → ℂ} {γ H c r : ℝ}
    (hzc : Continuous z) (hdzc : Continuous dz) (hγ : 0 < γ) (hH : 0 ≤ H)
    (hc : 0 < c) (hr : 0 ≤ r) (hz : ∀ s, HasDerivAt z (dz s) s)
    (hd : ∀ s t, ‖dz s - dz t‖ ≤ H * |s - t| ^ γ)
    (hchord : ∀ θ τ : ℝ, |τ| ≤ r → c * |τ| ≤ ‖z θ - z (θ + τ)‖) (θ : ℝ) :
    (∫ τ in Icc (-r) r, ‖contourCauchyPoleIntegrand z dz θ τ‖) ≤
      (2 * H / c) * (2 * r ^ γ / γ) := by
  have hi := integrableOn_contourCauchyPoleIntegrand hzc hdzc hγ hH hc hr hz hd hchord θ
  calc
    _ ≤ ∫ τ in Icc (-r) r, (2 * H / c) * |τ| ^ (γ - 1) := by
      apply integral_mono_ae hi.norm ((integrableOn_abs_rpow_sub_one hγ hr).const_mul _)
      filter_upwards [ae_restrict_mem measurableSet_Icc] with τ hτ
      exact norm_contourCauchyPoleIntegrand_le hγ.le hH hc hz hd
        (hchord θ τ (abs_le.mpr hτ))
    _ = _ := by rw [integral_const_mul, integral_abs_rpow_sub_one hγ hr]

end Euler2D

end
