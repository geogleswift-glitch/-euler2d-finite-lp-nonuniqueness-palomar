module

public import RequestProject.Euler.ContourHilbertNearFar

/-! # Actual endpoint strips and constant cancellation for Hilbert translations -/

@[expose] public section

noncomputable section

open Set MeasureTheory Filter Topology Real
open scoped NNReal Interval

namespace Euler2D

theorem norm_hilbertIncrementIntegrand_le_of_abs_lower
    {f : ℝ → ℂ} {θ s M δ : ℝ} (hM0 : 0 ≤ M) (hδ : 0 < δ)
    (hden : δ ≤ |s|) (hM : ∀ t, ‖f t‖ ≤ M) :
    ‖hilbertIncrementIntegrand f θ s‖ ≤ 2 * M / δ := by
  have hn : ‖f (θ + s) - f θ‖ ≤ 2 * M :=
    (norm_sub_le _ _).trans (by linarith [hM (θ + s), hM θ])
  rw [hilbertIncrementIntegrand, norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
    ← div_eq_inv_mul]
  exact div_le_div₀ (by positivity) hn hδ hden

theorem norm_hilbert_negative_endpoint_le {f : ℝ → ℂ} {θ h P M : ℝ}
    (hP : 0 < P) (hh : 0 < h) (hsmall : h ≤ P / 4)
    (hM0 : 0 ≤ M) (hM : ∀ t, ‖f t‖ ≤ M) :
    ‖∫ s in (-P)..(h - P), hilbertIncrementIntegrand f θ s‖ ≤ (4 * M / P) * h := by
  have hbound : ∀ s ∈ Ι (-P) (h - P), ‖hilbertIncrementIntegrand f θ s‖ ≤ 4 * M / P := by
    intro s hs
    rw [uIoc_of_le (by linarith : -P ≤ h - P)] at hs
    have hd : P / 2 ≤ |s| := by linarith [hs.2, neg_le_abs s]
    have hb := norm_hilbertIncrementIntegrand_le_of_abs_lower hM0
      (by positivity : 0 < P / 2) hd hM (θ := θ)
    convert hb using 1; ring
  have hi := intervalIntegral.norm_integral_le_of_norm_le_const hbound
  rwa [show h - P - -P = h by ring, abs_of_pos hh] at hi

theorem norm_hilbert_positive_endpoint_le {f : ℝ → ℂ} {θ h P M : ℝ}
    (hP : 0 < P) (hh : 0 < h) (hsmall : h ≤ P / 4)
    (hM0 : 0 ≤ M) (hM : ∀ t, ‖f t‖ ≤ M) :
    ‖∫ s in P..(P + h), translatedHilbertIncrementIntegrand f θ h s‖ ≤ (4 * M / P) * h := by
  have hbound : ∀ s ∈ Ι P (P + h),
      ‖translatedHilbertIncrementIntegrand f θ h s‖ ≤ 4 * M / P := by
    intro s hs
    rw [uIoc_of_le (by linarith : P ≤ P + h)] at hs
    have hd : P / 2 ≤ |s - h| := by linarith [hs.1, le_abs_self (s - h)]
    rw [translatedHilbertIncrementIntegrand_eq]
    have hb := norm_hilbertIncrementIntegrand_le_of_abs_lower hM0
      (by positivity : 0 < P / 2) hd hM (θ := θ + h)
    convert hb using 1; ring
  have hi := intervalIntegral.norm_integral_le_of_norm_le_const hbound
  rwa [show P + h - P = h by ring, abs_of_pos hh] at hi

theorem norm_hilbert_endpoint_difference_le {f : ℝ → ℂ} {θ h P M : ℝ}
    (hP : 0 < P) (hh : 0 < h) (hsmall : h ≤ P / 4)
    (hM0 : 0 ≤ M) (hM : ∀ t, ‖f t‖ ≤ M) :
    ‖(∫ s in P..(P + h), translatedHilbertIncrementIntegrand f θ h s) -
        (∫ s in (-P)..(h - P), hilbertIncrementIntegrand f θ s)‖ ≤
      (8 * M / P) * h := by
  calc
    _ ≤ _ := norm_sub_le _ _
    _ ≤ _ := add_le_add (norm_hilbert_positive_endpoint_le hP hh hsmall hM0 hM)
      (norm_hilbert_negative_endpoint_le hP hh hsmall hM0 hM)
    _ = _ := by ring

/-- Complex-vector version of the exact common-far constant cancellation. -/
theorem norm_hilbert_common_far_constant_le {P h : ℝ} (v : ℂ)
    (hP : 0 < P) (hh : 0 < h) (hsmall : h ≤ P / 4) :
    ‖(∫ s in (h - P)..(-2 * h), ((s - h : ℝ) : ℂ)⁻¹ * v) +
        (∫ s in (2 * h)..P, ((s - h : ℝ) : ℂ)⁻¹ * v)‖ ≤ Real.log 3 * ‖v‖ := by
  simp_rw [← Complex.ofReal_inv]
  rw [intervalIntegral.integral_mul_const, intervalIntegral.integral_mul_const,
    intervalIntegral.integral_ofReal, intervalIntegral.integral_ofReal,
    ← add_mul, ← Complex.ofReal_add, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right (abs_integral_common_far_reciprocal_le hP hh hsmall)
    (norm_nonneg v)

end Euler2D

end
