module

public import RequestProject.Euler.ContourCircularKernel

/-! Integrability and both signs of the actual two-radius logarithmic
Fourier coefficients, including the singular equal-radius case. -/

@[expose] public section

noncomputable section

open Complex Set Filter MeasureTheory
open scoped ComplexConjugate Interval

namespace Euler2D

theorem intervalIntegrable_contourCircular_scaled_logMode {r s : ℝ}
    (hr : 0 < r) (hs : 0 ≤ s) (hsr : s ≤ r) (k : ℤ) :
    IntervalIntegrable (fun θ : ℝ =>
      (Real.log ‖(r : ℂ) - (s : ℂ) * contourCircleCharacter 1 θ‖ : ℂ) *
        contourCircleCharacter k θ) volume (-Real.pi) Real.pi := by
  have hq0 : 0 ≤ s / r := div_nonneg hs hr.le
  have hq1 : s / r ≤ 1 := (div_le_one hr).mpr hsr
  have hc : IntervalIntegrable (fun θ : ℝ => (Real.log r : ℂ) * contourCircleCharacter k θ)
      volume (-Real.pi) Real.pi :=
    (continuous_const.mul (continuous_contourCircleCharacter k)).intervalIntegrable _ _
  have hi := intervalIntegrable_contourCircular_logMode hq0 hq1 k
  apply (hc.add hi).congr_ae
  filter_upwards [ae_restrict_mem measurableSet_uIoc, ae_restrict_of_ae (volume.ae_ne (0 : ℝ))]
    with θ hθ hθ0
  have hab : (-Real.pi : ℝ) ≤ Real.pi := by linarith [Real.pi_pos]
  rw [uIoc_of_le hab] at hθ
  have ha : |θ| ≤ Real.pi := abs_le.mpr ⟨hθ.1.le, hθ.2⟩
  have hn : ‖1 - ((s / r : ℝ) : ℂ) * contourCircleCharacter 1 θ‖ ≠ 0 :=
    (lt_of_lt_of_le (mul_pos (by positivity) (abs_pos.mpr hθ0))
      (contourCircular_radial_chord_lower hq0 hq1 ha)).ne'
  have hf : (r : ℂ) - (s : ℂ) * contourCircleCharacter 1 θ =
      (r : ℂ) * (1 - ((s / r : ℝ) : ℂ) * contourCircleCharacter 1 θ) := by
    push_cast
    field_simp [show (r : ℂ) ≠ 0 by exact_mod_cast hr.ne']
    <;> ring
  rw [hf, norm_mul, Complex.norm_of_nonneg hr.le, Real.log_mul hr.ne' hn,
    Complex.ofReal_add, add_mul]

theorem intervalIntegrable_contourCircular_two_radii_logMode {r s : ℝ}
    (hr : 0 < r) (hs : 0 < s) (k : ℤ) :
    IntervalIntegrable (fun θ : ℝ =>
      (Real.log ‖(r : ℂ) - (s : ℂ) * contourCircleCharacter 1 θ‖ : ℂ) *
        contourCircleCharacter k θ) volume (-Real.pi) Real.pi := by
  by_cases hsr : s ≤ r
  · exact intervalIntegrable_contourCircular_scaled_logMode hr hs.le hsr k
  · have he : (fun θ : ℝ =>
        (Real.log ‖(r : ℂ) - (s : ℂ) * contourCircleCharacter 1 θ‖ : ℂ) * contourCircleCharacter k θ) =
        (fun θ : ℝ =>
          (Real.log ‖(s : ℂ) - (r : ℂ) * contourCircleCharacter 1 θ‖ : ℂ) * contourCircleCharacter k θ) := by
      funext θ
      rw [norm_real_sub_mul_unit_swap r s (norm_contourCircleCharacter 1 θ)]
    rw [he]
    exact intervalIntegrable_contourCircular_scaled_logMode hs hr.le (not_le.mp hsr).le k

theorem integral_contourCircular_two_radii_logMode_negative {r s : ℝ}
    (hr : 0 < r) (hs : 0 < s) {m : ℕ} (hm : 0 < m) :
    (∫ θ in (-Real.pi : ℝ)..Real.pi,
      (Real.log ‖(r : ℂ) - (s : ℂ) * contourCircleCharacter 1 θ‖ : ℂ) *
        contourCircleCharacter (-(m : ℤ)) θ) =
      -(((min r s / max r s : ℝ) : ℂ) ^ m / (m : ℂ)) * (Real.pi : ℂ) := by
  have hc := Complex.conjCLE.toContinuousLinearMap.intervalIntegral_comp_comm
    (intervalIntegrable_contourCircular_two_radii_logMode hr hs (m : ℤ))
  change (∫ θ in (-Real.pi : ℝ)..Real.pi,
    conj ((Real.log ‖(r : ℂ) - (s : ℂ) * contourCircleCharacter 1 θ‖ : ℂ) *
      contourCircleCharacter (m : ℤ) θ)) =
    conj (∫ θ in (-Real.pi : ℝ)..Real.pi,
      (Real.log ‖(r : ℂ) - (s : ℂ) * contourCircleCharacter 1 θ‖ : ℂ) *
        contourCircleCharacter (m : ℤ) θ) at hc
  simp only [map_mul, Complex.conj_ofReal, conj_contourCircleCharacter] at hc
  rw [hc, integral_contourCircular_two_radii_logMode hr hs hm]
  simp only [map_mul, map_neg, map_div₀, map_pow, map_natCast, Complex.conj_ofReal]

end Euler2D

end
