module

public import RequestProject.Euler.ContourCircularRadialLimit

/-! The actual circular logarithmic kernel, including equal radii.
All singular equalities below are justified almost everywhere before
the interval integrals are evaluated. -/

@[expose] public section

noncomputable section

open Complex MeasureTheory Set Filter Topology
open scoped Interval

namespace Euler2D

theorem intervalIntegrable_contourCircular_logMode {q : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (k : ℤ) :
    IntervalIntegrable (fun θ : ℝ =>
      (Real.log ‖1 - (q : ℂ) * contourCircleCharacter 1 θ‖ : ℂ) *
        contourCircleCharacter k θ) volume (-Real.pi) Real.pi := by
  let B : ℝ → ℝ := fun θ => |Real.log (1 / Real.pi)| + |Real.log (2 : ℝ)| + |Real.log θ|
  have hab : -Real.pi ≤ Real.pi := by linarith [Real.pi_pos]
  have hB : IntervalIntegrable B volume (-Real.pi) Real.pi :=
    (intervalIntegrable_const).add (intervalIntegral.intervalIntegrable_log').abs
  apply (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mpr
  apply ((intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mp hB).mono'
  · have hn : Continuous (fun θ : ℝ => ‖1 - (q : ℂ) * contourCircleCharacter 1 θ‖) :=
      (continuous_const.sub (continuous_const.mul (continuous_contourCircleCharacter 1))).norm
    exact ((Complex.measurable_ofReal.comp hn.measurable.log).mul
      (continuous_contourCircleCharacter k).measurable).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioc,
      ae_restrict_of_ae (volume.ae_ne (0 : ℝ))] with θ hθ hθ0
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_contourCircleCharacter, mul_one]
    exact contourCircular_radial_log_bound hq0 hq1 (abs_le.mpr ⟨hθ.1.le, hθ.2⟩) hθ0

theorem integral_contourCircular_logMode_closed {q : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) {m : ℕ} (hm : 0 < m) :
    (∫ θ in (-Real.pi : ℝ)..Real.pi,
      (Real.log ‖1 - (q : ℂ) * contourCircleCharacter 1 θ‖ : ℂ) *
        contourCircleCharacter (m : ℤ) θ) =
      -((q : ℂ) ^ m / (m : ℂ)) * (Real.pi : ℂ) := by
  rcases lt_or_eq_of_le hq1 with hlt | rfl
  · exact integral_contourCircular_logNorm_real_symmetric hq0 hlt hm
  · simpa only [Complex.ofReal_one, one_mul, one_pow] using integral_contourCircular_unit_logNorm hm

theorem integral_contourCircleCharacter_symmetric (k : ℤ) :
    (∫ θ in (-Real.pi : ℝ)..Real.pi, contourCircleCharacter k θ) =
      if k = 0 then (2 * Real.pi : ℂ) else 0 := by
  have he := (periodic_contourCircleCharacter k).intervalIntegral_add_eq (-Real.pi) 0
  have hs : (-Real.pi + 2 * Real.pi : ℝ) = Real.pi := by ring
  rw [hs, zero_add] at he
  rw [he, integral_contourCircleCharacter]

theorem integral_contourCircular_scaled_logMode {r s : ℝ}
    (hr : 0 < r) (hs : 0 ≤ s) (hsr : s ≤ r) {m : ℕ} (hm : 0 < m) :
    (∫ θ in (-Real.pi : ℝ)..Real.pi,
      (Real.log ‖(r : ℂ) - (s : ℂ) * contourCircleCharacter 1 θ‖ : ℂ) *
        contourCircleCharacter (m : ℤ) θ) =
      -(((s / r : ℝ) : ℂ) ^ m / (m : ℂ)) * (Real.pi : ℂ) := by
  have hq0 : 0 ≤ s / r := div_nonneg hs hr.le
  have hq1 : s / r ≤ 1 := (div_le_one hr).mpr hsr
  have he : (∫ θ in (-Real.pi : ℝ)..Real.pi,
      (Real.log ‖(r : ℂ) - (s : ℂ) * contourCircleCharacter 1 θ‖ : ℂ) *
        contourCircleCharacter (m : ℤ) θ) =
      ∫ θ in (-Real.pi : ℝ)..Real.pi,
        (Real.log r : ℂ) * contourCircleCharacter (m : ℤ) θ +
          (Real.log ‖1 - ((s / r : ℝ) : ℂ) * contourCircleCharacter 1 θ‖ : ℂ) *
            contourCircleCharacter (m : ℤ) θ := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [volume.ae_ne (0 : ℝ)] with θ hθ0
    intro hθ
    have ha : |θ| ≤ Real.pi := by
      rw [uIoc_of_le (by linarith [Real.pi_pos] : -Real.pi ≤ Real.pi)] at hθ
      exact abs_le.mpr ⟨hθ.1.le, hθ.2⟩
    have hl := contourCircular_radial_chord_lower hq0 hq1 ha
    have hn : ‖1 - ((s / r : ℝ) : ℂ) * contourCircleCharacter 1 θ‖ ≠ 0 :=
      (lt_of_lt_of_le (mul_pos (by positivity) (abs_pos.mpr hθ0)) hl).ne'
    have hf : (r : ℂ) - (s : ℂ) * contourCircleCharacter 1 θ =
        (r : ℂ) * (1 - ((s / r : ℝ) : ℂ) * contourCircleCharacter 1 θ) := by
      push_cast
      field_simp [show (r : ℂ) ≠ 0 by exact_mod_cast hr.ne']
      <;> ring
    rw [hf, norm_mul, Complex.norm_of_nonneg hr.le, Real.log_mul hr.ne' hn,
      Complex.ofReal_add, add_mul]
  rw [he, intervalIntegral.integral_add
    (f := fun θ => (Real.log r : ℂ) * contourCircleCharacter (m : ℤ) θ)
    (g := fun θ =>
      (Real.log ‖1 - ((s / r : ℝ) : ℂ) * contourCircleCharacter 1 θ‖ : ℂ) *
        contourCircleCharacter (m : ℤ) θ)
    ((continuous_const.mul (continuous_contourCircleCharacter (m : ℤ))).intervalIntegrable
      (μ := volume) (-Real.pi) Real.pi)
    (intervalIntegrable_contourCircular_logMode hq0 hq1 (m : ℤ)),
    intervalIntegral.integral_const_mul, integral_contourCircleCharacter_symmetric,
    if_neg (by exact_mod_cast hm.ne'), mul_zero, zero_add]
  exact integral_contourCircular_logMode_closed hq0 hq1 hm

theorem norm_real_sub_mul_unit_swap (r s : ℝ) {z : ℂ} (hz : ‖z‖ = 1) :
    ‖(r : ℂ) - (s : ℂ) * z‖ = ‖(s : ℂ) - (r : ℂ) * z‖ := by
  have hzz : starRingEnd ℂ z * z = 1 := by
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, hz]
    norm_num
  have he : starRingEnd ℂ ((r : ℂ) - (s : ℂ) * z) * z =
      -((s : ℂ) - (r : ℂ) * z) := by
    simp only [map_sub, map_mul, Complex.conj_ofReal]
    rw [sub_mul, mul_assoc, hzz, mul_one]
    ring
  have hn := congrArg norm he
  simpa only [norm_mul, norm_conj, hz, mul_one, norm_neg] using hn

theorem integral_contourCircular_two_radii_logMode {r s : ℝ}
    (hr : 0 < r) (hs : 0 < s) {m : ℕ} (hm : 0 < m) :
    (∫ θ in (-Real.pi : ℝ)..Real.pi,
      (Real.log ‖(r : ℂ) - (s : ℂ) * contourCircleCharacter 1 θ‖ : ℂ) *
        contourCircleCharacter (m : ℤ) θ) =
      -(((min r s / max r s : ℝ) : ℂ) ^ m / (m : ℂ)) * (Real.pi : ℂ) := by
  by_cases hsr : s ≤ r
  · rw [min_eq_right hsr, max_eq_left hsr]
    exact integral_contourCircular_scaled_logMode hr hs.le hsr hm
  · have hrs : r ≤ s := (not_le.mp hsr).le
    rw [min_eq_left hrs, max_eq_right hrs]
    simp_rw [norm_real_sub_mul_unit_swap r s (norm_contourCircleCharacter 1 _)]
    exact integral_contourCircular_scaled_logMode hs hr.le hrs hm

end Euler2D

end
