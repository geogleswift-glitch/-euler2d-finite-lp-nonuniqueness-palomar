module

public import RequestProject.Euler.ContourCircularLogFourier
public import RequestProject.Euler.ContourLogKernel
public import RequestProject.Euler.ContourChordArc

/-! A common integrable logarithmic bound for radial approach to the
singular unit-circle kernel. -/

@[expose] public section

noncomputable section

open Complex MeasureTheory Set

namespace Euler2D

theorem periodic_contourCircleCharacter (k : ℤ) :
    Function.Periodic (contourCircleCharacter k) (2 * Real.pi) := by
  intro θ
  unfold contourCircleCharacter
  rw [show (k : ℂ) * ((θ + 2 * Real.pi : ℝ) : ℂ) * I =
    (k : ℂ) * (θ : ℂ) * I + (k : ℂ) * (2 * Real.pi * I) by push_cast; ring]
  rw [exp_add, exp_int_mul_two_pi_mul_I, mul_one]

theorem norm_unit_sub_le_two_radial {z : ℂ} (hz : ‖z‖ = 1) {q : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) : ‖1 - z‖ ≤ 2 * ‖1 - (q : ℂ) * z‖ := by
  have hn := norm_sub_norm_le (1 : ℂ) ((q : ℂ) * z)
  simp only [norm_one, norm_mul, Complex.norm_of_nonneg hq0, hz, mul_one] at hn
  have he : (q : ℂ) * z - z = ((q - 1 : ℝ) : ℂ) * z := by push_cast; ring
  have hd : ‖(q : ℂ) * z - z‖ = 1 - q := by
    rw [he, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonpos (by linarith), hz, mul_one]
    ring
  have ht := norm_sub_le_norm_sub_add_norm_sub (1 : ℂ) ((q : ℂ) * z) z
  rw [hd] at ht
  linarith

theorem contourCircular_radial_chord_lower {q τ : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hτ : |τ| ≤ Real.pi) :
    (1 / Real.pi) * |τ| ≤ ‖1 - (q : ℂ) * contourCircleCharacter 1 τ‖ := by
  have hb := refCircle_chord_lower (r := (1 : ℝ)) (θ := (0 : ℝ)) (φ := τ)
    zero_le_one (by simpa only [zero_sub, abs_neg] using hτ)
  have hc : (2 / Real.pi) * |τ| ≤ ‖1 - contourCircleCharacter 1 τ‖ := by
    simpa [refCircle, contourCircleCharacter] using hb
  have hd := norm_unit_sub_le_two_radial (norm_contourCircleCharacter 1 τ) hq0 hq1
  have he : (2 / Real.pi) * |τ| = 2 * ((1 / Real.pi) * |τ|) := by ring
  rw [he] at hc
  linarith

theorem contourCircular_radial_log_bound {q τ : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hτ : |τ| ≤ Real.pi) (hτ0 : τ ≠ 0) :
    |Real.log ‖1 - (q : ℂ) * contourCircleCharacter 1 τ‖| ≤
      |Real.log (1 / Real.pi)| + |Real.log (2 : ℝ)| + |Real.log τ| := by
  have hu : ‖1 - (q : ℂ) * contourCircleCharacter 1 τ‖ ≤ 2 := by
    have hb := norm_sub_le (1 : ℂ) ((q : ℂ) * contourCircleCharacter 1 τ)
    simp only [norm_one, norm_mul, Complex.norm_of_nonneg hq0,
      norm_contourCircleCharacter, mul_one] at hb
    linarith
  have hb := abs_log_le_of_mul_lower (show 0 < 1 / Real.pi by positivity)
    (abs_pos.mpr hτ0) (contourCircular_radial_chord_lower hq0 hq1 hτ) hu
  rw [Real.log_abs] at hb
  linarith

theorem integral_contourCircular_logNorm_real_symmetric {q : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q < 1) {m : ℕ} (hm : 0 < m) :
    (∫ θ in (-Real.pi : ℝ)..Real.pi,
      (Real.log ‖1 - (q : ℂ) * contourCircleCharacter 1 θ‖ : ℂ) *
        contourCircleCharacter (m : ℤ) θ) =
      -((q : ℂ) ^ m / (m : ℂ)) * (Real.pi : ℂ) := by
  have hp : Function.Periodic (fun θ : ℝ =>
      (Real.log ‖1 - (q : ℂ) * contourCircleCharacter 1 θ‖ : ℂ) *
        contourCircleCharacter (m : ℤ) θ) (2 * Real.pi) := by
    intro θ
    dsimp only
    rw [periodic_contourCircleCharacter 1 θ, periodic_contourCircleCharacter (m : ℤ) θ]
  have he := hp.intervalIntegral_add_eq (-Real.pi) 0
  have hs : (-Real.pi + 2 * Real.pi : ℝ) = Real.pi := by ring
  rw [hs, zero_add] at he
  rw [he]
  exact integral_contourCircular_logNorm_real_positive hq0 hq1 hm

end Euler2D

end
