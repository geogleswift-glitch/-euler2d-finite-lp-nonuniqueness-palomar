module

public import RequestProject.Euler.ContourBoundaryIntegralCoordinates
public import RequestProject.Euler.ContourSmoothEmbedding

/-! Actual geometric invariances of the original logarithmic boundary
integral, obtained by pointwise unitary algebra and genuine parameter
translation of a periodic integral. -/

@[expose] public section

noncomputable section

open Complex Set MeasureTheory intervalIntegral

namespace Euler2D

theorem contourLogBoundaryIntegral_mul_unit (z dz : ℝ → ℂ) {a : ℂ}
    (ha : ‖a‖ = 1) (x : ℂ) :
    contourLogBoundaryIntegral (fun φ => a * z φ) (fun φ => a * dz φ) (a * x) =
      a * contourLogBoundaryIntegral z dz x := by
  simp only [contourLogBoundaryIntegral]
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro φ _
  dsimp only
  rw [show a * x - a * z φ = a * (x - z φ) by ring, norm_mul, ha, one_mul]
  simp only [Complex.real_smul]
  ring

theorem contourLogBoundaryIntegral_comp_add (z dz : ℝ → ℂ)
    (hz : Function.Periodic z (2 * Real.pi))
    (hdz : Function.Periodic dz (2 * Real.pi)) (b : ℝ) (x : ℂ) :
    contourLogBoundaryIntegral (fun φ => z (φ + b)) (fun φ => dz (φ + b)) x =
      contourLogBoundaryIntegral z dz x := by
  let f : ℝ → ℂ := fun φ => Real.log ‖x - z φ‖ • dz φ
  have hp : Function.Periodic f (2 * Real.pi) := by
    intro φ
    dsimp only [f]
    rw [hz φ, hdz φ]
  change (∫ φ in (0 : ℝ)..2 * Real.pi, f (φ + b)) = ∫ φ in (0 : ℝ)..2 * Real.pi, f φ
  rw [intervalIntegral.integral_comp_add_right]
  simpa only [zero_add, add_zero, add_comm] using hp.intervalIntegral_add_eq b 0

theorem hasDerivAt_rotShift {z : ℝ → ℂ} {dz : ℂ} (b θ : ℝ)
    (hz : HasDerivAt z dz (θ - b)) :
    HasDerivAt (rotShift b z) (exp ((b : ℂ) * I) * dz) θ := by
  have hh := (hz.scomp θ ((hasDerivAt_id θ).sub_const b)).const_mul (exp ((b : ℂ) * I))
  unfold rotShift
  simpa only [Function.comp_def, id_eq, one_smul] using hh

theorem deriv_rotShift {z : ℝ → ℂ} (hz : Differentiable ℝ z) (b : ℝ) :
    deriv (rotShift b z) = fun θ => exp ((b : ℂ) * I) * deriv z (θ - b) := by
  funext θ
  exact (hasDerivAt_rotShift b θ (hz (θ - b)).hasDerivAt).deriv

theorem contourLogBoundaryIntegral_rotShift {z : ℝ → ℂ} (hz : Differentiable ℝ z)
    (hp : Function.Periodic z (2 * Real.pi)) (b : ℝ) (x : ℂ) :
    contourLogBoundaryIntegral (rotShift b z) (deriv (rotShift b z)) (exp ((b : ℂ) * I) * x) =
      exp ((b : ℂ) * I) * contourLogBoundaryIntegral z (deriv z) x := by
  rw [deriv_rotShift hz]
  change contourLogBoundaryIntegral
    (fun φ => exp ((b : ℂ) * I) * z (φ - b))
    (fun φ => exp ((b : ℂ) * I) * deriv z (φ - b)) (exp ((b : ℂ) * I) * x) = _
  rw [contourLogBoundaryIntegral_mul_unit _ _ (norm_exp_ofReal_mul_I b)]
  congr 1
  simpa only [sub_eq_add_neg] using
    contourLogBoundaryIntegral_comp_add z (deriv z) hp (periodic_deriv_contour hp hz) (-b) x

theorem deriv_shift_eq_I_mul {z : ℝ → ℂ} (hz : Differentiable ℝ z)
    (hrot : ∀ θ, z (θ + Real.pi / 2) = I * z θ) (θ : ℝ) :
    deriv z (θ + Real.pi / 2) = I * deriv z θ := by
  have hleft := ((hz (θ + Real.pi / 2)).hasDerivAt).scomp θ
    ((hasDerivAt_id θ).add_const (Real.pi / 2))
  have he : (fun t => z (t + Real.pi / 2)) = fun t => I * z t := funext hrot
  dsimp only [Function.comp_def, id_eq] at hleft
  rw [he] at hleft
  have hright := ((hz θ).hasDerivAt).const_mul I
  simpa only [one_smul] using hleft.unique hright

theorem contourLogBoundaryIntegral_mul_I_of_fourfold {z : ℝ → ℂ}
    (hz : Differentiable ℝ z) (hp : Function.Periodic z (2 * Real.pi))
    (hrot : ∀ θ, z (θ + Real.pi / 2) = I * z θ) (x : ℂ) :
    contourLogBoundaryIntegral z (deriv z) (I * x) =
      I * contourLogBoundaryIntegral z (deriv z) x := by
  have hshift := contourLogBoundaryIntegral_comp_add z (deriv z) hp
    (periodic_deriv_contour hp hz) (Real.pi / 2) (I * x)
  have hdz : (fun θ => deriv z (θ + Real.pi / 2)) = fun θ => I * deriv z θ :=
    funext (deriv_shift_eq_I_mul hz hrot)
  rw [funext hrot, hdz] at hshift
  rw [← hshift, contourLogBoundaryIntegral_mul_unit _ _ norm_I]

end Euler2D
