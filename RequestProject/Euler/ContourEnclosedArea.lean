module

public import RequestProject.Euler.ContourEnclosedDomain

/-! The area of the actual constructed near-circle domain equals the
original `loopArea`, by genuine polar integration and the actual angular
change of variables. -/

@[expose] public section

noncomputable section

open Complex Set Filter Topology MeasureTheory intervalIntegral
open scoped ComplexConjugate NNReal

namespace Euler2D

theorem area_nearCircleEnclosedDomain {z dz : ℝ → ℂ} {r ε : ℝ}
    (hr : 0 < r) (hε : 0 ≤ ε) (hsmall : ε ≤ r / 4)
    (hz : ∀ θ, HasDerivAt z (dz θ) θ)
    (hv : ∀ θ, ‖z θ - refCircle r θ‖ ≤ ε)
    (hd : ∀ θ, ‖dz θ - deriv (refCircle r) θ‖ ≤ ε)
    (hdc : Continuous dz) (hp : Function.Periodic z (2 * Real.pi)) :
    volume.real (nearCircleEnclosedDomain hr hε hsmall hz hv hd) = loopArea z := by
  let R := nearCircleRadialProfile hr hε hsmall hz hv hd
  let α := contourAngleLift z r
  let g : ℝ → ℝ := fun φ => R φ ^ 2 / 2
  have hRc : Continuous R := continuous_nearCircleRadialProfile hr hε hsmall hz hv hd
  have hRp : Function.Periodic R (2 * Real.pi) :=
    periodic_nearCircleRadialProfile hr hε hsmall hz hv hd hp
  have hgc : Continuous g := (hRc.pow 2).div_const 2
  have hgp : Function.Periodic g (2 * Real.pi) := by
    intro φ
    dsimp only [g]
    rw [hRp φ]
  have hz0 (θ : ℝ) : z θ ≠ 0 := contour_ne_zero_of_quarter_radius hr hsmall (hv θ)
  have hzc : Continuous z := continuous_iff_continuousAt.mpr (fun θ => (hz θ).continuousAt)
  have hαd (θ : ℝ) : HasDerivAt α (dz θ / z θ).im θ :=
    hasDerivAt_contourAngleLift hr (by linarith) (hv θ) (hz θ)
  have hαdc : Continuous (fun θ => (dz θ / z θ).im) :=
    Complex.continuous_im.comp (hdc.div hzc hz0)
  have hRα (θ : ℝ) : R (α θ) = ‖z θ‖ := by
    change ‖z ((contourAngleOrderIso hr hε hsmall hz hv hd).symm
      ((contourAngleOrderIso hr hε hsmall hz hv hd) θ))‖ = _
    rw [OrderIso.symm_apply_apply]
  have hpoint (θ : ℝ) : (g ∘ α) θ * (dz θ / z θ).im =
      (1 / 2 : ℝ) * contourAngularJacobian z dz θ := by
    dsimp only [Function.comp_def, g]
    rw [hRα θ, im_div_eq_angularJacobian]
    field_simp [norm_ne_zero_iff.mpr (hz0 θ)]
  have hchange := intervalIntegral.integral_comp_mul_deriv
    (a := (0 : ℝ)) (b := 2 * Real.pi) (g := g)
    (fun θ _ => hαd θ) hαdc.continuousOn hgc
  have hend : α (2 * Real.pi) = α 0 + 2 * Real.pi := by
    simpa only [zero_add] using contourAngleLift_add_period hp r 0
  have hperiod := hgp.intervalIntegral_add_eq (α 0) (-Real.pi)
  have hpi : -Real.pi + 2 * Real.pi = Real.pi := by ring
  rw [hpi] at hperiod
  have hset : (∫ φ in Ioo (-Real.pi) Real.pi, g φ) =
      ∫ φ in (-Real.pi)..Real.pi, g φ := by
    rw [intervalIntegral.integral_of_le (by linarith [Real.pi_pos]), integral_Ioc_eq_integral_Ioo]
  rw [area_nearCircleEnclosedDomain_radial hr hε hsmall hz hv hd]
  change (∫ φ in Ioo (-Real.pi) Real.pi, g φ) = _
  rw [hset, ← hperiod, ← hend, ← hchange]
  simp_rw [hpoint]
  rw [intervalIntegral.integral_const_mul]
  unfold loopArea
  congr 2
  funext θ
  rw [(hz θ).deriv]
  rfl

end Euler2D
