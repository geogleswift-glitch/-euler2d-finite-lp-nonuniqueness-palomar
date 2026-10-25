module

public import RequestProject.Euler.ContourCircularKernel
public import RequestProject.Euler.ContourBoundaryInvariance

/-! Exact values of the original logarithmic boundary integral for
two concentric circles, including its singular self-interaction. -/

@[expose] public section

noncomputable section

open Complex Set MeasureTheory

namespace Euler2D

theorem contourLogBoundaryIntegral_refCircle_at_real {r s : ℝ}
    (hr : 0 < r) (hs : 0 < s) :
    contourLogBoundaryIntegral (refCircle s) (deriv (refCircle s)) (r : ℂ) =
      -(Real.pi : ℂ) * I * (s : ℂ) * ((min r s / max r s : ℝ) : ℂ) := by
  let f : ℝ → ℂ := fun φ =>
    (Real.log ‖(r : ℂ) - (s : ℂ) * contourCircleCharacter 1 φ‖ : ℂ) *
      contourCircleCharacter 1 φ
  have hp : Function.Periodic f (2 * Real.pi) := by
    intro φ
    dsimp only [f]
    rw [periodic_contourCircleCharacter 1 φ]
  have hperiod := hp.intervalIntegral_add_eq (-Real.pi) 0
  have hπ : (-Real.pi + 2 * Real.pi : ℝ) = Real.pi := by ring
  rw [hπ, zero_add] at hperiod
  have hi : contourLogBoundaryIntegral (refCircle s) (deriv (refCircle s)) (r : ℂ) =
      ((s : ℂ) * I) * ∫ φ in (0 : ℝ)..2 * Real.pi, f φ := by
    rw [contourLogBoundaryIntegral, ← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro φ _
    dsimp only [f]
    rw [deriv_refCircle]
    simp only [refCircle, contourCircleCharacter, Int.cast_one, one_mul, Complex.real_smul]
    ring
  rw [hi, ← hperiod]
  have hm := integral_contourCircular_two_radii_logMode hr hs (m := 1) (by norm_num)
  change (∫ φ in (-Real.pi : ℝ)..Real.pi, f φ) = _ at hm
  rw [hm]
  simp only [pow_one, Nat.cast_one, div_one]
  ring

theorem contourLogBoundaryIntegral_refCircle {r s : ℝ}
    (hr : 0 < r) (hs : 0 < s) (θ : ℝ) :
    contourLogBoundaryIntegral (refCircle s) (deriv (refCircle s)) (refCircle r θ) =
      -(Real.pi : ℂ) * I * (s : ℂ) * ((min r s / max r s : ℝ) : ℂ) *
        exp ((θ : ℂ) * I) := by
  have hu := contourLogBoundaryIntegral_rotShift
    ((contDiff_refCircle s).differentiable (by norm_num)) (periodic_refCircle s) θ (r : ℂ)
  rw [rotShift_refCircle] at hu
  have ht : exp ((θ : ℂ) * I) * (r : ℂ) = refCircle r θ := by
    unfold refCircle
    ring
  rw [ht, contourLogBoundaryIntegral_refCircle_at_real hr hs] at hu
  rw [hu]
  ring

theorem contourCircular_patchBoundaryVelocity {r s : ℝ}
    (hr : 0 < r) (hs : 0 < s) (θ : ℝ) :
    (-1 / (2 * Real.pi) : ℂ) *
      contourLogBoundaryIntegral (refCircle s) (deriv (refCircle s)) (refCircle r θ) =
      I * (((s / 2 * (min r s / max r s) : ℝ) : ℂ)) * exp ((θ : ℂ) * I) := by
  rw [contourLogBoundaryIntegral_refCircle hr hs θ]
  push_cast
  field_simp
  <;> ring

end Euler2D

end
