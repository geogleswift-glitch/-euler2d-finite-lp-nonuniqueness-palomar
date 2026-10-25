module

public import RequestProject.Euler.ContourLogCircle
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-! The relative-angle self-integral agrees exactly with the original
boundary integral over one positively oriented parameter period. -/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped NNReal

namespace Euler2D

def contourLogBoundaryIntegral (z dz : ℝ → ℂ) (x : ℂ) : ℂ :=
  ∫ φ in (0 : ℝ)..(2 * Real.pi), Real.log ‖x - z φ‖ • dz φ

theorem contourSelfIntegral_eq_boundaryIntegral (z dz : ℝ → ℂ)
    (hz : Function.Periodic z (2 * Real.pi))
    (hdz : Function.Periodic dz (2 * Real.pi)) (θ : ℝ) :
    contourSelfIntegral z dz θ = contourLogBoundaryIntegral z dz (z θ) := by
  let f : ℝ → ℂ := fun φ => Real.log ‖z θ - z φ‖ • dz φ
  have hp : Function.Periodic f (2 * Real.pi) := by
    intro φ
    dsimp only [f]
    rw [hz φ, hdz φ]
  change (∫ τ in (-Real.pi)..Real.pi, f (θ + τ)) = ∫ φ in (0 : ℝ)..(2 * Real.pi), f φ
  rw [intervalIntegral.integral_comp_add_left]
  have he := hp.intervalIntegral_add_eq (θ - Real.pi) 0
  convert he using 1 <;> congr 1 <;> ring

theorem ContourC1Space.selfLogIntegral_eq_boundaryIntegral {γ : ℝ≥0}
    (Z : ContourC1Space γ) (θ : ℝ) :
    ContourC1Space.selfLogIntegral Z θ =
      contourLogBoundaryIntegral (ContourC1Space.lift γ Z)
        (deriv (ContourC1Space.lift γ Z)) (ContourC1Space.lift γ Z θ) := by
  apply contourSelfIntegral_eq_boundaryIntegral _ _ (ContourC1Space.periodic_lift Z)
  intro t
  rw [ContourC1Space.deriv_lift, ContourC1Space.deriv_lift, AddCircle.coe_add_period]

end Euler2D

end
