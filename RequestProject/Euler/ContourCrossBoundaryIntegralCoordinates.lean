module

public import RequestProject.Euler.ContourCrossLogLittle
public import RequestProject.Euler.ContourBoundaryIntegralCoordinates

/-! # Exact source-period coordinates for the actual cross interaction -/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped NNReal

namespace Euler2D

theorem contourCrossLogIntegral_eq_boundaryIntegral (z w dw : ℝ → ℂ)
    (hw : Function.Periodic w (2 * Real.pi))
    (hdw : Function.Periodic dw (2 * Real.pi)) (θ : ℝ) :
    contourCrossLogIntegral z w dw θ = contourLogBoundaryIntegral w dw (z θ) := by
  rw [contourCrossLogIntegral_eq_intervalIntegral]
  let f : ℝ → ℂ := fun φ => Real.log ‖z θ - w φ‖ • dw φ
  have hp : Function.Periodic f (2 * Real.pi) := by
    intro φ
    dsimp only [f]
    rw [hw φ, hdw φ]
  change (∫ φ in (-Real.pi)..Real.pi, f φ) = ∫ φ in (0 : ℝ)..(2 * Real.pi), f φ
  have he := hp.intervalIntegral_add_eq (-Real.pi) 0
  convert he using 1 <;> congr 1 <;> ring

theorem contourC1CrossLogIntegral_eq_boundaryIntegral {γ : ℝ≥0}
    (Z W : ContourC1Space γ) (θ : ℝ) :
    contourC1CrossLogIntegral Z W θ =
      contourLogBoundaryIntegral (ContourC1Space.lift γ W)
        (deriv (ContourC1Space.lift γ W)) (ContourC1Space.lift γ Z θ) := by
  apply contourCrossLogIntegral_eq_boundaryIntegral _ _ _ (ContourC1Space.periodic_lift W)
  intro t
  rw [ContourC1Space.deriv_lift, ContourC1Space.deriv_lift, AddCircle.coe_add_period]

theorem contourCrossLogLittle_eq_boundaryIntegral {γ : ℝ≥0} (hγ1 : (γ : ℝ) ≤ 1)
    (Z W : LittleContourSpace γ) {σ : ℝ} (hσ : 0 < σ)
    (hsep : ContourCrossSeparated Z.val W.val σ) (θ : ℝ) :
    LittleContourSpace.lift γ (contourCrossLogLittle hγ1 Z W hσ hsep) θ =
      contourLogBoundaryIntegral (LittleContourSpace.lift γ W)
        (deriv (LittleContourSpace.lift γ W)) (LittleContourSpace.lift γ Z θ) := by
  rw [lift_contourCrossLogLittle]
  exact contourC1CrossLogIntegral_eq_boundaryIntegral Z.val W.val θ

theorem contourCrossLogLittleOnLocus_eq_boundaryIntegral {γ : ℝ≥0} (hγ1 : (γ : ℝ) ≤ 1)
    (p : PositiveSeparatedLittleContourPair γ) (θ : ℝ) :
    LittleContourSpace.lift γ (contourCrossLogLittleOnLocus hγ1 p) θ =
      contourLogBoundaryIntegral (LittleContourSpace.lift γ p.val.2)
        (deriv (LittleContourSpace.lift γ p.val.2)) (LittleContourSpace.lift γ p.val.1 θ) := by
  rw [lift_contourCrossLogLittleOnLocus]
  exact contourC1CrossLogIntegral_eq_boundaryIntegral p.val.1.val p.val.2.val θ

end Euler2D

end
