module

public import RequestProject.Euler.CircularGrowingMoment
public import RequestProject.Euler.CircularPhaseArea

/-! The genuine boundary formula for the fourth domain moment is
invariant under changes of the contour parameter. Its derivative has
the same covariance. -/

@[expose] public section

noncomputable section

open Complex Set Filter Topology Metric MeasureTheory
open scoped NNReal ContDiff ComplexConjugate

namespace Euler2D

local instance (priority := 2000) fourthShiftC1_group (γ : ℝ≥0) :
    NormedAddCommGroup (ContourC1Space γ) := Submodule.normedAddCommGroup (contourC1GraphSubmodule γ)
local instance (priority := 2000) fourthShiftC1_space (γ : ℝ≥0) :
    NormedSpace ℝ (ContourC1Space γ) := Submodule.normedSpace (contourC1GraphSubmodule γ)

theorem contourFourthMoment_parameterShiftC1 {γ : ℝ≥0} (b : ℝ) (Z : ContourC1Space γ) :
    contourFourthMoment γ (contourParameterShiftC1 b Z) = contourFourthMoment γ Z := by
  have he : ContourC1Space.lift γ (contourParameterShiftC1 b Z) =
      fun θ => ContourC1Space.lift γ Z (θ + b) := funext (lift_contourParameterShiftC1 b Z)
  rw [contourFourthMoment_eq_integral, contourFourthMoment_eq_integral, he]
  congr 1
  have hd : deriv (fun θ => ContourC1Space.lift γ Z (θ + b)) =
      fun θ => deriv (ContourC1Space.lift γ Z) (θ + b) := by
    funext θ
    rw [ContourC1Space.deriv_lift]
    exact ((ContourC1Space.hasDerivAt_lift Z (θ + b)).comp_add_const θ b).deriv
  rw [hd]
  dsimp only
  have hp : Function.Periodic (fun θ =>
      ((ContourC1Space.lift γ Z θ ^ 5).re : ℂ) * deriv (ContourC1Space.lift γ Z) θ)
      (2 * Real.pi) := by
    intro θ
    dsimp only
    rw [ContourC1Space.periodic_lift Z θ, periodic_deriv (ContourC1Space.periodic_lift Z) θ]
  rw [intervalIntegral.integral_comp_add_right (fun θ =>
    ((ContourC1Space.lift γ Z θ ^ 5).re : ℂ) * deriv (ContourC1Space.lift γ Z) θ) b]
  convert hp.intervalIntegral_add_eq (-Real.pi + b) (-Real.pi) using 1 <;> congr 1 <;> ring

theorem fderiv_contourFourthMoment_parameterShiftC1 {γ : ℝ≥0} (b : ℝ)
    (Z V : ContourC1Space γ) :
    fderiv ℝ (contourFourthMoment γ) (contourParameterShiftC1 b Z)
        (contourParameterShiftC1 b V) = fderiv ℝ (contourFourthMoment γ) Z V := by
  have hd (W : ContourC1Space γ) :=
    ((contDiff_contourFourthMoment γ).differentiable (by norm_num)).differentiableAt.hasFDerivAt (x := W)
  have hleft := (hd (contourParameterShiftC1 b Z)).comp Z
    (contourParameterShiftC1CLM γ b).hasFDerivAt
  have he : (fun W : ContourC1Space γ => contourFourthMoment γ (contourParameterShiftC1 b W)) =
      contourFourthMoment γ := funext (contourFourthMoment_parameterShiftC1 b)
  change HasFDerivAt (fun W : ContourC1Space γ => contourFourthMoment γ (contourParameterShiftC1 b W))
    ((fderiv ℝ (contourFourthMoment γ) (contourParameterShiftC1 b Z)).comp
      (contourParameterShiftC1CLM γ b)) Z at hleft
  rw [he] at hleft
  exact congrArg (fun A : ContourC1Space γ →L[ℝ] ℂ => A V) (hleft.unique (hd Z))

end Euler2D

end
