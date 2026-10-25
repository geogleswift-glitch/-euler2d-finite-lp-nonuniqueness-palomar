module

public import RequestProject.Euler.ContourDomainTransport
public import RequestProject.Euler.ContourFourthMomentParameterShift

/-! The actual enclosed domain is intrinsic to the contour image.
Its radial-fill description is independent of every material
parameter shift, including overlaps of all circular phase charts. -/

@[expose] public section

set_option maxHeartbeats 1800000

noncomputable section

open Complex Set Filter Topology MeasureTheory Metric
open scoped NNReal

namespace Euler2D

local instance (priority := 2000) phaseDomainC1_group (γ : ℝ≥0) :
    NormedAddCommGroup (ContourC1Space γ) := Submodule.normedAddCommGroup (contourC1GraphSubmodule γ)
local instance (priority := 2000) phaseDomainC1_space (γ : ℝ≥0) :
    NormedSpace ℝ (ContourC1Space γ) := Submodule.normedSpace (contourC1GraphSubmodule γ)

theorem range_lift_contourParameterShiftC1 {γ : ℝ≥0} (b : ℝ) (Z : ContourC1Space γ) :
    range (ContourC1Space.lift γ (contourParameterShiftC1 b Z)) = range (ContourC1Space.lift γ Z) := by
  ext x
  constructor
  · rintro ⟨θ, rfl⟩
    exact ⟨θ + b, (lift_contourParameterShiftC1 b Z θ).symm⟩
  · rintro ⟨θ, rfl⟩
    exact ⟨θ - b, by rw [lift_contourParameterShiftC1, sub_add_cancel]⟩

theorem contourRadialFill_parameterShiftC1 {γ : ℝ≥0} (b : ℝ) (Z : ContourC1Space γ) :
    contourRadialFill (ContourC1Space.lift γ (contourParameterShiftC1 b Z)) =
      contourRadialFill (ContourC1Space.lift γ Z) :=
  contourRadialFill_eq_of_range_eq (range_lift_contourParameterShiftC1 b Z)

section Geometry

variable {γ : ℝ≥0} (Z Z₀ : ContourC1Space γ) {r : ℝ} (hr : 0 < r)
  (href : ContourC1Space.lift γ Z₀ = refCircle r) (b : ℝ)
  (hsmall : ‖contourParameterShiftC1 b Z - Z₀‖ ≤ r / 4)

include hr href hsmall

theorem contourRadialFill_eq_enclosedDomain_of_shift :
    contourRadialFill (ContourC1Space.lift γ Z) =
      contourC1EnclosedDomain (contourParameterShiftC1 b Z) Z₀ hr href hsmall := by
  rw [contourC1EnclosedDomain_eq_radialFill, contourRadialFill_parameterShiftC1]

theorem isOpen_contourRadialFill_of_shift : IsOpen (contourRadialFill (ContourC1Space.lift γ Z)) := by
  rw [contourRadialFill_eq_enclosedDomain_of_shift Z Z₀ hr href b hsmall]
  exact isOpen_contourC1EnclosedDomain _ _ _ _ _

theorem frontier_contourRadialFill_of_shift :
    frontier (contourRadialFill (ContourC1Space.lift γ Z)) = range (ContourC1Space.lift γ Z) := by
  rw [contourRadialFill_eq_enclosedDomain_of_shift Z Z₀ hr href b hsmall,
    frontier_contourC1EnclosedDomain, range_lift_contourParameterShiftC1]

theorem norm_lt_of_mem_contourRadialFill_of_shift {x : ℂ}
    (hx : x ∈ contourRadialFill (ContourC1Space.lift γ Z)) : ‖x‖ < 5 * r / 4 := by
  rw [contourRadialFill_eq_enclosedDomain_of_shift Z Z₀ hr href b hsmall] at hx
  have hb := mem_ball_zero_iff.mp (contourC1EnclosedDomain_subset_ball _ _ hr href hsmall hx)
  linarith

theorem area_contourRadialFill_of_shift :
    volume.real (contourRadialFill (ContourC1Space.lift γ Z)) = contourArea γ Z := by
  rw [contourRadialFill_eq_enclosedDomain_of_shift Z Z₀ hr href b hsmall,
    area_contourC1EnclosedDomain]
  exact contourArea_parameterShiftC1 b Z

theorem momentJ_contourRadialFill_four_of_shift :
    momentJ (contourRadialFill (ContourC1Space.lift γ Z)) 4 = contourFourthMoment γ Z := by
  rw [contourRadialFill_eq_enclosedDomain_of_shift Z Z₀ hr href b hsmall,
    momentJ_contourC1EnclosedDomain_four]
  exact contourFourthMoment_parameterShiftC1 b Z

end Geometry

end Euler2D

end
