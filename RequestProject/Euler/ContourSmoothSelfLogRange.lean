module

public import RequestProject.Euler.ContourSmoothSelfLog
public import RequestProject.Euler.ContourLogCircle

/-! The literal smooth self-log integral has an actual element of the
little Hölder space as its value.  Its periodic lift is exactly the
original contour integral. -/

@[expose] public section

noncomputable section

open scoped NNReal ContDiff

namespace Euler2D.ContourC1Space

local instance (priority := 2000) selfLogRange_normedAddCommGroup (γ : ℝ≥0) :
    NormedAddCommGroup (ContourC1Space γ) :=
  Submodule.normedAddCommGroup (contourC1GraphSubmodule γ)

local instance (priority := 2000) selfLogRange_normedSpace (γ : ℝ≥0) :
    NormedSpace ℝ (ContourC1Space γ) :=
  Submodule.normedSpace (contourC1GraphSubmodule γ)

variable {γ : ℝ≥0}

theorem contDiff_selfLogIntegral_of_smooth (Z : ContourC1Space γ)
    (hs : ContDiff ℝ ∞ (lift γ Z)) {c : ℝ} (hc : 0 < c) (hZ : HasChordArcLower Z c) :
    ContDiff ℝ ∞ (selfLogIntegral Z) :=
  contDiff_contourSelfIntegral_of_smooth_chord hs hc hZ

/-- An actual little-space value for the actual self-log contour integral. -/
def selfLogLittleOfSmooth (hγ₀ : 0 < γ) (hγ₁ : γ ≤ 1) (Z : ContourC1Space γ)
    (hs : ContDiff ℝ ∞ (lift γ Z)) {c : ℝ} (hc : 0 < c) (hZ : HasChordArcLower Z c) :
    LittleContourSpace γ :=
  littleContourOfPeriodicSmooth hγ₀ hγ₁ (selfLogIntegral Z) (periodic_selfLogIntegral Z)
    (contDiff_selfLogIntegral_of_smooth Z hs hc hZ)

@[simp] theorem lift_selfLogLittleOfSmooth (hγ₀ : 0 < γ) (hγ₁ : γ ≤ 1)
    (Z : ContourC1Space γ) (hs : ContDiff ℝ ∞ (lift γ Z)) {c : ℝ}
    (hc : 0 < c) (hZ : HasChordArcLower Z c) :
    LittleContourSpace.lift γ (selfLogLittleOfSmooth hγ₀ hγ₁ Z hs hc hZ) =
      selfLogIntegral Z := rfl

/-- Any actual C¹ Hölder realization of that same integral lies in the
genuine little closure.  This matches independently constructed operators. -/
theorem mem_little_of_lift_eq_smooth_selfLog (Z W : ContourC1Space γ)
    (hs : ContDiff ℝ ∞ (lift γ Z)) {c : ℝ} (hc : 0 < c) (hZ : HasChordArcLower Z c)
    (hW : lift γ W = selfLogIntegral Z) :
    W ∈ (LittleContourSpace γ : Set (ContourC1Space γ)) := by
  apply (smoothContourSubmodule γ).le_topologicalClosure
  change ContDiff ℝ ∞ (lift γ W)
  rw [hW]
  exact contDiff_selfLogIntegral_of_smooth Z hs hc hZ

end Euler2D.ContourC1Space

end
