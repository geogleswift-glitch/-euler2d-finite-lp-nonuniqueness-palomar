module

public import RequestProject.Euler.CircularOrbitNormalFourier

/-! Compactness of the entire genuine circular material reference orbit,
in the original little Banach norm, from its exact time periodicity. -/

@[expose] public section

noncomputable section

open Set
open scoped NNReal ContDiff

namespace Euler2D

local instance (priority := 2000) referenceCompactC1_group (γ : ℝ≥0) :
    NormedAddCommGroup (ContourC1Space γ) := Submodule.normedAddCommGroup (contourC1GraphSubmodule γ)
local instance (priority := 2000) referenceCompactLittle_group (γ : ℝ≥0) :
    NormedAddCommGroup (LittleContourSpace γ) := Submodule.normedAddCommGroup (LittleContourSpace γ)
local instance (priority := 2000) referenceCompactLittle_space (γ : ℝ≥0) :
    NormedSpace ℝ (LittleContourSpace γ) := Submodule.normedSpace (LittleContourSpace γ)

theorem periodic_littleCircularMaterialContours {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1) :
    Function.Periodic (littleCircularMaterialContours hγ hγ1) period := by
  intro t
  funext i
  apply Subtype.ext
  apply ContourC1Space.ext
  intro x
  obtain ⟨θ, rfl⟩ := QuotientAddGroup.mk_surjective x
  change LittleContourSpace.lift γ (littleCircularMaterialContours hγ hγ1 (t + period) i) θ =
    LittleContourSpace.lift γ (littleCircularMaterialContours hγ hγ1 t i) θ
  rw [lift_littleCircularMaterialContours, lift_littleCircularMaterialContours]
  fin_cases i
  · change refCircle cellA (θ + (1 / 2 : ℝ) * (t + period)) =
      refCircle cellA (θ + (1 / 2 : ℝ) * t)
    rw [show θ + (1 / 2 : ℝ) * (t + period) = θ + (1 / 2 : ℝ) * t + 2 * Real.pi by
      unfold period; ring]
    exact periodic_refCircle cellA _
  · change refCircle 1 (θ + 0 * (t + period)) = refCircle 1 (θ + 0 * t)
    simp only [zero_mul, add_zero]

theorem isCompact_range_littleCircularMaterialContours {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1) :
    IsCompact (range (littleCircularMaterialContours hγ hγ1)) :=
  (periodic_littleCircularMaterialContours hγ hγ1).compact_of_continuous
    (by unfold period; positivity) (contDiff_littleCircularMaterialContours hγ hγ1).continuous

end Euler2D

end
