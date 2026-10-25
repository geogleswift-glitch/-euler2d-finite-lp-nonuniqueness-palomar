module

public import RequestProject.Euler.CircularConstrainedReturnConjugacy

/-! An actual nearby fourfold fixed-area material contour is recovered
from its literal original constrained projection. This is the inverse
identity needed when consecutive actual block endpoints are sampled. -/

@[expose] public section

set_option maxHeartbeats 4000000
set_option maxRecDepth 4000

noncomputable section

open Set Filter Topology Metric
open scoped NNReal

namespace Euler2D

attribute [local instance 2000] returnConjugacyLittle_group returnConjugacyLittle_space
  returnConjugacyFamily_tower returnConjugacyTangent_group returnConjugacyTangent_space
  returnConjugacyTangent_continuousAdd

attribute [local irreducible] circularConstrainedTangentSubmodule circularConstrainedChart
  circularConstraintProjectionToTangentCLM

theorem circularConstrainedChart_projection_actual_of_area {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1) (Z : Fin 2 → LittleContourSpace γ)
    (hfour : ∀ i, Z i ∈ fourfoldLittleContourSubmodule γ)
    (hpos : ∀ i, 0 < 1 + littleAreaRadialCoeffCLM γ (circularContourRadii i)
      (Z i - littleReferenceCircle hγ hγ1.le (circularContourRadii i)))
    (harea : ∀ i, littleContourArea γ (Z i) = Real.pi * circularContourRadii i ^ 2) :
    circularConstrainedChart hγ hγ1
      (circularConstraintProjectionToTangentCLM hγ hγ1.le
        (Z - littleCircularReference hγ hγ1)) = Z := by
  have he : (circularConstraintProjectionToTangentCLM hγ hγ1.le
      (Z - littleCircularReference hγ hγ1)).val = circularAreaChartInverseFamily hγ hγ1 Z := by
    rw [circularConstraintProjectionToTangentCLM_val]
    exact circularConstraintProjection_sub_reference hγ hγ1 Z hfour
  funext i
  unfold circularConstrainedChart
  change littleAreaChart hγ hγ1.le (circularContourRadii i)
    ((circularConstraintProjectionToTangentCLM hγ hγ1.le
      (Z - littleCircularReference hγ hγ1)).val i) = Z i
  rw [congrFun he i]
  exact littleAreaChart_littleAreaChartInverse hγ hγ1.le
    (by fin_cases i <;> simp [circularContourRadii, cellA_pos.ne']) (Z i) (hpos i) (harea i)

theorem exists_circular_actualConstraintChart_radius {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1) :
    ∃ δ > 0, ∀ Z ∈ ball (littleCircularReference hγ hγ1) δ,
      (∀ i, Z i ∈ fourfoldLittleContourSubmodule γ) →
      (∀ i, littleContourArea γ (Z i) = Real.pi * circularContourRadii i ^ 2) →
      circularConstrainedChart hγ hγ1
        (circularConstraintProjectionToTangentCLM hγ hγ1.le
          (Z - littleCircularReference hγ hγ1)) = Z := by
  have hp : ∀ᶠ Z : Fin 2 → LittleContourSpace γ in 𝓝 (littleCircularReference hγ hγ1),
      ∀ i, 0 < 1 + littleAreaRadialCoeffCLM γ (circularContourRadii i)
        (Z i - littleReferenceCircle hγ hγ1.le (circularContourRadii i)) := by
    apply Filter.eventually_all.mpr
    intro i
    let C := littleReferenceCircle hγ hγ1.le (circularContourRadii i)
    let L := littleAreaRadialCoeffCLM γ (circularContourRadii i)
    have hc : Continuous (fun Z : Fin 2 → LittleContourSpace γ => 1 + L (Z i - C)) :=
      continuous_const.add (L.continuous.comp ((continuous_apply i).sub continuous_const))
    exact hc.continuousAt.eventually (eventually_gt_nhds (by
      change 0 < 1 + L (C - C)
      rw [sub_self, map_zero, add_zero]
      norm_num))
  obtain ⟨δ, hδ, hδprop⟩ := Metric.eventually_nhds_iff.mp hp
  exact ⟨δ, hδ, fun Z hZ hfour harea =>
    circularConstrainedChart_projection_actual_of_area hγ hγ1 Z hfour (hδprop hZ) harea⟩

end Euler2D

end
