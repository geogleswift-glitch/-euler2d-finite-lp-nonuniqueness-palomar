module

public import RequestProject.Euler.CircularActualTorusForcedPeriod
public import RequestProject.Euler.CircularConstrainedReturnMap
public import RequestProject.Euler.BanachFlattenedForcingError

/-! The proved material endpoint error transfers to the literal original
return coordinates by their fixed continuous linear projection. This
estimate does not assert the additional fixed-area inverse-chart identity. -/

@[expose] public section

set_option maxHeartbeats 2500000

noncomputable section

open Set Metric
open scoped NNReal

namespace Euler2D

local instance (priority := 2000) forcedCoordLittle_group (γ : ℝ≥0) :
    NormedAddCommGroup (LittleContourSpace γ) := Submodule.normedAddCommGroup (LittleContourSpace γ)
local instance (priority := 2000) forcedCoordLittle_space (γ : ℝ≥0) :
    NormedSpace ℝ (LittleContourSpace γ) := Submodule.normedSpace (LittleContourSpace γ)
local instance (priority := 2000) forcedCoordFamily_tower (γ : ℝ≥0) :
    IsScalarTower ℝ ℝ (Fin 2 → LittleContourSpace γ) where
  smul_assoc a b Z := by
    funext i
    change (a * b) • Z i = a • (b • Z i)
    exact (smul_smul a b (Z i)).symm
local instance (priority := 2000) forcedCoordTangent_group (γ : ℝ≥0) :
    NormedAddCommGroup (CircularConstrainedTangentSpace γ) :=
      Submodule.normedAddCommGroup (circularConstrainedTangentSubmodule γ)
local instance (priority := 2000) forcedCoordTangent_space (γ : ℝ≥0) :
    NormedSpace ℝ (CircularConstrainedTangentSpace γ) :=
      Submodule.normedSpace (circularConstrainedTangentSubmodule γ)

attribute [local irreducible] circularConstrainedTangentSubmodule
  circularConstraintProjectionToTangentCLM circularConstrainedReturnMap circularConstrainedChart

theorem circularConstrainedReturnMap_difference_le {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1)
    (F G : (Fin 2 → LittleContourSpace γ) → Fin 2 → LittleContourSpace γ)
    (z : CircularConstrainedTangentSpace γ) :
    ‖circularConstrainedReturnMap hγ hγ1 G z - circularConstrainedReturnMap hγ hγ1 F z‖ ≤
      ‖circularConstraintProjectionToTangentCLM hγ hγ1.le‖ *
        dist (G (circularConstrainedChart hγ hγ1 z)) (F (circularConstrainedChart hγ hγ1 z)) := by
  let Q := circularConstraintProjectionToTangentCLM hγ hγ1.le
  have he : circularConstrainedReturnMap hγ hγ1 G z - circularConstrainedReturnMap hγ hγ1 F z =
      Q (G (circularConstrainedChart hγ hγ1 z) - F (circularConstrainedChart hγ hγ1 z)) := by
    unfold circularConstrainedReturnMap
    change Q (_ - _) - Q (_ - _) = Q (_ - _)
    rw [← Q.map_sub]
    congr 1
    abel
  rw [he, dist_eq_norm]
  exact Q.le_opNorm _

theorem circularForcedReturn_coordinate_error {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1)
    (X Y : (Fin 2 → LittleContourSpace γ) → ℝ → Fin 2 → LittleContourSpace γ)
    {ρ δ ε K : ℝ}
    (hcompare : ∀ Z ∈ ball (littleCircularReference hγ hγ1) (min ρ δ),
      dist (Y Z period) (X Z period) ≤ ε * period * Real.exp (K * period))
    (z : CircularConstrainedTangentSpace γ)
    (hz : circularConstrainedChart hγ hγ1 z ∈ ball (littleCircularReference hγ hγ1) (min ρ δ)) :
    ‖circularConstrainedReturnMap hγ hγ1 (fun Z => Y Z period) z -
        circularConstrainedReturnMap hγ hγ1 (fun Z => X Z period) z‖ ≤
      ‖circularConstraintProjectionToTangentCLM hγ hγ1.le‖ *
        (ε * period * Real.exp (K * period)) :=
  (circularConstrainedReturnMap_difference_le hγ hγ1 _ _ z).trans
    (mul_le_mul_of_nonneg_left (hcompare _ hz)
      (norm_nonneg (circularConstraintProjectionToTangentCLM hγ hγ1.le)))

end Euler2D

end
