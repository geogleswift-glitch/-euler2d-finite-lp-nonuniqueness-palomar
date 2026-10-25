module

public import RequestProject.Euler.CircularConstrainedRotation
public import RequestProject.Euler.CircularLocalBackwardGraph
public import RequestProject.Euler.BanachBackwardGraphUniformCommutingInvariance

/-! The SAME original fixed-area weighted backward graph has a common
rotation-invariant germ. This uses actual constrained return covariance
and the same weighted-orbit uniqueness, with no replacement graph. -/

@[expose] public section

set_option maxHeartbeats 400000
set_option maxRecDepth 6000

noncomputable section

open Set Filter Topology Metric
open scoped NNReal ContDiff

namespace Euler2D

attribute [local instance 2000] localGraphLittle_group localGraphLittle_space localGraphFamily_tower
  localGraphTangent_group localGraphTangent_space localGraphTangent_complete localGraphTangent_continuousAdd

attribute [local irreducible] circularConstrainedTangentSubmodule circularConstrainedUnstableProjectionCLM
  circularConstrainedReturnMap circularConstrainedChart circularConstraintProjectionToTangentCLM
  circularConstrainedRotationCLM circularConstrainedUnstableEmbeddingCLM circularConstrainedUnstableCoordinateCLM
  circularBanachField circularBanachDomain littleCircularReference
  contourC1GraphSubmodule holderGraphSubmodule

theorem exists_circularConstrained_backwardGraph_rotation_radius {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1) {R : ℝ} (hR : 0 < R)
    {X : (Fin 2 → LittleContourSpace γ) → ℝ → Fin 2 → LittleContourSpace γ}
    (hX : IsBanachFlowOn (circularBanachField hγ hγ1) (circularBanachDomain hγ hγ1)
      (ball (littleCircularReference hγ hγ1) R) period X)
    (hd : DifferentiableAt ℝ (fun W => X W period) (littleCircularReference hγ hγ1))
    (hfix : X (littleCircularReference hγ hγ1) period = littleCircularReference hγ hγ1)
    {w r : ℝ} (hw : 1 ≤ w) (hr : 0 < r)
    {x : CircularConstrainedTangentSpace γ → ℕ → CircularConstrainedTangentSpace γ}
    (hg : IsLocalWeightedBackwardGraph
      (banachDoubleReturn (circularConstrainedReturnMap hγ hγ1 (fun W => X W period)))
      (circularConstrainedUnstableProjectionCLM hγ hγ1.le) w r x) :
    ∃ η > 0, η ≤ r / 2 ∧ ∀ (b : ℝ) (ξ : CircularConstrainedTangentSpace γ),
      circularConstrainedUnstableProjectionCLM hγ hγ1.le ξ = ξ → ‖ξ‖ ≤ η →
      ‖circularConstrainedUnstableProjectionCLM hγ hγ1.le (circularConstrainedRotationCLM γ b (x ξ 0))‖ ≤ r / 2 ∧
      x (circularConstrainedUnstableProjectionCLM hγ hγ1.le (circularConstrainedRotationCLM γ b (x ξ 0))) =
        (fun n => circularConstrainedRotationCLM γ b (x ξ n)) := by
  apply hg.exists_uniform_commuting_family_invariant_radius_of_double_return
    (G := circularConstrainedReturnMap hγ hγ1 (fun W => X W period))
    (C := 1) hw hr (circularConstrainedUnstableProjectionCLM_idempotent hγ hγ1.le)
    (circularConstrainedReturnMap_zero hγ hγ1 _ hfix)
    (hasFDerivAt_circularConstrainedReturnMap_zero hγ hγ1 hd).continuousAt
    (fun b v => circularConstrainedRotationCLM γ b v) (by norm_num)
  · intro b v
    rw [norm_circularConstrainedRotationCLM, one_mul]
  · exact exists_circularConstrainedReturnMap_rotation_radius hγ hγ1 hR hX

end Euler2D

end
