module

public import RequestProject.Euler.CircularCanonicalAncientGraphCells
public import RequestProject.Euler.BanachCellAsymptoticAtBot

/-! The entire sufficiently negative canonical trajectory, not only
its discrete samples, lies on the same backward graph in the actual
global material frame. Its literal original unstable coordinate tends
to zero and is continuous on negative time. -/

@[expose] public section

set_option maxHeartbeats 16000000
set_option maxRecDepth 6000

noncomputable section

open Set Filter Topology Metric
open scoped NNReal ContDiff

namespace Euler2D

attribute [local instance 2000] quadraticReferenceC1_group localGraphLittle_group localGraphLittle_space
  localGraphFamily_tower localGraphTangent_group localGraphTangent_space
  localGraphTangent_complete localGraphTangent_continuousAdd

namespace CircularMaterialTransferProfile

variable {γ : ℝ≥0} {hγ : 0 < γ} {hγ1 : (γ : ℝ) < 1} (P : CircularMaterialTransferProfile hγ hγ1)

def coRotatedAncientGraphPoint (t : ℝ) : CircularConstrainedTangentSpace γ :=
  circularConstraintProjectionToTangentCLM hγ hγ1.le
    (circularCoRotationCLM γ t (P.ancient t) - littleCircularReference hγ hγ1)

def coRotatedAncientGraphBase (t : ℝ) : CircularConstrainedTangentSpace γ :=
  circularConstrainedUnstableProjectionCLM hγ hγ1.le (P.coRotatedAncientGraphPoint t)

theorem continuousOn_coRotatedAncientGraphPoint :
    ContinuousOn P.coRotatedAncientGraphPoint (Iic (0 : ℝ)) := by
  unfold coRotatedAncientGraphPoint
  exact (circularConstraintProjectionToTangentCLM hγ hγ1.le).continuous.comp_continuousOn
    ((continuousOn_circularCoRotatedCurve hγ1.le P.ancient_continuous).sub continuousOn_const)

theorem continuousOn_coRotatedAncientGraphBase :
    ContinuousOn P.coRotatedAncientGraphBase (Iic (0 : ℝ)) := by
  unfold coRotatedAncientGraphBase
  exact (circularConstrainedUnstableProjectionCLM hγ hγ1.le).continuous.comp_continuousOn
    P.continuousOn_coRotatedAncientGraphPoint

theorem coRotatedAncientGraphPoint_eq_of_chart (t : ℝ) (v : CircularConstrainedTangentSpace γ)
    (hv : circularConstrainedChart hγ hγ1 v = circularCoRotationCLM γ t (P.ancient t)) :
    P.coRotatedAncientGraphPoint t = v := by
  unfold coRotatedAncientGraphPoint
  rw [← hv]
  exact circularConstrainedChart_projection_left_inverse hγ hγ1 v

attribute [local irreducible] circularBanachField circularBanachDomain circularCoRotationCLM
  littleCircularReference circularConstrainedTangentSubmodule circularConstrainedChart
  circularConstraintProjectionToTangentCLM circularConstrainedReturnMap circularConstrainedUnstableProjectionCLM
  circularCoRotatedConstrainedMap contourC1GraphSubmodule holderGraphSubmodule

theorem exists_ancient_tail_on_same_graph {R r : ℝ} (hR : 0 < R) (hr : 0 < r)
    {X : (Fin 2 → LittleContourSpace γ) → ℝ → Fin 2 → LittleContourSpace γ}
    (hX : IsBanachFlowOn (circularBanachField hγ hγ1) (circularBanachDomain hγ hγ1)
      (ball (littleCircularReference hγ hγ1) R) period X)
    (hd : DifferentiableAt ℝ (fun W => X W period) (littleCircularReference hγ hγ1))
    (hfix : X (littleCircularReference hγ hγ1) period = littleCircularReference hγ hγ1)
    (hareaX : ∀ W ∈ ball (littleCircularReference hγ hγ1) R, ∀ i,
      littleContourArea γ (X W period i) = littleContourArea γ (W i))
    {x : CircularConstrainedTangentSpace γ → ℕ → CircularConstrainedTangentSpace γ}
    (hg : IsLocalWeightedBackwardGraph
      (banachDoubleReturn (circularConstrainedReturnMap hγ hγ1 (fun W => X W period)))
      (circularConstrainedUnstableProjectionCLM hγ hγ1.le) circularAncientBackwardWeight r x)
    (hsamples : ∃ N : ℕ, ∀ n ≥ N, ∃ ξ : CircularConstrainedTangentSpace γ,
      circularConstrainedUnstableProjectionCLM hγ hγ1.le ξ = ξ ∧ ‖ξ‖ ≤ r / 2 ∧
      P.ancient (-(n : ℝ) * (period + period)) = circularConstrainedChart hγ hγ1 (x ξ 0)) :
    ∀ ε > 0, ∃ T ≤ 0, ∀ t ≤ T,
      circularConstrainedUnstableProjectionCLM hγ hγ1.le (P.coRotatedAncientGraphBase t) =
        P.coRotatedAncientGraphBase t ∧
      ‖P.coRotatedAncientGraphBase t‖ ≤ r / 2 ∧ ‖P.coRotatedAncientGraphBase t‖ < ε ∧
      P.coRotatedAncientGraphPoint t = x (P.coRotatedAncientGraphBase t) 0 ∧
      circularConstrainedChart hγ hγ1 (P.coRotatedAncientGraphPoint t) =
        circularCoRotationCLM γ t (P.ancient t) := by
  intro ε hε
  have hp : 0 < period := by unfold period; positivity
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    (P.eventually_ancient_cells_on_same_graph hR hr hX hd hfix hareaX hg hsamples ε hε)
  have hT : -(N : ℝ) * (period + period) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (Nat.cast_nonneg N)) (add_pos hp hp).le
  refine ⟨-(N : ℝ) * (period + period), hT, ?_⟩
  intro t ht
  obtain ⟨n, hn, u, hu, htime⟩ := exists_negative_time_cell (add_pos hp hp) (ht.trans hT) N ht
  obtain ⟨α, hα, hαr, hαε, hchart⟩ := hN (n + 1) (hn.trans (Nat.le_succ n)) u hu
  rw [← htime] at hchart
  have hpoint : P.coRotatedAncientGraphPoint t = x α 0 :=
    P.coRotatedAncientGraphPoint_eq_of_chart t (x α 0) hchart
  have hbase : P.coRotatedAncientGraphBase t = α := by
    unfold coRotatedAncientGraphBase
    rw [hpoint]
    exact hg.coordinate α hα hαr
  rw [hbase]
  refine ⟨hα, hαr, hαε, hpoint, ?_⟩
  rw [hpoint]
  exact hchart

theorem coRotatedAncientGraphBase_tendsto_zero {R r : ℝ} (hR : 0 < R) (hr : 0 < r)
    {X : (Fin 2 → LittleContourSpace γ) → ℝ → Fin 2 → LittleContourSpace γ}
    (hX : IsBanachFlowOn (circularBanachField hγ hγ1) (circularBanachDomain hγ hγ1)
      (ball (littleCircularReference hγ hγ1) R) period X)
    (hd : DifferentiableAt ℝ (fun W => X W period) (littleCircularReference hγ hγ1))
    (hfix : X (littleCircularReference hγ hγ1) period = littleCircularReference hγ hγ1)
    (hareaX : ∀ W ∈ ball (littleCircularReference hγ hγ1) R, ∀ i,
      littleContourArea γ (X W period i) = littleContourArea γ (W i))
    {x : CircularConstrainedTangentSpace γ → ℕ → CircularConstrainedTangentSpace γ}
    (hg : IsLocalWeightedBackwardGraph
      (banachDoubleReturn (circularConstrainedReturnMap hγ hγ1 (fun W => X W period)))
      (circularConstrainedUnstableProjectionCLM hγ hγ1.le) circularAncientBackwardWeight r x)
    (hsamples : ∃ N : ℕ, ∀ n ≥ N, ∃ ξ : CircularConstrainedTangentSpace γ,
      circularConstrainedUnstableProjectionCLM hγ hγ1.le ξ = ξ ∧ ‖ξ‖ ≤ r / 2 ∧
      P.ancient (-(n : ℝ) * (period + period)) = circularConstrainedChart hγ hγ1 (x ξ 0)) :
    Tendsto P.coRotatedAncientGraphBase atBot (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨T, hT, htail⟩ := P.exists_ancient_tail_on_same_graph hR hr hX hd hfix hareaX hg hsamples ε hε
  filter_upwards [eventually_le_atBot T] with t ht
  simpa only [dist_zero_right] using (htail t ht).2.2.1

end CircularMaterialTransferProfile
end Euler2D

end
