module

public import RequestProject.Euler.CircularCanonicalAncientGraphTail
public import RequestProject.Euler.CircularUnstableRotationPhase
public import RequestProject.Euler.CircularFlattenedAncientCaptureSeed

/-! A genuine fixed canonical section of the same original ancient
curve. The section time is chosen before all points at its prescribed
growing-coordinate norm; one constant rotation aligns each such point. -/

@[expose] public section

set_option maxHeartbeats 24000000
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

theorem coRotatedAncientGraphBase_negative_grid (n : ℕ) :
    P.coRotatedAncientGraphBase (-(n : ℝ) * (period + period)) =
      circularConstrainedUnstableProjectionCLM hγ hγ1.le
        (circularConstraintProjectionToTangentCLM hγ hγ1.le
          (P.ancient (-(n : ℝ) * (period + period)) - littleCircularReference hγ hγ1)) := by
  unfold coRotatedAncientGraphBase coRotatedAncientGraphPoint
  rw [circularCoRotationCLM_negative_double_grid]

attribute [local irreducible] circularBanachField circularBanachDomain circularCoRotationCLM
  littleCircularReference circularConstrainedTangentSubmodule circularConstrainedChart
  circularConstraintProjectionToTangentCLM circularConstrainedReturnMap circularConstrainedUnstableProjectionCLM
  circularConstrainedRotationCLM circularCoRotatedConstrainedMap contourC1GraphSubmodule holderGraphSubmodule

theorem exists_same_graph_fixed_canonical_section {R r : ℝ} (hR : 0 < R) (hr : 0 < r)
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
    ∃ d > 0, d ≤ r / 2 ∧ ∀ δ ∈ Ioo (0 : ℝ) d, ∃ s < 0,
      ‖P.coRotatedAncientGraphBase s‖ = δ ∧
      P.coRotatedAncientGraphPoint s = x (P.coRotatedAncientGraphBase s) 0 ∧
      ∀ ξ : CircularConstrainedTangentSpace γ,
        circularConstrainedUnstableProjectionCLM hγ hγ1.le ξ = ξ → ‖ξ‖ = δ →
        ∃ b : ℝ, x ξ 0 = circularConstrainedRotationCLM γ b (P.coRotatedAncientGraphPoint s) ∧
          circularConstrainedChart hγ hγ1 (x ξ 0) =
            contourRotationFamilyLittleCLM γ b (circularCoRotationCLM γ s (P.ancient s)) := by
  have hw : 1 ≤ circularAncientBackwardWeight := by linarith [circularAncientBackwardWeight_bounds.1]
  obtain ⟨η, hη, hηr, hphase⟩ := exists_same_circularBackwardGraph_phase_alignment_radius
    hγ hγ1 hR hX hd hfix hw hr hg
  obtain ⟨T, hT, htail⟩ := P.exists_ancient_tail_on_same_graph hR hr hX hd hfix hareaX hg hsamples η hη
  have hlim := P.coRotatedAncientGraphBase_tendsto_zero hR hr hX hd hfix hareaX hg hsamples
  have hp : 0 < period := by unfold period; positivity
  have hclock : Tendsto (fun n : ℕ => -(n : ℝ) * (period + period)) atTop atBot := by
    have hh : Tendsto (fun n : ℕ => (n : ℝ) * (period + period)) atTop atTop :=
      (tendsto_mul_const_atTop_of_pos (add_pos hp hp)).mpr tendsto_natCast_atTop_atTop
    simpa only [Function.comp_def, neg_mul] using tendsto_neg_atTop_atBot.comp hh
  have hseed := P.ancient_flattened_samples_eventually_seed hg hsamples (by norm_num : (0 : ℝ) < 1)
  obtain ⟨n, hnseed, hnclock⟩ :=
    (hseed.and (hclock.eventually (eventually_le_atBot (min T (-1))))).exists
  let btime := -(n : ℝ) * (period + period)
  have hbT : btime ≤ T := hnclock.trans (min_le_left _ _)
  have hbneg : btime < 0 := (hnclock.trans (min_le_right _ _)).trans_lt (by norm_num)
  have hbpos : 0 < ‖P.coRotatedAncientGraphBase btime‖ := by
    change 0 < ‖P.coRotatedAncientGraphBase (-(n : ℝ) * (period + period))‖
    rw [P.coRotatedAncientGraphBase_negative_grid]
    exact hnseed.2.1
  let d := ‖P.coRotatedAncientGraphBase btime‖
  have hdr : d ≤ r / 2 := (htail btime hbT).2.1
  have hdη : d < η := (htail btime hbT).2.2.1
  refine ⟨d, hbpos, hdr, ?_⟩
  intro δ hδ
  have hsmall : ∀ᶠ t : ℝ in atBot, ‖P.coRotatedAncientGraphBase t‖ < δ :=
    hlim.norm.eventually (eventually_lt_nhds (by simpa only [norm_zero] using hδ.1))
  obtain ⟨a, haSmall, hab⟩ := (hsmall.and (eventually_le_atBot btime)).exists
  have hc : ContinuousOn (fun t => ‖P.coRotatedAncientGraphBase t‖) (Icc a btime) :=
    P.continuousOn_coRotatedAncientGraphBase.norm.mono (fun t ht => ht.2.trans hbneg.le)
  obtain ⟨s, hs, hsδ⟩ := intermediate_value_Icc hab hc ⟨haSmall.le, hδ.2.le⟩
  change ‖P.coRotatedAncientGraphBase s‖ = δ at hsδ
  have hsneg : s < 0 := hs.2.trans_lt hbneg
  have hsT : s ≤ T := hs.2.trans hbT
  have hinfo := htail s hsT
  refine ⟨s, hsneg, hsδ, hinfo.2.2.2.1, ?_⟩
  intro ξ hξ hnξ
  have hsη : ‖P.coRotatedAncientGraphBase s‖ ≤ η := by
    rw [hsδ]
    exact hδ.2.le.trans hdη.le
  obtain ⟨b, hrot⟩ := hphase (P.coRotatedAncientGraphBase s) ξ hinfo.1 hξ hsη (hsδ.trans hnξ.symm)
  have hpoint : x ξ 0 = circularConstrainedRotationCLM γ b (P.coRotatedAncientGraphPoint s) := by
    have hh := congrFun hrot 0
    rw [← hinfo.2.2.2.1] at hh
    exact hh
  refine ⟨b, hpoint, ?_⟩
  calc
    circularConstrainedChart hγ hγ1 (x ξ 0) =
        circularConstrainedChart hγ hγ1 (circularConstrainedRotationCLM γ b (P.coRotatedAncientGraphPoint s)) :=
      congrArg (circularConstrainedChart hγ hγ1) hpoint
    _ = contourRotationFamilyLittleCLM γ b
        (circularConstrainedChart hγ hγ1 (P.coRotatedAncientGraphPoint s)) :=
      circularConstrainedChart_rotation hγ hγ1 b _
    _ = contourRotationFamilyLittleCLM γ b (circularCoRotationCLM γ s (P.ancient s)) :=
      congrArg (contourRotationFamilyLittleCLM γ b) hinfo.2.2.2.2

end CircularMaterialTransferProfile
end Euler2D

end
