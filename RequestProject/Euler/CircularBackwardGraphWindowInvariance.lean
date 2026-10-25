module

public import RequestProject.Euler.CircularBackwardGraphTimeInvariance
public import RequestProject.Euler.CircularConstrainedIntervalFlow
public import RequestProject.Euler.CircularLocalBackwardGraph
public import RequestProject.Euler.BanachBackwardGraphLocalFamilyInvariance

/-! Invariance of the same original weighted graph on any fixed positive time window.
The extended actual material flow is compared with the graph's already
fixed short-period flow by uniqueness, on a common neighborhood. -/

@[expose] public section

set_option maxHeartbeats 8000000
set_option maxRecDepth 6000

noncomputable section

open Set Filter Topology Metric
open scoped NNReal ContDiff

namespace Euler2D

attribute [local instance 2000] quadraticReferenceC1_group localGraphLittle_group localGraphLittle_space
  localGraphFamily_tower localGraphTangent_group localGraphTangent_space
  localGraphTangent_complete localGraphTangent_continuousAdd

attribute [local irreducible] circularBanachField circularBanachDomain circularCoRotationCLM
  littleCircularReference littleCircularMaterialContours circularConstrainedTangentSubmodule
  circularConstraintProjectionToTangentCLM circularConstrainedChart circularConstrainedReturnMap
  circularCoRotatedConstrainedMap circularConstrainedUnstableProjectionCLM
  contourC1GraphSubmodule holderGraphSubmodule

theorem exists_circularCoRotatedConstrainedMap_uniform_window_commutation {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1) {R S D : ℝ} (hD : 0 < D) (hR : 0 < R) (hS : 0 < S)
    {X Y : (Fin 2 → LittleContourSpace γ) → ℝ → Fin 2 → LittleContourSpace γ}
    (hX : IsBanachFlowOn (circularBanachField hγ hγ1) (circularBanachDomain hγ hγ1)
      (ball (littleCircularReference hγ hγ1) R) period X)
    (hd : DifferentiableAt ℝ (fun W => X W period) (littleCircularReference hγ hγ1))
    (hfix : X (littleCircularReference hγ hγ1) period = littleCircularReference hγ hγ1)
    (hareaX : ∀ W ∈ ball (littleCircularReference hγ hγ1) R, ∀ i,
      littleContourArea γ (X W period i) = littleContourArea γ (W i))
    (hY : IsBanachFlowOn (circularBanachField hγ hγ1) (circularBanachDomain hγ hγ1)
      (ball (littleCircularReference hγ hγ1) S) (D + period) Y)
    (hareaY : ∀ W ∈ ball (littleCircularReference hγ hγ1) S, ∀ t ∈ Icc (0 : ℝ) (D + period), ∀ i,
      littleContourArea γ (Y W t i) = littleContourArea γ (W i)) :
    ∃ C > 0, ∀ᶠ v : CircularConstrainedTangentSpace γ in 𝓝 0, ∀ t ∈ Icc (0 : ℝ) D,
      ‖circularCoRotatedConstrainedMap hγ hγ1 Y t v‖ ≤ C * ‖v‖ ∧
      circularConstrainedReturnMap hγ hγ1 (fun W => X W period)
          (circularCoRotatedConstrainedMap hγ hγ1 Y t v) =
        circularCoRotatedConstrainedMap hγ hγ1 Y t
          (circularConstrainedReturnMap hγ hγ1 (fun W => X W period) v) := by
  let F := circularConstrainedReturnMap hγ hγ1 (fun W => X W period)
  let Φ := circularConstrainedChart hγ hγ1
  let c := littleCircularReference hγ hγ1
  let Qproj := circularConstraintProjectionToTangentCLM hγ hγ1.le
  have hp : 0 < period := by unfold period; positivity
  obtain ⟨η, hη, C, hC, hcoords⟩ := exists_circularCoRotatedFlow_uniform_constraint_coordinates
    hγ hγ1 (add_pos hD hp) hS hR hY hareaY
  have hF0 : F 0 = 0 := circularConstrainedReturnMap_zero hγ hγ1 _ hfix
  have hFc : ContinuousAt F 0 := (hasFDerivAt_circularConstrainedReturnMap_zero hγ hγ1 hd).continuousAt
  have hΦc : ContinuousAt Φ 0 := (hasFDerivAt_circularConstrainedChart_zero hγ hγ1).continuousAt
  have hnearV : ∀ᶠ v in 𝓝 (0 : CircularConstrainedTangentSpace γ), ‖v‖ < η :=
    (continuous_norm.tendsto _).eventually (eventually_lt_nhds (by simpa only [norm_zero] using hη))
  have hnearF : ∀ᶠ v in 𝓝 (0 : CircularConstrainedTangentSpace γ), ‖F v‖ < η :=
    hFc.norm.eventually (eventually_lt_nhds (by change ‖F 0‖ < η; rw [hF0, norm_zero]; exact hη))
  have hnearX : ∀ᶠ v in 𝓝 (0 : CircularConstrainedTangentSpace γ), Φ v ∈ ball c R :=
    hΦc.eventually (by
      rw [show Φ 0 = c from circularConstrainedChart_zero hγ hγ1]
      exact isOpen_ball.mem_nhds (mem_ball_self hR))
  have hconj := eventually_circularConstrainedReturnMap_conjugacy hγ hγ1 hR hd.continuousAt hfix hareaX
    (fun W hW hf i => circularBanachFlow_fourfold hγ hγ1 hX hW hf ⟨hp.le, le_rfl⟩ i)
  refine ⟨C, hC, ?_⟩
  filter_upwards [hnearV, hnearF, hnearX, hconj] with v hv hFv hvX hΦF
  intro t ht
  have htH : t ∈ Icc (0 : ℝ) (D + period) := ⟨ht.1, by linarith [ht.2]⟩
  have hcv := hcoords v hv
  have hcf := hcoords (F v) hFv
  have hreturn : X (Φ v) period ∈ ball c S := by
    rw [← hΦF]
    exact hcf.1
  have hcomm := circularBanachFlow_coRotated_commute hγ hγ1 hX hY hvX hcv.1 ht.1
    (by linarith [ht.2]) hreturn (hcv.2 t htH).1
  have hΦT : Φ (circularCoRotatedConstrainedMap hγ hγ1 Y t v) =
      circularCoRotationCLM γ t (Y (Φ v) t) := (hcv.2 t htH).2.2
  have hΦF' : Φ (F v) = X (Φ v) period := hΦF
  refine ⟨(hcv.2 t htH).2.1, ?_⟩
  conv_lhs => rw [circularConstrainedReturnMap]
  conv_rhs => rw [circularCoRotatedConstrainedMap, circularConstrainedReturnMap]
  change Qproj (X (Φ (circularCoRotatedConstrainedMap hγ hγ1 Y t v)) period - c) =
    Qproj (circularCoRotationCLM γ t (Y (Φ (F v)) t) - c)
  rw [hΦT, hcomm, hΦF']

theorem exists_same_circularBackwardGraph_window_invariant_radius {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1) {R S D r w : ℝ}
    (hD : 0 < D) (hR : 0 < R) (hS : 0 < S) (hr : 0 < r) (hw : 1 ≤ w)
    {X Y : (Fin 2 → LittleContourSpace γ) → ℝ → Fin 2 → LittleContourSpace γ}
    (hX : IsBanachFlowOn (circularBanachField hγ hγ1) (circularBanachDomain hγ hγ1)
      (ball (littleCircularReference hγ hγ1) R) period X)
    (hd : DifferentiableAt ℝ (fun W => X W period) (littleCircularReference hγ hγ1))
    (hfix : X (littleCircularReference hγ hγ1) period = littleCircularReference hγ hγ1)
    (hareaX : ∀ W ∈ ball (littleCircularReference hγ hγ1) R, ∀ i,
      littleContourArea γ (X W period i) = littleContourArea γ (W i))
    (hY : IsBanachFlowOn (circularBanachField hγ hγ1) (circularBanachDomain hγ hγ1)
      (ball (littleCircularReference hγ hγ1) S) (D + period) Y)
    (hareaY : ∀ W ∈ ball (littleCircularReference hγ hγ1) S, ∀ t ∈ Icc (0 : ℝ) (D + period), ∀ i,
      littleContourArea γ (Y W t i) = littleContourArea γ (W i))
    {x : CircularConstrainedTangentSpace γ → ℕ → CircularConstrainedTangentSpace γ}
    (hg : IsLocalWeightedBackwardGraph
      (banachDoubleReturn (circularConstrainedReturnMap hγ hγ1 (fun W => X W period)))
      (circularConstrainedUnstableProjectionCLM hγ hγ1.le) w r x) :
    ∃ η > 0, η ≤ r / 2 ∧ ∀ t ∈ Icc (0 : ℝ) D, ∀ ξ : CircularConstrainedTangentSpace γ,
        circularConstrainedUnstableProjectionCLM hγ hγ1.le ξ = ξ → ‖ξ‖ ≤ η →
        ‖circularConstrainedUnstableProjectionCLM hγ hγ1.le
          (circularCoRotatedConstrainedMap hγ hγ1 Y t (x ξ 0))‖ ≤ r / 2 ∧
        x (circularConstrainedUnstableProjectionCLM hγ hγ1.le
          (circularCoRotatedConstrainedMap hγ hγ1 Y t (x ξ 0))) =
            (fun n => circularCoRotatedConstrainedMap hγ hγ1 Y t (x ξ n)) := by
  obtain ⟨C, hC, hlocal⟩ := exists_circularCoRotatedConstrainedMap_uniform_window_commutation
    hγ hγ1 hD hR hS hX hd hfix hareaX hY hareaY
  have hlocal' : ∀ᶠ v : CircularConstrainedTangentSpace γ in 𝓝 0, ∀ t : Icc (0 : ℝ) D,
      ‖circularCoRotatedConstrainedMap hγ hγ1 Y t.val v‖ ≤ C * ‖v‖ ∧
      circularConstrainedReturnMap hγ hγ1 (fun W => X W period)
          (circularCoRotatedConstrainedMap hγ hγ1 Y t.val v) =
        circularCoRotatedConstrainedMap hγ hγ1 Y t.val
          (circularConstrainedReturnMap hγ hγ1 (fun W => X W period) v) := by
    filter_upwards [hlocal] with v hv
    intro t
    exact hv t.val t.property
  obtain ⟨η, hη, hηr, hinv⟩ := hg.exists_uniform_local_family_invariant_radius_of_double_return
    hw hr (circularConstrainedUnstableProjectionCLM_idempotent hγ hγ1.le)
    (circularConstrainedReturnMap_zero hγ hγ1 _ hfix)
    (hasFDerivAt_circularConstrainedReturnMap_zero hγ hγ1 hd).continuousAt
    (fun t : Icc (0 : ℝ) D => circularCoRotatedConstrainedMap hγ hγ1 Y t.val) hC hlocal'
  refine ⟨η, hη, hηr, ?_⟩
  intro t ht ξ hξ hξη
  exact hinv ⟨t, ht⟩ ξ hξ hξη

end Euler2D

end
