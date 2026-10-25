module

public import RequestProject.Euler.CircularFixedGraphInnerMomentSection
public import RequestProject.Euler.CircularSelectedCanonicalCaptureTarget
public import RequestProject.Euler.CircularActualConstraintChart

/-! The detector is applied to an actual fourfold fixed-area contour.
The selected target gives closeness to the same graph chart, so the
actual chart inverse is proved rather than supplied as new data. -/

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 24000000
set_option maxRecDepth 6000

noncomputable section

open Set Filter Topology Metric
open scoped NNReal ContDiff

namespace Euler2D

attribute [local instance 2000] innerDetectorLittle_group innerDetectorLittle_space
  innerDetectorFamily_tower innerDetectorTangent_group innerDetectorTangent_space
  innerDetectorTangent_continuousAdd fixedGraphTangent_complete

attribute [local irreducible] circularConstrainedTangentSubmodule circularConstrainedUnstableProjectionCLM
  circularConstrainedReturnMap circularConstrainedChart circularConstraintProjectionToTangentCLM
  circularBanachField circularBanachDomain

namespace CircularMaterialTransferProfile

variable {γ : ℝ≥0} {hγ : 0 < γ} {hγ1 : (γ : ℝ) < 1}
  (P : CircularMaterialTransferProfile hγ hγ1)

theorem exists_uniform_actualContour_innerMoment_section {Rflow r₀ : ℝ}
    (hRflow : 0 < Rflow) (hr₀ : 0 < r₀)
    {Xflow : (Fin 2 → LittleContourSpace γ) → ℝ → Fin 2 → LittleContourSpace γ}
    (hflow : IsBanachFlowOn (circularBanachField hγ hγ1) (circularBanachDomain hγ hγ1)
      (ball (littleCircularReference hγ hγ1) Rflow) period Xflow)
    (hd : ContDiffAt ℝ 2 (fun W => Xflow W period) (littleCircularReference hγ hγ1))
    (hfix : Xflow (littleCircularReference hγ hγ1) period = littleCircularReference hγ hγ1)
    (hareaFlow : ∀ W ∈ ball (littleCircularReference hγ hγ1) Rflow, ∀ i,
      littleContourArea γ (Xflow W period i) = littleContourArea γ (W i))
    {gseq : CircularConstrainedTangentSpace γ → ℕ → CircularConstrainedTangentSpace γ}
    (hg : IsLocalWeightedBackwardGraph
      (banachDoubleReturn (circularConstrainedReturnMap hγ hγ1 (fun W => Xflow W period)))
      (circularConstrainedUnstableProjectionCLM hγ hγ1.le) circularAncientBackwardWeight r₀ gseq) :
    ∃ δmax > 0, ∃ m > 0, ∀ δ : ℝ, 0 < δ → δ < δmax →
      ∀ sCanon εtarget Ctarget : ℝ,
      P.IsSelectedCanonicalCaptureTarget gseq δ sCanon εtarget Ctarget →
      ∀ Cgraph : ℝ, 0 ≤ Cgraph → ∀ᶠ ξ : ℝ in atTop,
      ∀ Z ∈ ball (littleCircularReference hγ hγ1) εtarget,
      (∀ i, Z i ∈ fourfoldLittleContourSubmodule γ) →
      (∀ i, littleContourArea γ (Z i) = Real.pi * circularContourRadii i ^ 2) →
      let v := circularConstraintProjectionToTangentCLM hγ hγ1.le (Z - littleCircularReference hγ hγ1)
      let α := circularConstrainedUnstableProjectionCLM hγ hγ1.le v
      ‖α‖ = δ → ‖v - gseq α 0‖ ≤ Cgraph * Real.exp (-ξ) ^ 3 →
        circularConstrainedChart hγ hγ1 v = Z ∧
        (m / 2) * δ ≤ ‖littlePatchFourthMoment hγ hγ1.le cellA cellA_pos (Z 0)‖ := by
  obtain ⟨δsection, hδsection, m, hm, hsection⟩ :=
    exists_fixedGraph_innerMoment_capture_section hγ hγ1 hRflow hr₀ hflow hd hfix hareaFlow hg
  obtain ⟨εchart, hεchart, hChartInverse⟩ := exists_circular_actualConstraintChart_radius hγ hγ1
  have hChartCont : ContinuousAt (fun v : CircularConstrainedTangentSpace γ =>
      ‖circularConstrainedChart hγ hγ1 v - littleCircularReference hγ hγ1‖) 0 :=
    ((hasFDerivAt_circularConstrainedChart_zero hγ hγ1).continuousAt.sub continuousAt_const).norm
  have hChartNear : ∀ᶠ v : CircularConstrainedTangentSpace γ in 𝓝 0,
      ‖circularConstrainedChart hγ hγ1 v - littleCircularReference hγ hγ1‖ < εchart / 4 :=
    hChartCont.eventually (eventually_lt_nhds (by
      simpa only [circularConstrainedChart_zero, sub_self, norm_zero] using
        (div_pos hεchart (by norm_num : (0 : ℝ) < 4))))
  obtain ⟨a, ha, hChartSmall⟩ := Metric.eventually_nhds_iff.mp hChartNear
  let δmax := min δsection (min (a / 4) (r₀ / 4))
  have hδmax : 0 < δmax := lt_min hδsection (lt_min (by positivity) (by positivity))
  refine ⟨δmax, hδmax, m, hm, ?_⟩
  intro δ hδ hδbound sCanon εtarget Ctarget htarget Cgraph hCgraph
  have hδsect : δ < δsection := hδbound.trans_le (min_le_left _ _)
  have hδa : δ < a / 4 := hδbound.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hδr₀ : δ ≤ r₀ / 2 := by
    have hh := hδbound.trans_le ((min_le_right _ _).trans (min_le_right _ _))
    linarith only [hh, hr₀]
  obtain ⟨hsCanon, hδTarget, hεtarget, hCtarget, hCanonicalNorm, hpoint⟩ := htarget
  have ht : Tendsto (fun ξ : ℝ => (Ctarget * Cgraph) * Real.exp (-ξ) ^ 3) atTop (𝓝 0) := by
    simpa only [zero_pow (by decide : (3 : ℕ) ≠ 0), mul_zero] using
      (Real.tendsto_exp_neg_atTop_nhds_zero.pow 3).const_mul (Ctarget * Cgraph)
  filter_upwards [hsection δ hδ hδsect Cgraph hCgraph,
    ht.eventually (gt_mem_nhds (half_pos hεchart))] with ξ hsectionξ hsmall
  intro Z hZtarget hfour harea
  dsimp only
  intro hαnorm herror
  let v := circularConstraintProjectionToTangentCLM hγ hγ1.le (Z - littleCircularReference hγ hγ1)
  let Q := circularConstrainedUnstableProjectionCLM hγ hγ1.le
  let α := Q v
  have hαnorm' : ‖α‖ = δ := hαnorm
  have hα : Q α = α := circularConstrainedUnstableProjectionCLM_idempotent hγ hγ1.le v
  have hgraph : ‖gseq α 0‖ ≤ 2 * δ := by
    simpa only [pow_zero, mul_one, hαnorm'] using hg.norm_le α hα
      (by rw [hαnorm']; exact hδr₀) 0
  have hgraphBall : gseq α 0 ∈ ball 0 a := by
    apply mem_ball_zero_iff.mpr
    linarith only [hgraph, hδa, hδ.le]
  have hgraphNear := hChartSmall hgraphBall
  obtain ⟨angle, hgraphChart, hZgraph⟩ := hpoint Z hZtarget hfour harea hαnorm
  have hZgraphSmall : ‖Z - circularConstrainedChart hγ hγ1 (gseq α 0)‖ ≤
      (Ctarget * Cgraph) * Real.exp (-ξ) ^ 3 := by
    rw [hgraphChart]
    exact hZgraph.trans (by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left herror hCtarget.le)
  have hZnear : Z ∈ ball (littleCircularReference hγ hγ1) εchart := by
    apply mem_ball_iff_norm.mpr
    have htriangle := norm_add_le (Z - circularConstrainedChart hγ hγ1 (gseq α 0))
      (circularConstrainedChart hγ hγ1 (gseq α 0) - littleCircularReference hγ hγ1)
    rw [sub_add_sub_cancel] at htriangle
    linarith only [htriangle, hZgraphSmall, hgraphNear, hsmall, hεchart]
  have hChart : circularConstrainedChart hγ hγ1 v = Z := hChartInverse Z hZnear hfour harea
  have hbound := (hsectionξ v hαnorm herror).2
  have hMomentEq : circularConstrainedInnerPatchFourthMoment hγ hγ1.le v =
      littlePatchFourthMoment hγ hγ1.le cellA cellA_pos (Z 0) := by
    simpa only [circularConstrainedInnerPatchFourthMoment, circularAreaChartFourthMoment,
      circularConstrainedChart, circularContourRadii] using
      congrArg (fun W : Fin 2 → LittleContourSpace γ =>
        littlePatchFourthMoment hγ hγ1.le cellA cellA_pos (W 0)) hChart
  refine ⟨hChart, ?_⟩
  simpa only [hMomentEq] using hbound

end CircularMaterialTransferProfile
end Euler2D

end
