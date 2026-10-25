module

public import RequestProject.Euler.CircularUnstableBackwardDeparture
public import RequestProject.Euler.CircularConstrainedReturnConjugacy
public import RequestProject.Euler.BanachAncientConjugacy

/-! A genuine ancient material solution of the original contour
equation, obtained from the actual local flow and its actual nonlinear
unstable return orbit. Its endpoint has a strictly positive fourth
moment of the original two-interface patch label. -/

@[expose] public section

set_option maxHeartbeats 10000000
set_option maxRecDepth 4000

noncomputable section

open Set Filter Topology Metric
open scoped NNReal ContDiff BigOperators

namespace Euler2D

local instance (priority := 2000) ancientMaterialLittle_group (γ : ℝ≥0) :
    NormedAddCommGroup (LittleContourSpace γ) := Submodule.normedAddCommGroup (LittleContourSpace γ)
local instance (priority := 2000) ancientMaterialLittle_space (γ : ℝ≥0) :
    NormedSpace ℝ (LittleContourSpace γ) := Submodule.normedSpace (LittleContourSpace γ)
local instance (priority := 2000) ancientMaterialFamily_tower (γ : ℝ≥0) :
    IsScalarTower ℝ ℝ (Fin 2 → LittleContourSpace γ) where
  smul_assoc a b Z := by
    funext i
    change (a * b) • Z i = a • (b • Z i)
    exact (smul_smul a b (Z i)).symm
local instance (priority := 2000) ancientMaterialTangent_group (γ : ℝ≥0) :
    NormedAddCommGroup (CircularConstrainedTangentSpace γ) :=
  Submodule.normedAddCommGroup (circularConstrainedTangentSubmodule γ)
local instance (priority := 2000) ancientMaterialTangent_space (γ : ℝ≥0) :
    NormedSpace ℝ (CircularConstrainedTangentSpace γ) :=
  Submodule.normedSpace (circularConstrainedTangentSubmodule γ)
local instance (priority := 2000) ancientMaterialTangent_continuousAdd (γ : ℝ≥0) :
    ContinuousAdd (CircularConstrainedTangentSpace γ) where
  continuous_add := by
    have h1 : Continuous (fun p : CircularConstrainedTangentSpace γ × CircularConstrainedTangentSpace γ =>
        p.1.val) := continuous_subtype_val.comp continuous_fst
    have h2 : Continuous (fun p : CircularConstrainedTangentSpace γ × CircularConstrainedTangentSpace γ =>
        p.2.val) := continuous_subtype_val.comp continuous_snd
    exact (h1.add h2).subtype_mk _
local instance (priority := 2000) ancientMaterialTangent_complete (γ : ℝ≥0) :
    CompleteSpace (CircularConstrainedTangentSpace γ) := circularConstrainedTangentSpace_complete γ

attribute [local irreducible] circularConstrainedTangentSubmodule circularConstrainedUnstableProjectionCLM

def circularMaterialPatchFourthMoment {γ : ℝ≥0} (hγ : 0 < γ) (hγ1 : γ ≤ 1)
    (Z : Fin 2 → LittleContourSpace γ) : ℂ :=
  ∑ i : Fin 2, (circularContourStrengths i : ℂ) *
    littlePatchFourthMoment hγ hγ1 (circularContourRadii i) (growingMoment_radius_pos i) (Z i)

theorem circularMaterialPatchFourthMoment_chart {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1) (v : CircularConstrainedTangentSpace γ) :
    circularMaterialPatchFourthMoment hγ hγ1.le (circularConstrainedChart hγ hγ1 v) =
      circularConstrainedPatchFourthMoment hγ hγ1.le v := rfl

theorem circularMaterialPatchFourthMoment_reference {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1) :
    circularMaterialPatchFourthMoment hγ hγ1.le (littleCircularReference hγ hγ1) = 0 := by
  have h := circularMaterialPatchFourthMoment_chart hγ hγ1 0
  rw [circularConstrainedChart_zero, circularConstrainedPatchFourthMoment_zero] at h
  exact h

theorem eventually_circularConstrainedChart_patch_near {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1) :
    ∀ᶠ v : CircularConstrainedTangentSpace γ in 𝓝 0, ∀ i : Fin 2,
      ‖(circularConstrainedChart hγ hγ1 v i).val -
          (littleReferenceCircle hγ hγ1.le (circularContourRadii i)).val‖ < circularContourRadii i / 4 := by
  have hΦ := (hasFDerivAt_circularConstrainedChart_zero hγ hγ1).continuousAt
  apply Filter.eventually_all.mpr
  intro i
  let pr : (Fin 2 → LittleContourSpace γ) →L[ℝ] ContourC1Space γ :=
    (LittleContourSpace.inclusion γ).comp (ContinuousLinearMap.proj i)
  have hc : ContinuousAt (fun v : CircularConstrainedTangentSpace γ =>
      ‖pr (circularConstrainedChart hγ hγ1 v) -
        (littleReferenceCircle hγ hγ1.le (circularContourRadii i)).val‖) 0 :=
    ((pr.continuous.continuousAt.comp hΦ).sub continuousAt_const).norm
  exact hc.eventually (eventually_lt_nhds (by
    change ‖pr (circularConstrainedChart hγ hγ1 0) -
      (littleReferenceCircle hγ hγ1.le (circularContourRadii i)).val‖ < circularContourRadii i / 4
    rw [circularConstrainedChart_zero]
    change ‖(littleReferenceCircle hγ hγ1.le (circularContourRadii i)).val -
      (littleReferenceCircle hγ hγ1.le (circularContourRadii i)).val‖ < _
    rw [sub_self, norm_zero]
    exact div_pos (growingMoment_radius_pos i) (by norm_num)))

attribute [local irreducible] circularConstrainedReturnMap circularConstrainedUnstableEmbeddingCLM
  circularConstrainedUnstableCoordinateCLM circularConstrainedChart circularConstraintProjectionToTangentCLM
  circularConstrainedPatchFourthMoment circularMaterialPatchFourthMoment

theorem exists_circularAncientMaterialOrbit {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1) :
    ∃ δ > 0, ∃ Y : ℝ → Fin 2 → LittleContourSpace γ,
      ContinuousOn Y (Iic 0) ∧
      (∀ s ≤ 0, Y s ∈ circularQuarterPhaseDomain hγ hγ1) ∧
      (∀ s ≤ 0, HasDerivAt Y (circularBanachField hγ hγ1 (Y s)) s) ∧
      Tendsto (fun n : ℕ => Y (-(n : ℝ) * (period + period))) atTop
        (𝓝 (littleCircularReference hγ hγ1)) ∧
      (∀ n : ℕ, ∀ i, Y (-(n : ℝ) * (period + period)) i ∈ fourfoldLittleContourSubmodule γ) ∧
      (∀ i, ‖(Y 0 i).val - (littleReferenceCircle hγ hγ1.le (circularContourRadii i)).val‖ <
        circularContourRadii i / 4) ∧
      (∀ i, littleContourArea γ (Y 0 i) = Real.pi * circularContourRadii i ^ 2) ∧
      (∀ i, Y 0 i ∈ fourfoldLittleContourSubmodule γ) ∧
      δ ≤ ‖circularMaterialPatchFourthMoment hγ hγ1.le (Y 0)‖ := by
  obtain ⟨R, hR, X, hX, hs, hfix, hnear, harea, hfour⟩ :=
    exists_circularContour_constrained_period_flow hγ hγ1 3
  have hp0 : 0 < period := by unfold period; positivity
  have hp : period ∈ Icc (0 : ℝ) period := ⟨hp0.le, le_rfl⟩
  have hd3 : ContDiffAt ℝ 3 (fun W => X W period) (littleCircularReference hγ hγ1) :=
    (hs period hp).contDiffAt (isOpen_ball.mem_nhds (mem_ball_self hR))
  have hd1 : ContDiffAt ℝ 1 (fun W => X W period) (littleCircularReference hγ hγ1) :=
    hd3.of_le (by norm_num)
  let F := circularConstrainedReturnMap hγ hγ1 (fun W => X W period)
  let Φ := circularConstrainedChart hγ hγ1
  have hF0 : F 0 = 0 := circularConstrainedReturnMap_zero hγ hγ1 _ hfix
  have hF : ContinuousAt F 0 := (contDiffAt_circularConstrainedReturnMap hγ hγ1 1 hd1).continuousAt
  have hΦ : ContinuousAt Φ 0 := (hasFDerivAt_circularConstrainedChart_zero hγ hγ1).continuousAt
  have hΦ0 : Φ 0 = littleCircularReference hγ hγ1 := circularConstrainedChart_zero hγ hγ1
  have hV : ball (littleCircularReference hγ hγ1) R ∈ 𝓝 (Φ 0) := by
    rw [hΦ0]
    exact ball_mem_nhds _ hR
  have hconj : ∀ᶠ v : CircularConstrainedTangentSpace γ in 𝓝 0, Φ (F v) = X (Φ v) period :=
    eventually_circularConstrainedReturnMap_conjugacy hγ hγ1 hR hd1.continuousAt hfix
      (fun W hW i => harea W hW period hp i)
      (fun W hW hf i => hfour W hW hf period hp i)
  have hXq : IsBanachFlowOn (circularBanachField hγ hγ1) (circularQuarterPhaseDomain hγ hγ1)
      (ball (littleCircularReference hγ hγ1) R) period X :=
    ⟨hX.initial, hX.continuous, hX.hasDerivAt, hnear⟩
  obtain ⟨rlift, hrlift, hlift⟩ := exists_ancientCurve_lifting_double_return hp0 hXq hF0 hF hΦ hV hconj
  obtain ⟨s, hsp, hgood⟩ := Metric.eventually_nhds_iff.mp
    ((eventually_circularConstrainedChart_patch_near hγ hγ1).and
      (eventually_circularConstrainedChart_positive hγ hγ1))
  let cap := min rlift (s / 2)
  have hcap : 0 < cap := lt_min hrlift (half_pos hsp)
  obtain ⟨t, ht, x, hback, hball, hnorm, hproj, hmoment, hmomentne, hxlim⟩ :=
    exists_circularConstrained_backward_departure hγ hγ1 hR hX hd1 hfix
      (fun W hW i => harea W hW period hp i) hcap
  obtain ⟨Y, hY0, hYc, hYm, hYd, hYsamp⟩ := hlift x
    (fun n => closedBall_subset_closedBall (min_le_left _ _) (hball n)) hback
  have hxgood := hgood (closedBall_subset_ball
    (lt_of_le_of_lt (min_le_right rlift (s / 2)) (half_lt_self hsp)) (hball 0))
  have hlim := hΦ.tendsto.comp hxlim
  rw [hΦ0] at hlim
  let δ := (‖circularPatchGrowingResponse‖ / 2) * t
  have hδ : 0 < δ := mul_pos (half_pos (norm_pos_iff.mpr circularPatchGrowingResponse_ne_zero)) ht
  refine ⟨δ, hδ, Y, hYc, hYm, hYd, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hlim.congr' (Filter.Eventually.of_forall (fun n => (hYsamp n).symm))
  · intro n i
    rw [hYsamp n]
    exact circularConstrainedChart_fourfold hγ hγ1 (x n) i
  · rw [hY0]
    exact hxgood.1
  · rw [hY0]
    exact circularConstrainedChart_area hγ hγ1 (x 0) hxgood.2
  · rw [hY0]
    exact circularConstrainedChart_fourfold hγ hγ1 (x 0)
  · rw [hY0, circularMaterialPatchFourthMoment_chart hγ hγ1]
    exact hmoment

end Euler2D

end
