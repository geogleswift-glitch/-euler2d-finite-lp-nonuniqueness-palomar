module

public import RequestProject.Euler.CircularConstrainedPatchMoment
public import RequestProject.Euler.BanachQuadraticRemainder
public import RequestProject.Euler.CircularPatchMomentResponse
public import RequestProject.Euler.BanachObservableDeparture

/-! The actual strength-weighted fourth patch moment restricted to
the original fourfold fixed-area tangent coordinates. -/

@[expose] public section

set_option maxHeartbeats 4000000
set_option maxRecDepth 4000

noncomputable section

open Set Filter Topology Metric
open scoped NNReal ContDiff

namespace Euler2D

local instance (priority := 2000) smoothMomentLittle_group (γ : ℝ≥0) :
    NormedAddCommGroup (LittleContourSpace γ) := Submodule.normedAddCommGroup (LittleContourSpace γ)
local instance (priority := 2000) smoothMomentLittle_space (γ : ℝ≥0) :
    NormedSpace ℝ (LittleContourSpace γ) := Submodule.normedSpace (LittleContourSpace γ)
local instance (priority := 2000) smoothMomentFamily_tower (γ : ℝ≥0) :
    IsScalarTower ℝ ℝ (Fin 2 → LittleContourSpace γ) where
  smul_assoc a b Z := by
    funext i
    change (a * b) • Z i = a • (b • Z i)
    exact (smul_smul a b (Z i)).symm
local instance (priority := 2000) smoothMomentTangent_group (γ : ℝ≥0) :
    NormedAddCommGroup (CircularConstrainedTangentSpace γ) :=
  Submodule.normedAddCommGroup (circularConstrainedTangentSubmodule γ)
local instance (priority := 2000) smoothMomentTangent_space (γ : ℝ≥0) :
    NormedSpace ℝ (CircularConstrainedTangentSpace γ) :=
  Submodule.normedSpace (circularConstrainedTangentSubmodule γ)
local instance (priority := 2000) smoothMomentTangent_continuousAdd (γ : ℝ≥0) :
    ContinuousAdd (CircularConstrainedTangentSpace γ) where
  continuous_add := by
    have h1 : Continuous (fun p : CircularConstrainedTangentSpace γ × CircularConstrainedTangentSpace γ =>
        p.1.val) := continuous_subtype_val.comp continuous_fst
    have h2 : Continuous (fun p : CircularConstrainedTangentSpace γ × CircularConstrainedTangentSpace γ =>
        p.2.val) := continuous_subtype_val.comp continuous_snd
    exact (h1.add h2).subtype_mk _

attribute [local irreducible] circularConstrainedTangentSubmodule circularConstrainedUnstableProjectionCLM

theorem contDiffAt_littlePatchFourthMoment_reference {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : γ ≤ 1) {r : ℝ} (hr : 0 < r) :
    ContDiffAt ℝ 2 (littlePatchFourthMoment hγ hγ1 r hr) (littleReferenceCircle hγ hγ1 r) := by
  have ho : ContDiffAt ℝ 2 (contourFourthMoment γ)
      ((LittleContourSpace.inclusion γ) (littleReferenceCircle hγ hγ1 r)) :=
    (contDiff_contourFourthMoment γ).contDiffAt.of_le (by
      change ((2 : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞)
      exact WithTop.coe_le_coe.mpr le_top)
  have h : ContDiffAt ℝ 2 (fun Z : LittleContourSpace γ => contourFourthMoment γ Z.val)
      (littleReferenceCircle hγ hγ1 r) :=
    ho.comp _ (LittleContourSpace.inclusion γ).contDiff.contDiffAt
  exact h.congr_of_eventuallyEq (littlePatchFourthMoment_eventually_eq_boundary hγ hγ1 hr)

theorem contDiffAt_circularAreaChartFourthMoment_zero {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : γ ≤ 1) (i : Fin 2) :
    ContDiffAt ℝ 2 (circularAreaChartFourthMoment hγ hγ1 i) 0 := by
  have hchart : ContDiffAt ℝ 2 (littleAreaChart hγ hγ1 (circularContourRadii i)) 0 :=
    (analyticAt_littleAreaChart hγ hγ1 _ 0 (by
      simp only [littleContourArea_zero, zero_div, sub_zero, zero_lt_one])).contDiffAt
  have houter : ContDiffAt ℝ 2
      (littlePatchFourthMoment hγ hγ1 (circularContourRadii i) (growingMoment_radius_pos i))
      (littleAreaChart hγ hγ1 (circularContourRadii i) 0) := by
    rw [littleAreaChart_zero]
    exact contDiffAt_littlePatchFourthMoment_reference hγ hγ1 (growingMoment_radius_pos i)
  exact houter.comp 0 hchart

theorem contDiffAt_circularFamilyPatchFourthMoment_zero {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : γ ≤ 1) : ContDiffAt ℝ 2 (circularFamilyPatchFourthMoment hγ hγ1) 0 := by
  have hd (i : Fin 2) : ContDiffAt ℝ 2
      (fun v : Fin 2 → LittleContourSpace γ => circularAreaChartFourthMoment hγ hγ1 i (v i)) 0 := by
    let p : (Fin 2 → LittleContourSpace γ) →L[ℝ] LittleContourSpace γ := ContinuousLinearMap.proj i
    have hg : ContDiffAt ℝ 2 (circularAreaChartFourthMoment hγ hγ1 i)
        (p (0 : Fin 2 → LittleContourSpace γ)) := by
      simpa only [ContinuousLinearMap.map_zero] using contDiffAt_circularAreaChartFourthMoment_zero hγ hγ1 i
    exact hg.comp 0 p.contDiff.contDiffAt
  have hw (i : Fin 2) : ContDiffAt ℝ 2
      (fun v : Fin 2 → LittleContourSpace γ => (circularContourStrengths i : ℂ) *
        circularAreaChartFourthMoment hγ hγ1 i (v i)) 0 := contDiffAt_const.mul (hd i)
  convert (hw 0).add (hw 1) using 1
  funext v
  simp only [circularFamilyPatchFourthMoment, Fin.sum_univ_two, Pi.add_apply]

theorem contDiffAt_circularConstrainedPatchFourthMoment_zero {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : γ ≤ 1) : ContDiffAt ℝ 2 (circularConstrainedPatchFourthMoment hγ hγ1) 0 := by
  have ho : ContDiffAt ℝ 2 (circularFamilyPatchFourthMoment hγ hγ1)
      ((circularConstrainedTangentSubmodule γ).subtypeL 0) := by
    simpa only [ContinuousLinearMap.map_zero] using contDiffAt_circularFamilyPatchFourthMoment_zero hγ hγ1
  exact ho.comp (0 : CircularConstrainedTangentSpace γ) (circularConstrainedTangentSubmodule γ).subtypeL.contDiff.contDiffAt

theorem exists_circularConstrainedPatchFourthMoment_quadratic_bound {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : γ ≤ 1) :
    ∃ C > 0, ∃ r > 0, ∀ v ∈ closedBall (0 : CircularConstrainedTangentSpace γ) r,
      ‖circularConstrainedPatchFourthMoment hγ hγ1 v -
          fderiv ℝ (circularConstrainedPatchFourthMoment hγ hγ1) 0 v‖ ≤ C * ‖v‖ ^ 2 := by
  simpa only [banachLocalRemainder] using exists_banachLocalRemainder_quadratic_bound
    (contDiffAt_circularConstrainedPatchFourthMoment_zero hγ hγ1)
    (circularConstrainedPatchFourthMoment_zero hγ hγ1)

end Euler2D

end
