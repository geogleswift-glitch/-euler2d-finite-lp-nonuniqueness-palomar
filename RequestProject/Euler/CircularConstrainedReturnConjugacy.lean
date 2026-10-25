module

public import RequestProject.Euler.CircularConstrainedReturnMap

/-! Genuine local conjugacy of the constrained nonlinear return map
to the actual full-period material flow, using the actual area inverse. -/

@[expose] public section

set_option maxHeartbeats 1000000

noncomputable section

open Set Filter Topology Metric Complex
open scoped NNReal ContDiff

namespace Euler2D

local instance (priority := 2000) returnConjugacyLittle_group (γ : ℝ≥0) :
    NormedAddCommGroup (LittleContourSpace γ) := Submodule.normedAddCommGroup (LittleContourSpace γ)
local instance (priority := 2000) returnConjugacyLittle_space (γ : ℝ≥0) :
    NormedSpace ℝ (LittleContourSpace γ) := Submodule.normedSpace (LittleContourSpace γ)
local instance (priority := 2000) returnConjugacyFamily_tower (γ : ℝ≥0) :
    IsScalarTower ℝ ℝ (Fin 2 → LittleContourSpace γ) where
  smul_assoc a b Z := by
    funext i
    change (a * b) • Z i = a • (b • Z i)
    exact (smul_smul a b (Z i)).symm
local instance (priority := 2000) returnConjugacyTangent_group (γ : ℝ≥0) :
    NormedAddCommGroup (CircularConstrainedTangentSpace γ) :=
  Submodule.normedAddCommGroup (circularConstrainedTangentSubmodule γ)
local instance (priority := 2000) returnConjugacyTangent_space (γ : ℝ≥0) :
    NormedSpace ℝ (CircularConstrainedTangentSpace γ) :=
  Submodule.normedSpace (circularConstrainedTangentSubmodule γ)
local instance (priority := 2000) returnConjugacyTangent_continuousAdd (γ : ℝ≥0) :
    ContinuousAdd (CircularConstrainedTangentSpace γ) where
  continuous_add := by
    have h1 : Continuous (fun p : CircularConstrainedTangentSpace γ × CircularConstrainedTangentSpace γ =>
        p.1.val) := continuous_subtype_val.comp continuous_fst
    have h2 : Continuous (fun p : CircularConstrainedTangentSpace γ × CircularConstrainedTangentSpace γ =>
        p.2.val) := continuous_subtype_val.comp continuous_snd
    exact (h1.add h2).subtype_mk _

theorem circularConstraintProjection_sub_reference {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1) (Z : Fin 2 → LittleContourSpace γ)
    (hZ : ∀ i, Z i ∈ fourfoldLittleContourSubmodule γ) :
    circularConstraintProjectionCLM hγ hγ1.le (Z - littleCircularReference hγ hγ1) =
      circularAreaChartInverseFamily hγ hγ1 Z := by
  funext i
  change littleAreaTangentProjection hγ hγ1.le (circularContourRadii i)
    (littleFourfoldProjectionCLM γ (Z i - littleReferenceCircle hγ hγ1.le (circularContourRadii i))) = _
  rw [littleFourfoldProjectionCLM_of_mem _
    ((fourfoldLittleContourSubmodule γ).sub_mem (hZ i)
      (littleReferenceCircle_mem_fourfold hγ hγ1.le (circularContourRadii i)))]
  rfl

theorem circularConstrainedReturnMap_val_of_fourfold {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1)
    (P : (Fin 2 → LittleContourSpace γ) → Fin 2 → LittleContourSpace γ)
    (v : CircularConstrainedTangentSpace γ)
    (hfour : ∀ i, P (circularConstrainedChart hγ hγ1 v) i ∈ fourfoldLittleContourSubmodule γ) :
    (circularConstrainedReturnMap hγ hγ1 P v).val =
      circularAreaChartInverseFamily hγ hγ1 (P (circularConstrainedChart hγ hγ1 v)) :=
  circularConstraintProjection_sub_reference hγ hγ1 _ hfour

theorem eventually_circularConstrainedChart_positive {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1) :
    ∀ᶠ v : CircularConstrainedTangentSpace γ in 𝓝 0, ∀ i,
      0 < 1 - littleContourArea γ (v.val i) / (Real.pi * circularContourRadii i ^ 2) := by
  apply Filter.eventually_all.mpr
  intro i
  let L : CircularConstrainedTangentSpace γ →L[ℝ] LittleContourSpace γ :=
    (ContinuousLinearMap.proj i).comp (circularConstrainedTangentSubmodule γ).subtypeL
  have hc : Continuous (fun v : CircularConstrainedTangentSpace γ =>
      1 - littleContourArea γ (v.val i) / (Real.pi * circularContourRadii i ^ 2)) :=
    continuous_const.sub ((((continuous_contourArea γ).comp (LittleContourSpace.inclusion γ).continuous).comp
      L.continuous).div_const _)
  exact hc.continuousAt.eventually (eventually_gt_nhds (by
    change 0 < 1 - littleContourArea γ 0 / _
    simp only [littleContourArea_zero, zero_div, sub_zero, zero_lt_one]))

theorem eventually_circularConstrainedReturnMap_conjugacy {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1) {ρ : ℝ} (hρ : 0 < ρ)
    {P : (Fin 2 → LittleContourSpace γ) → Fin 2 → LittleContourSpace γ}
    (hP : ContinuousAt P (littleCircularReference hγ hγ1))
    (hfix : P (littleCircularReference hγ hγ1) = littleCircularReference hγ hγ1)
    (harea : ∀ W ∈ ball (littleCircularReference hγ hγ1) ρ, ∀ i,
      littleContourArea γ (P W i) = littleContourArea γ (W i))
    (hfour : ∀ W ∈ ball (littleCircularReference hγ hγ1) ρ,
      (∀ i, W i ∈ fourfoldLittleContourSubmodule γ) →
        ∀ i, P W i ∈ fourfoldLittleContourSubmodule γ) :
    ∀ᶠ v : CircularConstrainedTangentSpace γ in 𝓝 0,
      circularConstrainedChart hγ hγ1 (circularConstrainedReturnMap hγ hγ1 P v) =
        P (circularConstrainedChart hγ hγ1 v) := by
  let Φ := circularConstrainedChart hγ hγ1
  let Y := fun v : CircularConstrainedTangentSpace γ => P (Φ v)
  have hΦ : ContinuousAt Φ 0 := (hasFDerivAt_circularConstrainedChart_zero hγ hγ1).continuousAt
  have hY : ContinuousAt Y 0 := by
    have hp' : ContinuousAt P (Φ 0) := by rw [show Φ 0 = _ from circularConstrainedChart_zero hγ hγ1]; exact hP
    exact hp'.comp hΦ
  have hY0 : Y 0 = littleCircularReference hγ hγ1 := by
    dsimp only [Y, Φ]
    rw [circularConstrainedChart_zero, hfix]
  have hball : ∀ᶠ v : CircularConstrainedTangentSpace γ in 𝓝 0,
      Φ v ∈ ball (littleCircularReference hγ hγ1) ρ :=
    hΦ (by rw [show Φ 0 = _ from circularConstrainedChart_zero hγ hγ1]; exact ball_mem_nhds _ hρ)
  have hrad : ∀ᶠ v : CircularConstrainedTangentSpace γ in 𝓝 0, ∀ i,
      0 < 1 + littleAreaRadialCoeffCLM γ (circularContourRadii i)
        (Y v i - littleReferenceCircle hγ hγ1.le (circularContourRadii i)) := by
    apply Filter.eventually_all.mpr
    intro i
    let C := littleReferenceCircle hγ hγ1.le (circularContourRadii i)
    let L := littleAreaRadialCoeffCLM γ (circularContourRadii i)
    have hi : ContinuousAt (fun v : CircularConstrainedTangentSpace γ => Y v i) 0 :=
      (continuous_apply i).continuousAt.comp hY
    have hc : ContinuousAt (fun v : CircularConstrainedTangentSpace γ => 1 + L (Y v i - C)) 0 :=
      continuousAt_const.add (L.continuous.continuousAt.comp (hi.sub continuousAt_const))
    exact hc.eventually (eventually_gt_nhds (by
      change 0 < 1 + L (Y 0 i - C)
      rw [hY0]
      change 0 < 1 + L (C - C)
      rw [sub_self, map_zero, add_zero]
      norm_num))
  filter_upwards [hball, eventually_circularConstrainedChart_positive hγ hγ1, hrad] with v hv hp hr
  have hf : ∀ i, Y v i ∈ fourfoldLittleContourSubmodule γ :=
    hfour (Φ v) hv (circularConstrainedChart_fourfold hγ hγ1 v)
  have he := circularConstrainedReturnMap_val_of_fourfold hγ hγ1 P v hf
  funext i
  change littleAreaChart hγ hγ1.le (circularContourRadii i)
    ((circularConstrainedReturnMap hγ hγ1 P v).val i) = Y v i
  rw [congrFun he i]
  exact littleAreaChart_littleAreaChartInverse hγ hγ1.le
    (by fin_cases i <;> simp [circularContourRadii, cellA_pos.ne']) (Y v i) (hr i)
    ((harea (Φ v) hv i).trans (circularConstrainedChart_area hγ hγ1 v hp i))

theorem exists_circularConstrained_C3_return_coordinates {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1) :
    ∃ ρ > 0, ∃ X : (Fin 2 → LittleContourSpace γ) → ℝ → Fin 2 → LittleContourSpace γ,
      IsBanachFlowOn (circularBanachField hγ hγ1) (circularBanachDomain hγ hγ1)
        (ball (littleCircularReference hγ hγ1) ρ) period X ∧
      ContDiffAt ℝ 3 (circularConstrainedReturnMap hγ hγ1 (fun W => X W period)) 0 ∧
      circularConstrainedReturnMap hγ hγ1 (fun W => X W period) 0 = 0 ∧
      (∀ᶠ v : CircularConstrainedTangentSpace γ in 𝓝 0,
        circularConstrainedChart hγ hγ1
          (circularConstrainedReturnMap hγ hγ1 (fun W => X W period) v) =
            X (circularConstrainedChart hγ hγ1 v) period) ∧
      ∀ c : ℂ, fderiv ℝ (circularConstrainedReturnMap hγ hγ1 (fun W => X W period)) 0
        (circularConstrainedUnstableEmbeddingCLM hγ hγ1.le c) =
          (-lamMult : ℝ) • circularConstrainedUnstableEmbeddingCLM hγ hγ1.le c := by
  have hflow := exists_circularContour_constrained_period_flow (γ := γ) hγ hγ1 (3 : ℕ)
  rcases hflow with ⟨ρ, hρ, X, hX, hs, hfix, hnear, harea, hfour⟩
  have hp : period ∈ Icc (0 : ℝ) period := ⟨by unfold period; positivity, le_rfl⟩
  have hP : ContDiffAt ℝ 3 (fun W => X W period) (littleCircularReference hγ hγ1) :=
    (hs period hp).contDiffAt (isOpen_ball.mem_nhds (mem_ball_self hρ))
  have hd := hP.differentiableAt (by norm_num)
  refine ⟨ρ, hρ, X, hX, contDiffAt_circularConstrainedReturnMap hγ hγ1 3 hP,
    circularConstrainedReturnMap_zero hγ hγ1 _ hfix, ?_, ?_⟩
  · exact eventually_circularConstrainedReturnMap_conjugacy hγ hγ1 hρ hP.continuousAt hfix
      (fun W hW i => harea W hW period hp i)
      (fun W hW hf i => hfour W hW hf period hp i)
  · intro c
    exact circularConstrainedReturnMap_derivative_unstable hγ hγ1 hρ hX hd c

end Euler2D

end
