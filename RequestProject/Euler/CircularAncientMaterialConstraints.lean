module

public import RequestProject.Euler.CircularAncientMaterialOrbit
public import RequestProject.Euler.BanachCurveFlow

/-! The actual ancient material solution retains the original
areas and fourfold symmetry at every negative time and satisfies the
original pointwise contour equation. -/

@[expose] public section

set_option maxHeartbeats 4000000
set_option maxRecDepth 4000

noncomputable section

open Set Filter Topology Metric
open scoped NNReal ContDiff

namespace Euler2D

local instance (priority := 2000) ancientConstraintLittle_group (γ : ℝ≥0) :
    NormedAddCommGroup (LittleContourSpace γ) := Submodule.normedAddCommGroup (LittleContourSpace γ)
local instance (priority := 2000) ancientConstraintLittle_space (γ : ℝ≥0) :
    NormedSpace ℝ (LittleContourSpace γ) := Submodule.normedSpace (LittleContourSpace γ)
local instance (priority := 2000) ancientConstraintFamily_tower (γ : ℝ≥0) :
    IsScalarTower ℝ ℝ (Fin 2 → LittleContourSpace γ) where
  smul_assoc a b Z := by
    funext i
    change (a * b) • Z i = a • (b • Z i)
    exact (smul_smul a b (Z i)).symm

theorem circularAncientMaterial_area {γ : ℝ≥0} (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1)
    {Y : ℝ → Fin 2 → LittleContourSpace γ}
    (hYm : ∀ s ≤ 0, Y s ∈ circularQuarterPhaseDomain hγ hγ1)
    (hYd : ∀ s ≤ 0, HasDerivAt Y (circularBanachField hγ hγ1 (Y s)) s)
    {t : ℝ} (ht : t ≤ 0) (i : Fin 2) :
    littleContourArea γ (Y t i) = littleContourArea γ (Y 0 i) := by
  have hflow : IsBanachFlowOn (circularBanachField hγ hγ1) (circularQuarterPhaseDomain hγ hγ1)
      {Y t} (0 - t) (fun _ s => Y (s + t)) :=
    isBanachFlowOn_of_curve_interval (fun s hs => hYd s hs.2) (fun s hs => hYm s hs.2)
  have he := circularBanachFlow_area hγ hγ1 hflow (W := Y t) (by simp)
    (t := 0 - t) ⟨by linarith, le_rfl⟩ i
  have he' : littleContourArea γ (Y 0 i) = littleContourArea γ (Y t i) := by
    simpa only [sub_add_cancel] using he
  exact he'.symm

theorem circularAncientMaterial_fourfold_of_samples {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1)
    {Y : ℝ → Fin 2 → LittleContourSpace γ}
    (hYm : ∀ s ≤ 0, Y s ∈ circularQuarterPhaseDomain hγ hγ1)
    (hYd : ∀ s ≤ 0, HasDerivAt Y (circularBanachField hγ hγ1 (Y s)) s)
    (hsample : ∀ n : ℕ, ∀ i, Y (-(n : ℝ) * (period + period)) i ∈ fourfoldLittleContourSubmodule γ)
    {t : ℝ} (ht : t ≤ 0) (i : Fin 2) : Y t i ∈ fourfoldLittleContourSubmodule γ := by
  have hp : 0 < period + period := by unfold period; positivity
  obtain ⟨n, hn⟩ := exists_backward_time_index hp t
  let a : ℝ := -(n : ℝ) * (period + period)
  have hat : a ≤ t := hn.le
  have hflow : IsBanachFlowOn (circularBanachField hγ hγ1) (circularBanachDomain hγ hγ1)
      {Y a} (0 - a) (fun _ s => Y (s + a)) :=
    isBanachFlowOn_of_curve_interval (fun s hs => hYd s hs.2) (fun s hs => (hYm s hs.2).1)
  have he := circularBanachFlow_fourfold hγ hγ1 hflow (W := Y a) (by simp) (hsample n)
    (t := t - a) ⟨by linarith, by linarith⟩ i
  simpa only [sub_add_cancel] using he

theorem circularAncientMaterial_boundary_equation {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1)
    {Y : ℝ → Fin 2 → LittleContourSpace γ}
    (hYm : ∀ s ≤ 0, Y s ∈ circularQuarterPhaseDomain hγ hγ1)
    (hYd : ∀ s ≤ 0, HasDerivAt Y (circularBanachField hγ hγ1 (Y s)) s)
    {s : ℝ} (hs : s ≤ 0) (i : Fin 2) (θ : ℝ) :
    HasDerivAt (fun u => LittleContourSpace.lift γ (Y u i) θ)
      (contourBoundaryField circularContourStrengths
        (fun j => LittleContourSpace.lift γ (Y s j)) i θ) s := by
  have hd := ((LittleContourSpace.eval γ (θ : ContourCircle)).comp
    (ContinuousLinearMap.proj i)).hasFDerivAt.comp_hasDerivAt s (hYd s hs)
  change HasDerivAt (fun u => LittleContourSpace.lift γ (Y u i) θ)
    (LittleContourSpace.lift γ (circularBanachField hγ hγ1 (Y s) i) θ) s at hd
  rw [circularBanachField, lift_finiteContourPhaseFieldTotal hγ hγ1 _ _ _ _ _
    (Y s) (hYm s hs).1] at hd
  exact hd

theorem exists_circularAncientMaterialOrbit_constrained {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1) :
    ∃ δ > 0, ∃ Y : ℝ → Fin 2 → LittleContourSpace γ,
      ContinuousOn Y (Iic 0) ∧
      (∀ s ≤ 0, Y s ∈ circularQuarterPhaseDomain hγ hγ1) ∧
      (∀ s ≤ 0, HasDerivAt Y (circularBanachField hγ hγ1 (Y s)) s) ∧
      (∀ s ≤ 0, ∀ i, littleContourArea γ (Y s i) = Real.pi * circularContourRadii i ^ 2) ∧
      (∀ s ≤ 0, ∀ i, Y s i ∈ fourfoldLittleContourSubmodule γ) ∧
      Tendsto (fun n : ℕ => Y (-(n : ℝ) * (period + period))) atTop
        (𝓝 (littleCircularReference hγ hγ1)) ∧
      (∀ i, ‖(Y 0 i).val - (littleReferenceCircle hγ hγ1.le (circularContourRadii i)).val‖ <
        circularContourRadii i / 4) ∧
      δ ≤ ‖circularMaterialPatchFourthMoment hγ hγ1.le (Y 0)‖ := by
  obtain ⟨δ, hδ, Y, hc, hm, hd, hlim, hsample, hclose, harea0, hfour0, hdep⟩ :=
    exists_circularAncientMaterialOrbit hγ hγ1
  refine ⟨δ, hδ, Y, hc, hm, hd, ?_, ?_, hlim, hclose, hdep⟩
  · intro s hs i
    exact (circularAncientMaterial_area hγ hγ1 hm hd hs i).trans (harea0 i)
  · intro s hs i
    exact circularAncientMaterial_fourfold_of_samples hγ hγ1 hm hd hsample hs i

end Euler2D

end
