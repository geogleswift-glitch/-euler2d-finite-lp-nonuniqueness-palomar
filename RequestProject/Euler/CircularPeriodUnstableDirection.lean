module

public import RequestProject.Euler.CircularGrowingVariation
public import RequestProject.Euler.CircularReferenceCompactness
public import RequestProject.Euler.CircularFourierConstraints
public import RequestProject.Euler.BanachReferenceVariational

/-! The genuine period map has a nonzero unstable direction in the
original fourfold fixed-area tangent space. Its multiplier is obtained
from the actual full-time flow derivative, not just from matrix algebra. -/

@[expose] public section

noncomputable section

open Set Filter Topology Metric
open scoped NNReal ContDiff

namespace Euler2D

local instance (priority := 2000) periodUnstableC1_group (γ : ℝ≥0) :
    NormedAddCommGroup (ContourC1Space γ) := Submodule.normedAddCommGroup (contourC1GraphSubmodule γ)
local instance (priority := 2000) periodUnstableLittle_group (γ : ℝ≥0) :
    NormedAddCommGroup (LittleContourSpace γ) := Submodule.normedAddCommGroup (LittleContourSpace γ)
local instance (priority := 2000) periodUnstableLittle_space (γ : ℝ≥0) :
    NormedSpace ℝ (LittleContourSpace γ) := Submodule.normedSpace (LittleContourSpace γ)

theorem circularGrowingVariation_mem_fourfold_area {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1) (i : Fin 2) :
    circularGrowingVariation hγ hγ1 0 i ∈
      fourfoldLittleContourSubmodule γ ⊓ LittleContourAreaConstraint γ (circularContourRadii i) := by
  rw [circularGrowingVariation_zero]
  exact circularFourthModeLittle_mem_fourfold_area hγ hγ1.le vPlus circularGrowingTangent i

set_option maxHeartbeats 800000 in
theorem circularPeriod_derivative_growing {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1) {ρ : ℝ} (hρ : 0 < ρ)
    {X : (Fin 2 → LittleContourSpace γ) → ℝ → Fin 2 → LittleContourSpace γ}
    (hX : IsBanachFlowOn (circularBanachField hγ hγ1) (circularBanachDomain hγ hγ1)
      (ball (littleCircularReference hγ hγ1) ρ) period X) :
    fderiv ℝ (fun W => X W period) (littleCircularReference hγ hγ1)
        (circularGrowingVariation hγ hγ1 0) =
      (-lamMult : ℝ) • circularGrowingVariation hγ hγ1 0 := by
  have hU : IsOpen (circularBanachDomain hγ hγ1) :=
    isOpen_phaseAdmissibleLittleContourFamilies _ _
  have hf : ContDiffOn ℝ ∞ (circularBanachField hγ hγ1) (circularBanachDomain hγ hγ1) :=
    contDiffOn_finiteContourPhaseFieldTotal hγ hγ1 _ _ _ _ _ (⊤ : ℕ∞)
  have hX' : IsBanachFlowOn (circularBanachField hγ hγ1) (circularBanachDomain hγ hγ1)
      (ball (littleCircularMaterialContours hγ hγ1 0) ρ) period X := by
    rwa [littleCircularMaterialContours_zero]
  have hYc : Continuous (circularGrowingVariation hγ hγ1) :=
    continuous_iff_continuousAt.mpr (fun t => (circularGrowingVariation_hasDerivAt hγ hγ1 t).continuousAt)
  have he := fderiv_banachFlow_eq_directional_variational_of_compact_reference hU hf
    (contDiff_littleCircularMaterialContours hγ hγ1).continuous
    (isCompact_range_littleCircularMaterialContours hγ hγ1)
    (phaseAdmissible_littleCircularMaterialContours hγ hγ1)
    (littleCircularMaterialContours_hasDerivAt hγ hγ1)
    (show 0 < period by unfold period; positivity) hρ hX' hYc.continuousOn
    (fun t _ => circularGrowingVariation_hasDerivAt hγ hγ1 t)
  simpa only [littleCircularMaterialContours_zero, circularGrowingVariation_period] using he

theorem circularPeriod_derivative_growing_norm_gt {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1) {ρ : ℝ} (hρ : 0 < ρ)
    {X : (Fin 2 → LittleContourSpace γ) → ℝ → Fin 2 → LittleContourSpace γ}
    (hX : IsBanachFlowOn (circularBanachField hγ hγ1) (circularBanachDomain hγ hγ1)
      (ball (littleCircularReference hγ hγ1) ρ) period X) :
    ‖circularGrowingVariation hγ hγ1 0‖ <
      ‖fderiv ℝ (fun W => X W period) (littleCircularReference hγ hγ1)
        (circularGrowingVariation hγ hγ1 0)‖ := by
  rw [circularPeriod_derivative_growing hγ hγ1 hρ hX, ← circularGrowingVariation_period]
  exact norm_circularGrowingVariation_period_gt hγ hγ1

set_option maxHeartbeats 800000 in
theorem exists_circularContour_C3_period_flow_growing {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1) :
    ∃ ρ > 0, ∃ X : (Fin 2 → LittleContourSpace γ) → ℝ → Fin 2 → LittleContourSpace γ,
      IsBanachFlowOn (circularBanachField hγ hγ1) (circularBanachDomain hγ hγ1)
        (ball (littleCircularReference hγ hγ1) ρ) period X ∧
      ContDiffOn ℝ 3 (fun W => X W period) (ball (littleCircularReference hγ hγ1) ρ) ∧
      X (littleCircularReference hγ hγ1) period = littleCircularReference hγ hγ1 ∧
      fderiv ℝ (fun W => X W period) (littleCircularReference hγ hγ1)
          (circularGrowingVariation hγ hγ1 0) =
        (-lamMult : ℝ) • circularGrowingVariation hγ hγ1 0 ∧
      circularGrowingVariation hγ hγ1 0 ≠ 0 ∧
      ∀ i, circularGrowingVariation hγ hγ1 0 i ∈
        fourfoldLittleContourSubmodule γ ⊓ LittleContourAreaConstraint γ (circularContourRadii i) := by
  obtain ⟨ρ, hρ, X, hX, hs, hfix, _⟩ := exists_circularContour_period_flow hγ hγ1 3
  exact ⟨ρ, hρ, X, hX, hs period ⟨by unfold period; positivity, le_rfl⟩, hfix,
    circularPeriod_derivative_growing hγ hγ1 hρ hX, circularGrowingVariation_ne_zero hγ hγ1,
    circularGrowingVariation_mem_fourfold_area hγ hγ1⟩

end Euler2D

end
