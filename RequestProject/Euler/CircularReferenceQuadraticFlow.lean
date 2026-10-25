module

public import RequestProject.Euler.BanachReferenceQuadraticVariation
public import RequestProject.Euler.CircularReferenceCompactness
public import RequestProject.Euler.CircularContourPeriodMap

/-! A genuine full fundamental operator and a uniform quadratic
material-flow error for the original circular contour dynamics. -/

@[expose] public section

set_option maxHeartbeats 4000000
set_option maxRecDepth 4000

noncomputable section

open Set Filter Topology Metric
open scoped NNReal ContDiff

namespace Euler2D

local instance (priority := 2000) quadraticReferenceC1_group (γ : ℝ≥0) :
    NormedAddCommGroup (ContourC1Space γ) := Submodule.normedAddCommGroup (contourC1GraphSubmodule γ)
local instance (priority := 2000) quadraticReferenceLittle_group (γ : ℝ≥0) :
    NormedAddCommGroup (LittleContourSpace γ) := Submodule.normedAddCommGroup (LittleContourSpace γ)
local instance (priority := 2000) quadraticReferenceLittle_space (γ : ℝ≥0) :
    NormedSpace ℝ (LittleContourSpace γ) := Submodule.normedSpace (LittleContourSpace γ)
local instance (priority := 2000) quadraticReferenceFamily_tower (γ : ℝ≥0) :
    IsScalarTower ℝ ℝ (Fin 2 → LittleContourSpace γ) where
  smul_assoc a b Z := by
    funext i
    change (a * b) • Z i = a • (b • Z i)
    exact (smul_smul a b (Z i)).symm

theorem exists_circularReference_quadratic_variation {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1) {T ρ : ℝ} (hT : 0 < T) (hρ : 0 < ρ)
    {X : (Fin 2 → LittleContourSpace γ) → ℝ → Fin 2 → LittleContourSpace γ}
    (hX : IsBanachFlowOn (circularBanachField hγ hγ1) (circularBanachDomain hγ hγ1)
      (ball (littleCircularReference hγ hγ1) ρ) T X) :
    ∃ A : ℝ → (Fin 2 → LittleContourSpace γ) →L[ℝ] (Fin 2 → LittleContourSpace γ),
      Continuous A ∧ A 0 = ContinuousLinearMap.id ℝ (Fin 2 → LittleContourSpace γ) ∧
      (∀ t ∈ Icc (0 : ℝ) T, HasDerivAt A
        ((fderiv ℝ (circularBanachField hγ hγ1) (littleCircularMaterialContours hγ hγ1 t)).comp (A t)) t) ∧
      ∃ δ > 0, ∃ C > 0, ∀ h : Fin 2 → LittleContourSpace γ, ‖h‖ ≤ δ → ∀ t ∈ Icc (0 : ℝ) T,
        ‖X (littleCircularReference hγ hγ1 + h) t - littleCircularMaterialContours hγ hγ1 t - A t h‖ ≤
          C * ‖h‖ ^ 2 := by
  have hU : IsOpen (circularBanachDomain hγ hγ1) :=
    isOpen_phaseAdmissibleLittleContourFamilies _ _
  have hf : ContDiffOn ℝ ∞ (circularBanachField hγ hγ1) (circularBanachDomain hγ hγ1) :=
    contDiffOn_finiteContourPhaseFieldTotal hγ hγ1 _ _ _ _ _ (⊤ : ℕ∞)
  have hX' : IsBanachFlowOn (circularBanachField hγ hγ1) (circularBanachDomain hγ hγ1)
      (ball (littleCircularMaterialContours hγ hγ1 0) ρ) T X := by
    simpa only [littleCircularMaterialContours_zero] using hX
  have he := exists_banachFlow_reference_quadratic_variation hU hf
    (contDiff_littleCircularMaterialContours hγ hγ1).continuous
    (isCompact_range_littleCircularMaterialContours hγ hγ1)
    (phaseAdmissible_littleCircularMaterialContours hγ hγ1)
    (littleCircularMaterialContours_hasDerivAt hγ hγ1) hT hρ hX'
  simpa only [littleCircularMaterialContours_zero] using he

end Euler2D

end
