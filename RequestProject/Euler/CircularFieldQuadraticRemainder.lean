module

public import RequestProject.Euler.BanachCompactQuadraticTaylor
public import RequestProject.Euler.CircularReferenceCompactness
public import RequestProject.Euler.CircularContourPeriodMap

/-! A uniform quadratic Taylor remainder for the original contour
field about every time on the actual circular material orbit. The
nonlinear error is derived from the original smooth field. -/

@[expose] public section

set_option maxHeartbeats 5000000
set_option maxRecDepth 5500

noncomputable section

open Set Filter Topology Metric
open scoped NNReal ContDiff

namespace Euler2D

local instance (priority := 2000) fieldQuadraticLittle_group (γ : ℝ≥0) :
    NormedAddCommGroup (LittleContourSpace γ) := Submodule.normedAddCommGroup (LittleContourSpace γ)
local instance (priority := 2000) fieldQuadraticLittle_space (γ : ℝ≥0) :
    NormedSpace ℝ (LittleContourSpace γ) := Submodule.normedSpace (LittleContourSpace γ)

theorem exists_circularField_uniform_quadratic_remainder {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1) :
    ∃ C > 0, ∃ r > 0, ∀ (t : ℝ) (H : Fin 2 → LittleContourSpace γ), ‖H‖ ≤ r →
      littleCircularMaterialContours hγ hγ1 t + H ∈ circularBanachDomain hγ hγ1 ∧
      ‖circularBanachField hγ hγ1 (littleCircularMaterialContours hγ hγ1 t + H) -
          circularBanachField hγ hγ1 (littleCircularMaterialContours hγ hγ1 t) -
            fderiv ℝ (circularBanachField hγ hγ1) (littleCircularMaterialContours hγ hγ1 t) H‖ ≤
        C * ‖H‖ ^ 2 := by
  have hU : IsOpen (circularBanachDomain hγ hγ1) := isOpen_phaseAdmissibleLittleContourFamilies _ _
  have hf : ContDiffOn ℝ 2 (circularBanachField hγ hγ1) (circularBanachDomain hγ hγ1) :=
    contDiffOn_finiteContourPhaseFieldTotal hγ hγ1 _ _ _ _ _ 2
  obtain ⟨K, r, hr, hquad⟩ := exists_uniform_quadratic_taylor_on_compact hU hf
    (isCompact_range_littleCircularMaterialContours hγ hγ1)
    (by rintro _ ⟨t, rfl⟩; exact phaseAdmissible_littleCircularMaterialContours hγ hγ1 t)
  refine ⟨(K : ℝ) + 1, by positivity, r, hr, ?_⟩
  intro t H hH
  obtain ⟨hmem, he⟩ := hquad _ (mem_range_self t) H hH
  exact ⟨hmem, he.trans (mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg ‖H‖))⟩

end Euler2D

end
