module

public import RequestProject.Euler.CircularReferencePhases

/-! One fixed material reparametrization at a stage entrance preserves
the actual isolated equation and the original norm of its forcing.
The stage clock and the physical spatial gauge remain fixed. -/

@[expose] public section

set_option maxHeartbeats 2000000
set_option maxRecDepth 4000

noncomputable section

open Set
open scoped NNReal

namespace Euler2D

local instance (priority := 2000) fixedMaterialForcingLittle_group (γ : ℝ≥0) :
    NormedAddCommGroup (LittleContourSpace γ) := Submodule.normedAddCommGroup (LittleContourSpace γ)
local instance (priority := 2000) fixedMaterialForcingLittle_space (γ : ℝ≥0) :
    NormedSpace ℝ (LittleContourSpace γ) := Submodule.normedSpace (LittleContourSpace γ)

attribute [local irreducible] circularBanachField circularBanachDomain

theorem hasDerivAt_fixedMaterialShift_forcedCircularCurve {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1) (b : Fin 2 → ℝ)
    {y p : ℝ → Fin 2 → LittleContourSpace γ} {t : ℝ}
    (hm : y t ∈ circularBanachDomain hγ hγ1)
    (hd : HasDerivAt y (circularBanachField hγ hγ1 (y t) + p t) t) :
    HasDerivAt (fun s => contourParameterShiftFamilyCLM γ b (y s))
      (circularBanachField hγ hγ1 (contourParameterShiftFamilyCLM γ b (y t)) +
        contourParameterShiftFamilyCLM γ b (p t)) t := by
  let S := contourParameterShiftFamilyCLM γ b
  have hh := S.hasFDerivAt.comp_hasDerivAt t hd
  change HasDerivAt (fun s => S (y s)) (S (circularBanachField hγ hγ1 (y t) + p t)) t at hh
  rw [S.map_add, ← circularBanachField_parameterShift hγ hγ1 b hm] at hh
  exact hh

theorem fixedMaterialShift_forcing_budget {γ : ℝ≥0} (b : Fin 2 → ℝ)
    {p : ℝ → Fin 2 → LittleContourSpace γ} {ε : ℝ} {J : Set ℝ}
    (hp : ∀ t ∈ J, ‖p t‖ ≤ ε) :
    ∀ t ∈ J, ‖contourParameterShiftFamilyCLM γ b (p t)‖ ≤ ε := by
  intro t ht
  rw [norm_contourParameterShiftFamilyCLM]
  exact hp t ht

end Euler2D

end
