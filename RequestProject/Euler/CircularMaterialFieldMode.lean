module

public import RequestProject.Euler.CircularFieldModeDerivative

/-! The instantaneous normal/tangential linearization in the true
material parameters, valid for an arbitrary original perturbation. -/

@[expose] public section

set_option maxHeartbeats 7000000
set_option maxRecDepth 6500

noncomputable section

open Complex Set
open scoped NNReal ContDiff

namespace Euler2D

local instance (priority := 2000) materialFieldModeLittle_group (γ : ℝ≥0) :
    NormedAddCommGroup (LittleContourSpace γ) := Submodule.normedAddCommGroup (LittleContourSpace γ)
local instance (priority := 2000) materialFieldModeLittle_space (γ : ℝ≥0) :
    NormedSpace ℝ (LittleContourSpace γ) := Submodule.normedSpace (LittleContourSpace γ)

theorem circularMaterialFieldDerivative_all_mode_coordinates {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1) (N : ℕ) (t : ℝ) (H : Fin 2 → LittleContourSpace γ) :
    circularModeAmplitudeCoefficientCLM γ N
        (contourParameterShiftFamilyCLM γ (fun i => -(circularContourAngularVelocities i * t))
          (fderiv ℝ (circularBanachField hγ hγ1) (littleCircularMaterialContours hγ hγ1 t) H)) =
      (circularMaterialNormalAmplitude N
        (circularModeNormalCoefficientCLM γ N
          (contourParameterShiftFamilyCLM γ (fun i => -(circularContourAngularVelocities i * t)) H))
        (circularModeTangentCoefficientCLM γ N
          (contourParameterShiftFamilyCLM γ (fun i => -(circularContourAngularVelocities i * t)) H)),
      circularMaterialTangentialAmplitude N
        (circularModeNormalCoefficientCLM γ N
          (contourParameterShiftFamilyCLM γ (fun i => -(circularContourAngularVelocities i * t)) H))) := by
  let σ : Fin 2 → ℝ := fun i => circularContourAngularVelocities i * t
  let S := contourParameterShiftFamilyCLM (ι := Fin 2) γ σ
  let B := contourParameterShiftFamilyCLM (ι := Fin 2) γ (-σ)
  have hSB (Z : Fin 2 → LittleContourSpace γ) : S (B Z) = Z := by
    change contourParameterShiftFamilyCLM γ σ (contourParameterShiftFamilyCLM γ (-σ) Z) = Z
    rw [contourParameterShiftFamilyCLM_add, add_neg_cancel, contourParameterShiftFamilyCLM_zero]
  have hBS (Z : Fin 2 → LittleContourSpace γ) : B (S Z) = Z := by
    change contourParameterShiftFamilyCLM γ (-σ) (contourParameterShiftFamilyCLM γ σ Z) = Z
    rw [contourParameterShiftFamilyCLM_add, neg_add_cancel, contourParameterShiftFamilyCLM_zero]
  have he : B (fderiv ℝ (circularBanachField hγ hγ1) (littleCircularMaterialContours hγ hγ1 t) H) =
      fderiv ℝ (circularBanachField hγ hγ1) (littleCircularReference hγ hγ1) (B H) := by
    conv_lhs => rw [← hSB H, fderiv_circularBanachField_material_orbit]
    exact hBS _
  change circularModeAmplitudeCoefficientCLM γ N
    (B (fderiv ℝ (circularBanachField hγ hγ1) (littleCircularMaterialContours hγ hγ1 t) H)) = _
  rw [he]
  exact circularFieldDerivative_all_mode_coordinates hγ hγ1 N (B H)

end Euler2D

end
