module

public import RequestProject.Euler.CircularFourierCoordinates
public import RequestProject.Euler.CircularOrbitNormalFourier
public import RequestProject.Euler.CircularPeriodRotationCovariance

/-! The derivative of the actual instantaneous field commutes with
every angular projection. Thus its normal/tangential mode equations
hold on arbitrary perturbations, rather than only finite-mode inputs. -/

@[expose] public section

set_option maxHeartbeats 7000000
set_option maxRecDepth 6500

noncomputable section

open Complex Set Filter Topology Metric
open scoped NNReal ContDiff

namespace Euler2D

local instance (priority := 2000) fieldModeLittle_group (γ : ℝ≥0) :
    NormedAddCommGroup (LittleContourSpace γ) := Submodule.normedAddCommGroup (LittleContourSpace γ)
local instance (priority := 2000) fieldModeLittle_space (γ : ℝ≥0) :
    NormedSpace ℝ (LittleContourSpace γ) := Submodule.normedSpace (LittleContourSpace γ)

theorem fderiv_circularBanachField_reference_rotation_commute {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1) (b : ℝ) :
    (fderiv ℝ (circularBanachField hγ hγ1) (littleCircularReference hγ hγ1)).comp
        (contourRotationFamilyLittleCLM γ b) =
      (contourRotationFamilyLittleCLM γ b).comp
        (fderiv ℝ (circularBanachField hγ hγ1) (littleCircularReference hγ hγ1)) := by
  let c := littleCircularReference hγ hγ1
  let R := contourRotationFamilyLittleCLM (ι := Fin 2) γ b
  have hU : IsOpen (circularBanachDomain hγ hγ1) := isOpen_phaseAdmissibleLittleContourFamilies _ _
  have hcU : c ∈ circularBanachDomain hγ hγ1 := by
    change IsPhaseAdmissibleLittleContourFamily (circularReferenceC1 hγ hγ1)
      circularContourRadii (littleCircularReference hγ hγ1)
    simpa only [littleCircularMaterialContours_zero] using phaseAdmissible_littleCircularMaterialContours hγ hγ1 0
  have hf : ContDiffOn ℝ 1 (circularBanachField hγ hγ1) (circularBanachDomain hγ hγ1) :=
    contDiffOn_finiteContourPhaseFieldTotal hγ hγ1 _ _ _ _ _ 1
  have hd : DifferentiableAt ℝ (circularBanachField hγ hγ1) c :=
    (hf.contDiffAt (hU.mem_nhds hcU)).differentiableAt (by norm_num)
  have hfix : R c = c := contourRotationFamilyLittleCLM_reference hγ hγ1 b
  have hleft := (show HasFDerivAt (circularBanachField hγ hγ1)
      (fderiv ℝ (circularBanachField hγ hγ1) c) (R c) by rw [hfix]; exact hd.hasFDerivAt).comp c R.hasFDerivAt
  have hright := R.hasFDerivAt.comp c hd.hasFDerivAt
  have he : (fun W => circularBanachField hγ hγ1 (R W)) =ᶠ[𝓝 c]
      (fun W => R (circularBanachField hγ hγ1 W)) := by
    filter_upwards [hU.mem_nhds hcU] with W hW
    exact circularBanachField_rotation hγ hγ1 b hW
  exact hleft.unique (hright.congr_of_eventuallyEq he)

theorem fderiv_circularBanachField_reference_angularProjection_commute {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1) (m : ℤ) :
    (fderiv ℝ (circularBanachField hγ hγ1) (littleCircularReference hγ hγ1)).comp
        (circularAngularModeProjectionCLM hγ hγ1.le m) =
      (circularAngularModeProjectionCLM hγ hγ1.le m).comp
        (fderiv ℝ (circularBanachField hγ hγ1) (littleCircularReference hγ hγ1)) :=
  circularAngularModeProjectionCLM_commute_of_rotation hγ hγ1.le m _
    (fderiv_circularBanachField_reference_rotation_commute hγ hγ1)

theorem circularFieldDerivative_all_mode_coordinates {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1) (N : ℕ) (H : Fin 2 → LittleContourSpace γ) :
    circularModeAmplitudeCoefficientCLM γ N
        (fderiv ℝ (circularBanachField hγ hγ1) (littleCircularReference hγ hγ1) H) =
      (circularMaterialNormalAmplitude N (circularModeNormalCoefficientCLM γ N H)
          (circularModeTangentCoefficientCLM γ N H),
        circularMaterialTangentialAmplitude N (circularModeNormalCoefficientCLM γ N H)) := by
  have hγle : γ ≤ 1 := by exact_mod_cast hγ1.le
  let D := fderiv ℝ (circularBanachField hγ hγ1) (littleCircularReference hγ hγ1)
  let P := circularAngularModeProjectionCLM hγ hγle ((N + 2 : ℕ) : ℤ)
  have he : D (P H) = P (D H) := congrArg (fun A => A H)
    (fderiv_circularBanachField_reference_angularProjection_commute hγ hγ1 ((N + 2 : ℕ) : ℤ))
  change circularModeAmplitudeCoefficientCLM γ N (D H) = _
  rw [← circularModeAmplitudeCoefficientCLM_projection hγ hγle N (D H), ← he]
  dsimp only [D, P]
  rw [circularAngularModeProjectionCLM_eq_normalMode hγ hγle N H]
  have hmode : fderiv ℝ (circularBanachField hγ hγ1) (littleCircularReference hγ hγ1)
      (circularNormalModeLittle hγ hγle N
        (circularModeNormalCoefficientCLM γ N H) (circularModeTangentCoefficientCLM γ N H)) =
    circularNormalModeLittle hγ hγle N
      (circularMaterialNormalAmplitude N (circularModeNormalCoefficientCLM γ N H)
        (circularModeTangentCoefficientCLM γ N H))
      (circularMaterialTangentialAmplitude N (circularModeNormalCoefficientCLM γ N H)) :=
    fderiv_circularBanachField_mode hγ hγ1 N
      (circularModeNormalCoefficientCLM γ N H) (circularModeTangentCoefficientCLM γ N H)
  rw [hmode]
  exact circularModeAmplitudeCoefficientCLM_normalMode hγ hγle N
    (circularMaterialNormalAmplitude N (circularModeNormalCoefficientCLM γ N H)
      (circularModeTangentCoefficientCLM γ N H),
      circularMaterialTangentialAmplitude N (circularModeNormalCoefficientCLM γ N H))

end Euler2D

end
