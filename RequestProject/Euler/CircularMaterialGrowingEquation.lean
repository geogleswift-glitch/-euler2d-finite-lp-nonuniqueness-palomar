module

public import RequestProject.Euler.CircularMaterialFieldMode
public import RequestProject.Euler.ContourShiftedFourierDerivative
public import RequestProject.Euler.CircularComplementAmplitudeBound

/-! The continuous growing-coordinate equation on any real clock,
derived from the original instantaneous field linearization. Only
scalar Fourier coefficients are differentiated under moving shifts. -/

@[expose] public section

set_option maxHeartbeats 16000000
set_option maxRecDepth 7500

noncomputable section

open Complex Set
open scoped NNReal ContDiff

namespace Euler2D

local instance (priority := 2000) materialGrowingLittle_group (γ : ℝ≥0) :
    NormedAddCommGroup (LittleContourSpace γ) := Submodule.normedAddCommGroup (LittleContourSpace γ)
local instance (priority := 2000) materialGrowingLittle_space (γ : ℝ≥0) :
    NormedSpace ℝ (LittleContourSpace γ) := Submodule.normedSpace (LittleContourSpace γ)

theorem hasDerivAt_circularMaterialNormalCoordinate_linearized {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1) (N : ℕ) (a : ℝ)
    {H : ℝ → Fin 2 → LittleContourSpace γ} {p : Fin 2 → LittleContourSpace γ} {t : ℝ}
    (hH : HasDerivAt H
      (a • fderiv ℝ (circularBanachField hγ hγ1) (littleCircularMaterialContours hγ hγ1 (a * t)) (H t) + p) t) :
    let S := fun u => contourParameterShiftFamilyCLM (ι := Fin 2) γ
      (fun i => (-a * circularContourAngularVelocities i) * u)
    let n := fun u => circularModeNormalCoefficientCLM γ N (S u (H u))
    HasDerivAt n (a • circularAngularNormalAmplitude N (n t) +
      circularModeNormalCoefficientCLM γ N (S t p)) t := by
  dsimp only
  let S := fun u => contourParameterShiftFamilyCLM (ι := Fin 2) γ
    (fun i => (-a * circularContourAngularVelocities i) * u)
  let n := fun u => circularModeNormalCoefficientCLM γ N (S u (H u))
  let q := circularModeTangentCoefficientCLM γ N (S t (H t))
  have hphase : (fun i => (-a * circularContourAngularVelocities i) * t) =
      (fun i => -(circularContourAngularVelocities i * (a * t))) := by funext i; ring
  have hcoord : circularModeNormalCoefficientCLM γ N
      (S t (fderiv ℝ (circularBanachField hγ hγ1) (littleCircularMaterialContours hγ hγ1 (a * t)) (H t))) =
      circularMaterialNormalAmplitude N (n t) q := by
    have hc := congrArg Prod.fst (circularMaterialFieldDerivative_all_mode_coordinates hγ hγ1 N (a * t) (H t))
    change circularModeNormalCoefficientCLM γ N
      (contourParameterShiftFamilyCLM γ (fun i => -(circularContourAngularVelocities i * (a * t)))
        (fderiv ℝ (circularBanachField hγ hγ1) (littleCircularMaterialContours hγ hγ1 (a * t)) (H t))) = _ at hc
    simpa only [S, n, q, hphase] using hc
  have hlin : circularModeNormalCoefficientCLM γ N
      (S t (a • fderiv ℝ (circularBanachField hγ hγ1)
        (littleCircularMaterialContours hγ hγ1 (a * t)) (H t) + p)) =
      a • circularMaterialNormalAmplitude N (n t) q + circularModeNormalCoefficientCLM γ N (S t p) := by
    rw [(S t).map_add, (S t).map_smul, (circularModeNormalCoefficientCLM γ N).map_add,
      (circularModeNormalCoefficientCLM γ N).map_smul, hcoord]
  have hd := hasDerivAt_shifted_circularModeNormalCoefficient N
    (fun i => -a * circularContourAngularVelocities i) hH
  change HasDerivAt n (a • circularAngularNormalAmplitude N (n t) + circularModeNormalCoefficientCLM γ N (S t p)) t
  convert hd using 1
  funext i
  change (a • circularAngularNormalAmplitude N (n t) + circularModeNormalCoefficientCLM γ N (S t p)) i =
    circularModeNormalCoefficientCLM γ N
      (S t (a • fderiv ℝ (circularBanachField hγ hγ1)
        (littleCircularMaterialContours hγ hγ1 (a * t)) (H t) + p)) i +
      I * (N + 2 : ℕ) * (((-a * circularContourAngularVelocities i : ℝ)) : ℂ) * n t i -
        (((-a * circularContourAngularVelocities i : ℝ)) : ℂ) * q i
  rw [hlin]
  simp only [Pi.add_apply, Pi.smul_apply, Complex.real_smul]
  rw [← circularAngularNormalAmplitude_material N (n t) q i]
  push_cast
  ring

theorem hasDerivAt_circularMaterialGrowingCoordinate_linearized {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1) (a : ℝ)
    {H : ℝ → Fin 2 → LittleContourSpace γ} {p : Fin 2 → LittleContourSpace γ} {t : ℝ}
    (hH : HasDerivAt H
      (a • fderiv ℝ (circularBanachField hγ hγ1) (littleCircularMaterialContours hγ hγ1 (a * t)) (H t) + p) t) :
    let S := fun u => contourParameterShiftFamilyCLM (ι := Fin 2) γ
      (fun i => (-a * circularContourAngularVelocities i) * u)
    let W := fun u => circularUnstableCoordinateCLM γ (S u (H u))
    HasDerivAt W ((a : ℂ) * lamStar * W t + circularUnstableCoordinateCLM γ (S t p)) t := by
  dsimp only
  let S := fun u => contourParameterShiftFamilyCLM (ι := Fin 2) γ
    (fun i => (-a * circularContourAngularVelocities i) * u)
  let n := fun u => circularModeNormalCoefficientCLM γ 2 (S u (H u))
  have hn := hasDerivAt_circularMaterialNormalCoordinate_linearized hγ hγ1 2 a hH
  have hd := circularEllPlusCLM.hasFDerivAt.comp_hasDerivAt t hn
  have hU (Z : Fin 2 → LittleContourSpace γ) : circularUnstableCoordinateCLM γ Z =
      circularEllPlusCLM (circularModeNormalCoefficientCLM γ 2 Z) := by
    rw [circularEllPlusCLM_apply]
    exact circularUnstableCoordinate_eq_ellPlus_amplitude Z
  simp_rw [hU]
  convert hd using 1
  change (a : ℂ) * lamStar * circularEllPlusCLM (n t) +
      circularEllPlusCLM (circularModeNormalCoefficientCLM γ 2 (S t p)) =
    circularEllPlusCLM (a • circularAngularNormalAmplitude 2 (n t) +
      circularModeNormalCoefficientCLM γ 2 (S t p))
  simp only [map_add, map_smul, circularEllPlusCLM_apply, Complex.real_smul]
  rw [← circularNormalGenerator_apply, ellPlus_circularNormalGenerator]
  ring

end Euler2D

end
