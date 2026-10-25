module

public import RequestProject.Euler.ContourAngularModeProjection

/-! Actual paired angular projections on the full contour family
commute with the genuine period derivative at every integer frequency. -/

@[expose] public section

set_option maxHeartbeats 1000000

noncomputable section

open Complex Set Filter Topology MeasureTheory Metric
open scoped NNReal ContDiff

namespace Euler2D

local instance (priority := 2000) familyAngularLittle_group (γ : ℝ≥0) :
    NormedAddCommGroup (LittleContourSpace γ) := Submodule.normedAddCommGroup (LittleContourSpace γ)
local instance (priority := 2000) familyAngularLittle_space (γ : ℝ≥0) :
    NormedSpace ℝ (LittleContourSpace γ) := Submodule.normedSpace (LittleContourSpace γ)

def circularAngularModeProjectionCLM {γ : ℝ≥0} (hγ : 0 < γ) (hγ1 : γ ≤ 1) (m : ℤ) :
    (Fin 2 → LittleContourSpace γ) →L[ℝ] (Fin 2 → LittleContourSpace γ) :=
  ContinuousLinearMap.pi (fun i => (contourAngularModeProjectionCLM hγ hγ1 m).comp
    (ContinuousLinearMap.proj i))

@[simp] theorem circularAngularModeProjectionCLM_apply {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : γ ≤ 1) (m : ℤ) (H : Fin 2 → LittleContourSpace γ) (i : Fin 2) :
    circularAngularModeProjectionCLM hγ hγ1 m H i = contourAngularModeProjectionCLM hγ hγ1 m (H i) := rfl

theorem norm_circularAngularModeProjectionCLM_le {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : γ ≤ 1) (m : ℤ) :
    ‖circularAngularModeProjectionCLM hγ hγ1 m‖ ≤ 2 := by
  apply (circularAngularModeProjectionCLM hγ hγ1 m).opNorm_le_bound (by norm_num)
  intro H
  apply (pi_norm_le_iff_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * ‖H‖)).mpr
  intro i
  change ‖contourAngularModeProjectionCLM hγ hγ1 m (H i)‖ ≤ _
  exact ((contourAngularModeProjectionCLM hγ hγ1 m).le_opNorm (H i)).trans
    (mul_le_mul (norm_contourAngularModeProjectionCLM_le hγ hγ1 m)
      (norm_le_pi_norm H i) (norm_nonneg _) (by norm_num))

theorem continuous_circularAngularRotationIntegrand {γ : ℝ≥0} (hγ1 : γ ≤ 1)
    (m : ℤ) (H : Fin 2 → LittleContourSpace γ) :
    Continuous (fun b : ℝ => Real.cos ((m : ℝ) * b) • contourRotationFamilyLittleCLM γ b H) := by
  apply continuous_pi
  intro i
  simpa only [Pi.smul_apply, contourRotationFamilyLittleCLM_apply] using
    continuous_contourAngularRotationIntegrand hγ1 m (H i)

theorem circularAngularModeProjectionCLM_eq_rotationAverage {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : γ ≤ 1) (m : ℤ) (H : Fin 2 → LittleContourSpace γ) :
    circularAngularModeProjectionCLM hγ hγ1 m H =
      (Real.pi⁻¹ : ℝ) • ∫ b in (0 : ℝ)..2 * Real.pi,
        Real.cos ((m : ℝ) * b) • contourRotationFamilyLittleCLM γ b H := by
  have hI := (continuous_circularAngularRotationIntegrand hγ1 m H).intervalIntegrable (μ := volume)
    (0 : ℝ) (2 * Real.pi)
  funext i
  change contourAngularModeProjectionCLM hγ hγ1 m (H i) =
    (Real.pi⁻¹ : ℝ) • ((∫ b in (0 : ℝ)..2 * Real.pi,
      Real.cos ((m : ℝ) * b) • contourRotationFamilyLittleCLM γ b H) i)
  let L : (Fin 2 → LittleContourSpace γ) →L[ℝ] LittleContourSpace γ := ContinuousLinearMap.proj i
  have he := L.intervalIntegral_comp_comm hI
  change (∫ b in (0 : ℝ)..2 * Real.pi,
    (Real.cos ((m : ℝ) * b) • contourRotationFamilyLittleCLM γ b H) i) =
      (∫ b in (0 : ℝ)..2 * Real.pi,
        Real.cos ((m : ℝ) * b) • contourRotationFamilyLittleCLM γ b H) i at he
  rw [← he]
  simpa only [Pi.smul_apply, contourRotationFamilyLittleCLM_apply, contourAngularRotationAverage] using
    contourAngularModeProjectionCLM_eq_rotationAverage hγ hγ1 m (H i)

theorem circularAngularModeProjectionCLM_commute_of_rotation {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : γ ≤ 1) (m : ℤ)
    (T : (Fin 2 → LittleContourSpace γ) →L[ℝ] (Fin 2 → LittleContourSpace γ))
    (hT : ∀ b : ℝ, T.comp (contourRotationFamilyLittleCLM γ b) =
      (contourRotationFamilyLittleCLM γ b).comp T) :
    T.comp (circularAngularModeProjectionCLM hγ hγ1 m) =
      (circularAngularModeProjectionCLM hγ hγ1 m).comp T := by
  apply ContinuousLinearMap.ext
  intro H
  change T (circularAngularModeProjectionCLM hγ hγ1 m H) =
    circularAngularModeProjectionCLM hγ hγ1 m (T H)
  rw [circularAngularModeProjectionCLM_eq_rotationAverage,
    circularAngularModeProjectionCLM_eq_rotationAverage, map_smul]
  have hI := (continuous_circularAngularRotationIntegrand hγ1 m H).intervalIntegrable (μ := volume)
    (0 : ℝ) (2 * Real.pi)
  rw [← T.intervalIntegral_comp_comm hI]
  congr 1
  apply intervalIntegral.integral_congr
  intro b _
  dsimp only
  rw [map_smul]
  have he := congrArg (fun A : (Fin 2 → LittleContourSpace γ) →L[ℝ]
    (Fin 2 → LittleContourSpace γ) => A H) (hT b)
  exact congrArg (fun Z => Real.cos ((m : ℝ) * b) • Z) he

theorem circularPeriod_derivative_angularProjection_commute {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1) {ρ : ℝ} (hρ : 0 < ρ)
    {X : (Fin 2 → LittleContourSpace γ) → ℝ → Fin 2 → LittleContourSpace γ}
    (hX : IsBanachFlowOn (circularBanachField hγ hγ1) (circularBanachDomain hγ hγ1)
      (ball (littleCircularReference hγ hγ1) ρ) period X)
    (hd : DifferentiableAt ℝ (fun W => X W period) (littleCircularReference hγ hγ1)) (m : ℤ) :
    (fderiv ℝ (fun W => X W period) (littleCircularReference hγ hγ1)).comp
        (circularAngularModeProjectionCLM hγ hγ1.le m) =
      (circularAngularModeProjectionCLM hγ hγ1.le m).comp
        (fderiv ℝ (fun W => X W period) (littleCircularReference hγ hγ1)) :=
  circularAngularModeProjectionCLM_commute_of_rotation hγ hγ1.le m _
    (fun b => circularPeriod_derivative_rotation_commute hγ hγ1 hρ hX hd b)

end Euler2D

end
