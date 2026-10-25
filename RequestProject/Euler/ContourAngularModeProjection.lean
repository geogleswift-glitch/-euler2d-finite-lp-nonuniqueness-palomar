module

public import RequestProject.Euler.CircularFourierRotationProjection
public import RequestProject.Euler.ContourFourierSmoothingMultiplier

/-! Every actual paired angular mode is a Bochner rotation average
in the unchanged little norm; its projection has norm at most two. -/

@[expose] public section

set_option maxHeartbeats 1000000

noncomputable section

open Complex Set Filter Topology MeasureTheory Metric
open scoped NNReal ContDiff

namespace Euler2D

local instance (priority := 2000) angularProjectionLittle_group (γ : ℝ≥0) :
    NormedAddCommGroup (LittleContourSpace γ) := Submodule.normedAddCommGroup (LittleContourSpace γ)
local instance (priority := 2000) angularProjectionLittle_space (γ : ℝ≥0) :
    NormedSpace ℝ (LittleContourSpace γ) := Submodule.normedSpace (LittleContourSpace γ)

theorem cos_int_mul_eq_contourCharacter (m : ℤ) (b : ℝ) :
    (Real.cos ((m : ℝ) * b) : ℂ) =
      (contourCircleCharacter m b + contourCircleCharacter (-m) b) / 2 := by
  rw [Complex.ofReal_cos]
  simp only [Complex.cos, contourCircleCharacter]
  congr 2 <;> push_cast <;> ring

theorem integral_cos_int_contourCharacter (m k : ℤ) :
    (∫ b in (0 : ℝ)..2 * Real.pi,
      (Real.cos ((m : ℝ) * b) : ℂ) * contourCircleCharacter (1 - k) b) =
      (if k = 1 + m then (Real.pi : ℂ) else 0) +
      (if k = 1 - m then (Real.pi : ℂ) else 0) := by
  have he (b : ℝ) :
      (Real.cos ((m : ℝ) * b) : ℂ) * contourCircleCharacter (1 - k) b =
        (contourCircleCharacter (1 + m - k) b + contourCircleCharacter (1 - m - k) b) / 2 := by
    rw [cos_int_mul_eq_contourCharacter]
    calc
      _ = (contourCircleCharacter m b * contourCircleCharacter (1 - k) b +
          contourCircleCharacter (-m) b * contourCircleCharacter (1 - k) b) / 2 := by ring
      _ = _ := by
        rw [contourCircleCharacter_mul, contourCircleCharacter_mul]
        congr 3 <;> omega
  simp_rw [he]
  rw [intervalIntegral.integral_div, intervalIntegral.integral_add
    ((continuous_contourCircleCharacter _).intervalIntegrable _ _)
    ((continuous_contourCircleCharacter _).intervalIntegrable _ _),
    integral_contourCircleCharacter, integral_contourCircleCharacter]
  have hp : 1 + m - k = 0 ↔ k = 1 + m := by omega
  have hn : 1 - m - k = 0 ↔ k = 1 - m := by omega
  simp_rw [hp, hn]
  split_ifs <;> ring

def contourAngularModeProjectionCLM {γ : ℝ≥0} (hγ : 0 < γ) (hγ1 : γ ≤ 1) (m : ℤ) :
    LittleContourSpace γ →L[ℝ] LittleContourSpace γ :=
  littleContourFourierTermCLM hγ hγ1 (1 + m) 1 + littleContourFourierTermCLM hγ hγ1 (1 - m) 1

theorem contourAngularModeProjectionCLM_apply {γ : ℝ≥0} (hγ : 0 < γ) (hγ1 : γ ≤ 1)
    (m : ℤ) (H : LittleContourSpace γ) :
    contourAngularModeProjectionCLM hγ hγ1 m H =
      littleContourFourierMode hγ hγ1 (1 + m) (littleContourFourierCoefficient γ (1 + m) H) +
      littleContourFourierMode hγ hγ1 (1 - m) (littleContourFourierCoefficient γ (1 - m) H) := by
  simp only [contourAngularModeProjectionCLM, ContinuousLinearMap.add_apply,
    littleContourFourierTermCLM_apply, one_mul]

theorem littleContourFourierCoefficient_angularProjection {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : γ ≤ 1) (m k : ℤ) (H : LittleContourSpace γ) :
    littleContourFourierCoefficient γ k (contourAngularModeProjectionCLM hγ hγ1 m H) =
      (if k = 1 + m then littleContourFourierCoefficient γ k H else 0) +
      (if k = 1 - m then littleContourFourierCoefficient γ k H else 0) := by
  rw [contourAngularModeProjectionCLM_apply]
  change littleContourFourierCoefficientCLM γ k (_ + _) = _
  rw [map_add]
  simp only [littleContourFourierCoefficientCLM_apply, littleContourFourierCoefficient_fourierMode]
  have hp : (1 + m = k) = (k = 1 + m) := propext eq_comm
  have hn : (1 - m = k) = (k = 1 - m) := propext eq_comm
  simp only [hp, hn]
  split_ifs <;> simp_all

theorem continuous_contourAngularRotationIntegrand {γ : ℝ≥0} (hγ1 : γ ≤ 1)
    (m : ℤ) (H : LittleContourSpace γ) :
    Continuous (fun b : ℝ => Real.cos ((m : ℝ) * b) • contourRotationLittleCLM γ b H) :=
  (Real.continuous_cos.comp (continuous_const.mul continuous_id)).smul
    (continuous_contourRotationLittleCLM hγ1 H)

def contourAngularRotationAverage (γ : ℝ≥0) (m : ℤ) (H : LittleContourSpace γ) :
    LittleContourSpace γ :=
  (Real.pi⁻¹ : ℝ) • ∫ b in (0 : ℝ)..2 * Real.pi,
    Real.cos ((m : ℝ) * b) • contourRotationLittleCLM γ b H

theorem littleContourFourierCoefficient_angularRotationAverage {γ : ℝ≥0}
    (hγ1 : γ ≤ 1) (m k : ℤ) (H : LittleContourSpace γ) :
    littleContourFourierCoefficient γ k (contourAngularRotationAverage γ m H) =
      (if k = 1 + m then littleContourFourierCoefficient γ k H else 0) +
      (if k = 1 - m then littleContourFourierCoefficient γ k H else 0) := by
  let L := littleContourFourierCoefficientCLM γ k
  have hI := (continuous_contourAngularRotationIntegrand hγ1 m H).intervalIntegrable (μ := volume)
    (0 : ℝ) (2 * Real.pi)
  have he (b : ℝ) : L (Real.cos ((m : ℝ) * b) • contourRotationLittleCLM γ b H) =
      ((Real.cos ((m : ℝ) * b) : ℂ) * contourCircleCharacter (1 - k) b) *
        littleContourFourierCoefficient γ k H := by
    rw [map_smul]
    dsimp only [L]
    rw [littleContourFourierCoefficientCLM_apply, littleContourFourierCoefficient_rotation]
    simp only [Complex.real_smul]
    ring
  change L ((Real.pi⁻¹ : ℝ) • ∫ b in (0 : ℝ)..2 * Real.pi,
    Real.cos ((m : ℝ) * b) • contourRotationLittleCLM γ b H) = _
  rw [map_smul, ← L.intervalIntegral_comp_comm hI]
  simp_rw [he]
  rw [intervalIntegral.integral_mul_const, integral_cos_int_contourCharacter]
  have hp : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  simp only [Complex.real_smul, Complex.ofReal_inv]
  split_ifs <;> field_simp <;> ring

theorem contourAngularModeProjectionCLM_eq_rotationAverage {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : γ ≤ 1) (m : ℤ) (H : LittleContourSpace γ) :
    contourAngularModeProjectionCLM hγ hγ1 m H = contourAngularRotationAverage γ m H := by
  apply littleContourFourierCoefficient_ext
  intro k
  rw [littleContourFourierCoefficient_angularProjection]
  exact (littleContourFourierCoefficient_angularRotationAverage hγ1 m k H).symm

theorem norm_contourAngularModeProjectionCLM_le {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : γ ≤ 1) (m : ℤ) :
    ‖contourAngularModeProjectionCLM hγ hγ1 m‖ ≤ 2 := by
  letI : NormSMulClass ℝ (LittleContourSpace γ) :=
    NormedSpace.toNormSMulClass (𝕜 := ℝ) (E := LittleContourSpace γ)
  apply (contourAngularModeProjectionCLM hγ hγ1 m).opNorm_le_bound (by norm_num)
  intro H
  rw [contourAngularModeProjectionCLM_eq_rotationAverage]
  have hi : ‖∫ b in (0 : ℝ)..2 * Real.pi,
      Real.cos ((m : ℝ) * b) • contourRotationLittleCLM γ b H‖ ≤ ‖H‖ * (2 * Real.pi) := by
    have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ))
      (b := 2 * Real.pi) (C := ‖H‖)
      (f := fun b => Real.cos ((m : ℝ) * b) • contourRotationLittleCLM γ b H)
      (fun b _ => by
        have hr : ‖contourRotationLittleCLM γ b H‖ = ‖H‖ :=
          norm_contourRotationLittleCLM b H
        calc
          ‖Real.cos ((m : ℝ) * b) • contourRotationLittleCLM γ b H‖ =
              ‖Real.cos ((m : ℝ) * b)‖ * ‖contourRotationLittleCLM γ b H‖ :=
            norm_smul _ _
          _ = ‖Real.cos ((m : ℝ) * b)‖ * ‖H‖ :=
            congrArg (fun r : ℝ => ‖Real.cos ((m : ℝ) * b)‖ * r) hr
          _ ≤ ‖H‖ := by
            rw [Real.norm_eq_abs]
            exact (mul_le_mul_of_nonneg_right (Real.abs_cos_le_one _) (norm_nonneg H)).trans_eq (one_mul _))
    calc
      _ ≤ ‖H‖ * |2 * Real.pi - (0 : ℝ)| := h
      _ = _ := by rw [sub_zero, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)]
  change ‖(Real.pi⁻¹ : ℝ) • _‖ ≤ _
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr Real.pi_pos)]
  calc
    _ ≤ Real.pi⁻¹ * (‖H‖ * (2 * Real.pi)) := mul_le_mul_of_nonneg_left hi (by positivity)
    _ = _ := by
      change Real.pi⁻¹ * (‖H‖ * (2 * Real.pi)) = 2 * ‖H‖
      calc
        _ = (Real.pi⁻¹ * Real.pi) * (2 * ‖H‖) := by ring
        _ = _ := by rw [inv_mul_cancel₀ Real.pi_ne_zero, one_mul]

end Euler2D

end
