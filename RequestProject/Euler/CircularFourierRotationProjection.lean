module

public import RequestProject.Euler.ContourFourierUniqueness
public import RequestProject.Euler.ContourLittleShiftContinuity
public import RequestProject.Euler.CircularPeriodRotationCovariance
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-! The genuine fourth contour projection is the cosine average of the
strongly continuous weighted rotation action in the original little norm. -/

@[expose] public section

noncomputable section

open Complex Set Filter Topology MeasureTheory Metric
open scoped NNReal ContDiff ComplexConjugate

namespace Euler2D

local instance (priority := 2000) rotationProjectionLittle_group (γ : ℝ≥0) :
    NormedAddCommGroup (LittleContourSpace γ) := Submodule.normedAddCommGroup (LittleContourSpace γ)
local instance (priority := 2000) rotationProjectionLittle_space (γ : ℝ≥0) :
    NormedSpace ℝ (LittleContourSpace γ) := Submodule.normedSpace (LittleContourSpace γ)

theorem littleContourFourierCoefficient_rotation {γ : ℝ≥0}
    (k : ℤ) (b : ℝ) (H : LittleContourSpace γ) :
    littleContourFourierCoefficient γ k (contourRotationLittleCLM γ b H) =
      contourCircleCharacter (1 - k) b * littleContourFourierCoefficient γ k H := by
  let f : ℝ → ℂ := fun θ => LittleContourSpace.lift γ H θ * contourCircleCharacter (-k) θ
  have hp : Function.Periodic f (2 * Real.pi) :=
    (LittleContourSpace.periodic_lift H).mul (periodic_contourCircleCharacter (-k))
  have hshift : (∫ θ in (0 : ℝ)..2 * Real.pi, f (θ - b)) =
      ∫ θ in (0 : ℝ)..2 * Real.pi, f θ := by
    rw [intervalIntegral.integral_comp_sub_right]
    simpa only [zero_sub, sub_eq_add_neg, zero_add, add_comm (2 * Real.pi) (-b)] using
      hp.intervalIntegral_add_eq (-b) 0
  have hi (θ : ℝ) :
      LittleContourSpace.lift γ (contourRotationLittleCLM γ b H) θ *
          contourCircleCharacter (-k) θ = contourCircleCharacter (1 - k) b * f (θ - b) := by
    rw [lift_contourRotationLittleCLM]
    change exp ((b : ℂ) * I) * LittleContourSpace.lift γ H (θ - b) *
      contourCircleCharacter (-k) θ = _
    rw [show θ = (θ - b) + b by ring, contourCircleCharacter_add_arg]
    rw [show 1 - k = 1 + -k by omega, ← contourCircleCharacter_mul]
    dsimp only [f]
    simp only [contourCircleCharacter, Int.cast_one, one_mul]
    ring
  unfold littleContourFourierCoefficient
  simp_rw [hi]
  rw [intervalIntegral.integral_const_mul, hshift]
  dsimp only [f]
  ring

theorem cos_four_mul_eq_character (b : ℝ) :
    (Real.cos (4 * b) : ℂ) =
      (contourCircleCharacter 4 b + contourCircleCharacter (-4) b) / 2 := by
  rw [Complex.ofReal_cos]
  simp only [Complex.cos, contourCircleCharacter]
  congr 2 <;> norm_num <;> push_cast <;> ring

theorem integral_cos_four_character (k : ℤ) :
    (∫ b in (0 : ℝ)..2 * Real.pi,
      (Real.cos (4 * b) : ℂ) * contourCircleCharacter (1 - k) b) =
      (if k = 5 then (Real.pi : ℂ) else 0) +
      (if k = -3 then (Real.pi : ℂ) else 0) := by
  have he (b : ℝ) : (Real.cos (4 * b) : ℂ) * contourCircleCharacter (1 - k) b =
      (contourCircleCharacter (5 - k) b + contourCircleCharacter (-3 - k) b) / 2 := by
    rw [cos_four_mul_eq_character]
    calc
      ((contourCircleCharacter 4 b + contourCircleCharacter (-4) b) / 2) *
          contourCircleCharacter (1 - k) b =
          (contourCircleCharacter 4 b * contourCircleCharacter (1 - k) b +
            contourCircleCharacter (-4) b * contourCircleCharacter (1 - k) b) / 2 := by ring
      _ = _ := by
        rw [contourCircleCharacter_mul, contourCircleCharacter_mul]
        rw [show (4 : ℤ) + (1 - k) = 5 - k by omega,
          show (-4 : ℤ) + (1 - k) = -3 - k by omega]
  simp_rw [he]
  rw [intervalIntegral.integral_div, intervalIntegral.integral_add
    ((continuous_contourCircleCharacter _).intervalIntegrable _ _)
    ((continuous_contourCircleCharacter _).intervalIntegrable _ _),
    integral_contourCircleCharacter, integral_contourCircleCharacter]
  by_cases h5 : k = 5
  · subst k
    norm_num
  · by_cases hn : k = -3
    · subst k
      norm_num
    · have h5' : 5 - k ≠ 0 := by omega
      have hn' : -3 - k ≠ 0 := by omega
      simp only [if_neg h5', if_neg hn', if_neg h5, if_neg hn, zero_add, zero_div]

theorem continuous_contourFourthRotationIntegrand {γ : ℝ≥0}
    (hγ1 : γ ≤ 1) (H : LittleContourSpace γ) :
    Continuous (fun b : ℝ => Real.cos (4 * b) • contourRotationLittleCLM γ b H) :=
  (Real.continuous_cos.comp (continuous_const.mul continuous_id)).smul
    (continuous_contourRotationLittleCLM hγ1 H)

def contourFourthRotationAverage (γ : ℝ≥0) (H : LittleContourSpace γ) :
    LittleContourSpace γ :=
  (Real.pi⁻¹ : ℝ) • ∫ b in (0 : ℝ)..2 * Real.pi,
    Real.cos (4 * b) • contourRotationLittleCLM γ b H

theorem littleContourFourierCoefficient_rotationAverage {γ : ℝ≥0}
    (hγ1 : γ ≤ 1) (k : ℤ) (H : LittleContourSpace γ) :
    littleContourFourierCoefficient γ k (contourFourthRotationAverage γ H) =
      (if k = 5 then littleContourFourierCoefficient γ k H else 0) +
      (if k = -3 then littleContourFourierCoefficient γ k H else 0) := by
  let L := littleContourFourierCoefficientCLM γ k
  have hI := (continuous_contourFourthRotationIntegrand hγ1 H).intervalIntegrable (μ := volume)
    (0 : ℝ) (2 * Real.pi)
  have he (b : ℝ) :
      L (Real.cos (4 * b) • contourRotationLittleCLM γ b H) =
        ((Real.cos (4 * b) : ℂ) * contourCircleCharacter (1 - k) b) *
          littleContourFourierCoefficient γ k H := by
    rw [map_smul]
    dsimp only [L]
    rw [littleContourFourierCoefficientCLM_apply, littleContourFourierCoefficient_rotation]
    simp only [Complex.real_smul]
    ring
  change L ((Real.pi⁻¹ : ℝ) • ∫ b in (0 : ℝ)..2 * Real.pi,
    Real.cos (4 * b) • contourRotationLittleCLM γ b H) = _
  rw [map_smul, ← L.intervalIntegral_comp_comm hI]
  simp_rw [he]
  rw [intervalIntegral.integral_mul_const, integral_cos_four_character]
  have hp : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  simp only [Complex.real_smul, Complex.ofReal_inv]
  by_cases h5 : k = 5
  · subst k
    norm_num
  · by_cases hn : k = -3
    · subst k
      norm_num
    · simp only [if_neg h5, if_neg hn, zero_add, zero_mul, mul_zero]

theorem littleContourFourierCoefficient_fourthProjection {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : γ ≤ 1) (k : ℤ) (H : LittleContourSpace γ) :
    littleContourFourierCoefficient γ k (contourFourthModeProjectionCLM hγ hγ1 H) =
      (if k = 5 then littleContourFourierCoefficient γ k H else 0) +
      (if k = -3 then littleContourFourierCoefficient γ k H else 0) := by
  rw [contourFourthModeProjectionCLM_apply]
  change littleContourFourierCoefficientCLM γ k (_ + _) = _
  rw [map_add]
  simp only [littleContourFourierCoefficientCLM_apply, littleContourFourierCoefficient_fourierMode]
  by_cases h5 : k = 5
  · subst k
    norm_num
  · by_cases hn : k = -3
    · subst k
      norm_num
    · simp only [if_neg h5, if_neg hn, if_neg (Ne.symm h5), if_neg (Ne.symm hn)]

theorem contourFourthModeProjectionCLM_eq_rotationAverage {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : γ ≤ 1) (H : LittleContourSpace γ) :
    contourFourthModeProjectionCLM hγ hγ1 H =
      (Real.pi⁻¹ : ℝ) • ∫ b in (0 : ℝ)..2 * Real.pi,
        Real.cos (4 * b) • contourRotationLittleCLM γ b H := by
  apply littleContourFourierCoefficient_ext
  intro k
  rw [littleContourFourierCoefficient_fourthProjection]
  exact (littleContourFourierCoefficient_rotationAverage hγ1 k H).symm

theorem continuous_contourFourthFamilyRotationIntegrand {γ : ℝ≥0}
    (hγ1 : γ ≤ 1) (H : Fin 2 → LittleContourSpace γ) :
    Continuous (fun b : ℝ => Real.cos (4 * b) • contourRotationFamilyLittleCLM γ b H) := by
  apply continuous_pi
  intro i
  simpa only [Pi.smul_apply, contourRotationFamilyLittleCLM_apply] using
    continuous_contourFourthRotationIntegrand hγ1 (H i)

set_option maxHeartbeats 800000 in
theorem circularFourthModeProjectionCLM_eq_rotationAverage {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : γ ≤ 1) (H : Fin 2 → LittleContourSpace γ) :
    circularFourthModeProjectionCLM hγ hγ1 H =
      (Real.pi⁻¹ : ℝ) • ∫ b in (0 : ℝ)..2 * Real.pi,
        Real.cos (4 * b) • contourRotationFamilyLittleCLM γ b H := by
  have hI := (continuous_contourFourthFamilyRotationIntegrand hγ1 H).intervalIntegrable (μ := volume)
    (0 : ℝ) (2 * Real.pi)
  funext i
  change contourFourthModeProjectionCLM hγ hγ1 (H i) =
    (Real.pi⁻¹ : ℝ) • ((∫ b in (0 : ℝ)..2 * Real.pi,
      Real.cos (4 * b) • contourRotationFamilyLittleCLM γ b H) i)
  let L : (Fin 2 → LittleContourSpace γ) →L[ℝ] LittleContourSpace γ := ContinuousLinearMap.proj i
  have he := L.intervalIntegral_comp_comm hI
  change (∫ b in (0 : ℝ)..2 * Real.pi,
    (Real.cos (4 * b) • contourRotationFamilyLittleCLM γ b H) i) =
      (∫ b in (0 : ℝ)..2 * Real.pi,
        Real.cos (4 * b) • contourRotationFamilyLittleCLM γ b H) i at he
  rw [← he]
  simpa only [Pi.smul_apply, contourRotationFamilyLittleCLM_apply] using
    contourFourthModeProjectionCLM_eq_rotationAverage hγ hγ1 (H i)

set_option maxHeartbeats 800000 in
theorem circularFourthModeProjectionCLM_commute_of_rotation {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : γ ≤ 1)
    (T : (Fin 2 → LittleContourSpace γ) →L[ℝ] (Fin 2 → LittleContourSpace γ))
    (hT : ∀ b : ℝ, T.comp (contourRotationFamilyLittleCLM γ b) =
      (contourRotationFamilyLittleCLM γ b).comp T) :
    T.comp (circularFourthModeProjectionCLM hγ hγ1) =
      (circularFourthModeProjectionCLM hγ hγ1).comp T := by
  apply ContinuousLinearMap.ext
  intro H
  change T (circularFourthModeProjectionCLM hγ hγ1 H) =
    circularFourthModeProjectionCLM hγ hγ1 (T H)
  rw [circularFourthModeProjectionCLM_eq_rotationAverage,
    circularFourthModeProjectionCLM_eq_rotationAverage, map_smul]
  have hI := (continuous_contourFourthFamilyRotationIntegrand hγ1 H).intervalIntegrable (μ := volume)
    (0 : ℝ) (2 * Real.pi)
  rw [← T.intervalIntegral_comp_comm hI]
  congr 1
  apply intervalIntegral.integral_congr
  intro b _
  dsimp only
  rw [map_smul]
  have he := congrArg (fun A : (Fin 2 → LittleContourSpace γ) →L[ℝ]
    (Fin 2 → LittleContourSpace γ) => A H) (hT b)
  exact congrArg (fun Z => Real.cos (4 * b) • Z) he

theorem circularFourthModeProjectionCLM_ker_invariant_of_rotation {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : γ ≤ 1)
    (T : (Fin 2 → LittleContourSpace γ) →L[ℝ] (Fin 2 → LittleContourSpace γ))
    (hT : ∀ b : ℝ, T.comp (contourRotationFamilyLittleCLM γ b) =
      (contourRotationFamilyLittleCLM γ b).comp T)
    {H : Fin 2 → LittleContourSpace γ} (hH : H ∈ (circularFourthModeProjectionCLM hγ hγ1).ker) :
    T H ∈ (circularFourthModeProjectionCLM hγ hγ1).ker := by
  change circularFourthModeProjectionCLM hγ hγ1 (T H) = 0
  have he := congrArg (fun A : (Fin 2 → LittleContourSpace γ) →L[ℝ]
    (Fin 2 → LittleContourSpace γ) => A H)
    (circularFourthModeProjectionCLM_commute_of_rotation hγ hγ1 T hT)
  change T (circularFourthModeProjectionCLM hγ hγ1 H) =
    circularFourthModeProjectionCLM hγ hγ1 (T H) at he
  rw [← he]
  change circularFourthModeProjectionCLM hγ hγ1 H = 0 at hH
  rw [hH, map_zero]

theorem circularPeriod_derivative_fourthProjection_commute {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1) {ρ : ℝ} (hρ : 0 < ρ)
    {X : (Fin 2 → LittleContourSpace γ) → ℝ → Fin 2 → LittleContourSpace γ}
    (hX : IsBanachFlowOn (circularBanachField hγ hγ1) (circularBanachDomain hγ hγ1)
      (ball (littleCircularReference hγ hγ1) ρ) period X)
    (hd : DifferentiableAt ℝ (fun W => X W period) (littleCircularReference hγ hγ1)) :
    (fderiv ℝ (fun W => X W period) (littleCircularReference hγ hγ1)).comp
        (circularFourthModeProjectionCLM hγ hγ1.le) =
      (circularFourthModeProjectionCLM hγ hγ1.le).comp
        (fderiv ℝ (fun W => X W period) (littleCircularReference hγ hγ1)) :=
  circularFourthModeProjectionCLM_commute_of_rotation hγ hγ1.le _
    (fun b => circularPeriod_derivative_rotation_commute hγ hγ1 hρ hX hd b)

theorem circularPeriod_derivative_fourthComplement_invariant {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1) {ρ : ℝ} (hρ : 0 < ρ)
    {X : (Fin 2 → LittleContourSpace γ) → ℝ → Fin 2 → LittleContourSpace γ}
    (hX : IsBanachFlowOn (circularBanachField hγ hγ1) (circularBanachDomain hγ hγ1)
      (ball (littleCircularReference hγ hγ1) ρ) period X)
    (hd : DifferentiableAt ℝ (fun W => X W period) (littleCircularReference hγ hγ1))
    {H : Fin 2 → LittleContourSpace γ}
    (hH : H ∈ (circularFourthModeProjectionCLM hγ hγ1.le).ker) :
    fderiv ℝ (fun W => X W period) (littleCircularReference hγ hγ1) H ∈
      (circularFourthModeProjectionCLM hγ hγ1.le).ker :=
  circularFourthModeProjectionCLM_ker_invariant_of_rotation hγ hγ1.le _
    (fun b => circularPeriod_derivative_rotation_commute hγ hγ1 hρ hX hd b) hH


end Euler2D

end
