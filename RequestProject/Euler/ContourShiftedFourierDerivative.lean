module

public import RequestProject.Euler.CircularFourierCoordinates
public import RequestProject.Euler.ContourFourierModeCalculus
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-! A moving parameter shift need not be differentiable in the full
little C1 norm. Its actual Fourier coefficients are differentiable:
their explicit scalar phases give the required transport terms. -/

@[expose] public section

set_option maxHeartbeats 9000000
set_option maxRecDepth 6500

noncomputable section

open Complex Set Filter Topology MeasureTheory
open scoped NNReal ContDiff ComplexConjugate

namespace Euler2D

local instance (priority := 2000) shiftedFourierLittle_group (γ : ℝ≥0) :
    NormedAddCommGroup (LittleContourSpace γ) := Submodule.normedAddCommGroup (LittleContourSpace γ)
local instance (priority := 2000) shiftedFourierLittle_space (γ : ℝ≥0) :
    NormedSpace ℝ (LittleContourSpace γ) := Submodule.normedSpace (LittleContourSpace γ)

theorem littleContourFourierCoefficient_parameterShift {γ : ℝ≥0}
    (k : ℤ) (b : ℝ) (H : LittleContourSpace γ) :
    littleContourFourierCoefficient γ k (contourParameterShiftLittleCLM γ b H) =
      contourCircleCharacter k b * littleContourFourierCoefficient γ k H := by
  let f : ℝ → ℂ := fun θ => LittleContourSpace.lift γ H θ * contourCircleCharacter (-k) θ
  have hp : Function.Periodic f (2 * Real.pi) :=
    (LittleContourSpace.periodic_lift H).mul (periodic_contourCircleCharacter (-k))
  have hshift : (∫ θ in (0 : ℝ)..2 * Real.pi, f (θ + b)) =
      ∫ θ in (0 : ℝ)..2 * Real.pi, f θ := by
    rw [intervalIntegral.integral_comp_add_right]
    simpa only [zero_add, add_comm b (2 * Real.pi)] using hp.intervalIntegral_add_eq b 0
  have hcancel : contourCircleCharacter k b * contourCircleCharacter (-k) b = 1 := by
    rw [contourCircleCharacter_mul, add_neg_cancel]
    simp only [contourCircleCharacter, Int.cast_zero, zero_mul, Complex.exp_zero]
  have hi (θ : ℝ) : LittleContourSpace.lift γ (contourParameterShiftLittleCLM γ b H) θ *
      contourCircleCharacter (-k) θ = contourCircleCharacter k b * f (θ + b) := by
    rw [lift_contourParameterShiftLittleCLM]
    dsimp only [f]
    rw [contourCircleCharacter_add_arg]
    calc
      _ = (contourCircleCharacter k b * contourCircleCharacter (-k) b) *
          (LittleContourSpace.lift γ H (θ + b) * contourCircleCharacter (-k) θ) := by rw [hcancel, one_mul]
      _ = _ := by ring
  unfold littleContourFourierCoefficient
  simp_rw [hi]
  rw [intervalIntegral.integral_const_mul, hshift]
  dsimp only [f]
  ring

theorem hasDerivAt_littleContourFourierCoefficient_variableShift {γ : ℝ≥0}
    (k : ℤ) {H : ℝ → LittleContourSpace γ} {H' : LittleContourSpace γ}
    {b : ℝ → ℝ} {b' t : ℝ} (hH : HasDerivAt H H' t) (hb : HasDerivAt b b' t) :
    HasDerivAt (fun u => littleContourFourierCoefficient γ k (contourParameterShiftLittleCLM γ (b u) (H u)))
      (littleContourFourierCoefficient γ k (contourParameterShiftLittleCLM γ (b t) H') +
        (k : ℂ) * I * (b' : ℂ) *
          littleContourFourierCoefficient γ k (contourParameterShiftLittleCLM γ (b t) (H t))) t := by
  simp_rw [littleContourFourierCoefficient_parameterShift]
  have hcoef := (littleContourFourierCoefficientCLM γ k).hasFDerivAt.comp_hasDerivAt t hH
  have hd := (hasDerivAt_contourCircleCharacter_comp k hb).mul hcoef
  convert hd using 1 <;> simp only [Function.comp_def, littleContourFourierCoefficientCLM_apply] <;> ring

theorem hasDerivAt_shifted_circularModeNormalCoefficient {γ : ℝ≥0} (N : ℕ)
    (v : Fin 2 → ℝ) {H : ℝ → Fin 2 → LittleContourSpace γ} {H' : Fin 2 → LittleContourSpace γ}
    {t : ℝ} (hH : HasDerivAt H H' t) :
    HasDerivAt (fun u => circularModeNormalCoefficientCLM γ N
        (contourParameterShiftFamilyCLM γ (fun i => v i * u) (H u)))
      (fun i => circularModeNormalCoefficientCLM γ N
          (contourParameterShiftFamilyCLM γ (fun j => v j * t) H') i +
        I * (N + 2 : ℕ) * v i * circularModeNormalCoefficientCLM γ N
          (contourParameterShiftFamilyCLM γ (fun j => v j * t) (H t)) i -
        v i * circularModeTangentCoefficientCLM γ N
          (contourParameterShiftFamilyCLM γ (fun j => v j * t) (H t)) i) t := by
  apply hasDerivAt_pi.mpr
  intro i
  have hHi := (ContinuousLinearMap.proj i).hasFDerivAt.comp_hasDerivAt t hH
  have hv : HasDerivAt (fun u : ℝ => v i * u) (v i) t := by
    simpa only [mul_one] using (hasDerivAt_id t).const_mul (v i)
  have hp := hasDerivAt_littleContourFourierCoefficient_variableShift ((N + 3 : ℕ) : ℤ) hHi hv
  have hm := hasDerivAt_littleContourFourierCoefficient_variableShift (-((N + 1 : ℕ) : ℤ)) hHi hv
  have hmc := Complex.conjCLE.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt t hm
  have hd := (hp.add hmc).div_const (circularContourRadii i : ℂ)
  convert hd using 1
  · funext u
    change littleContourModeNormalCoefficientCLM γ (circularContourRadii i) N
      (contourParameterShiftLittleCLM γ (v i * u) (H u i)) = _
    rw [littleContourModeNormalCoefficientCLM_apply]
    rfl
  · change littleContourModeNormalCoefficientCLM γ (circularContourRadii i) N _ +
        I * (N + 2 : ℕ) * v i * littleContourModeNormalCoefficientCLM γ (circularContourRadii i) N _ -
          v i * littleContourModeTangentCoefficientCLM γ (circularContourRadii i) N _ = _
    simp only [littleContourModeNormalCoefficientCLM_apply, littleContourModeTangentCoefficientCLM_apply,
      ContinuousLinearMap.coe_coe, ContinuousLinearEquiv.coe_coe, Function.comp_def,
      ContinuousLinearMap.proj_apply, contourParameterShiftFamilyCLM_apply,
      Complex.conjCLE_apply, map_add, map_mul, conj_I, conj_ofReal, map_intCast]
    norm_num only [Int.cast_neg, Int.cast_natCast, Nat.cast_add, Nat.cast_ofNat]
    push_cast
    ring

end Euler2D

end
