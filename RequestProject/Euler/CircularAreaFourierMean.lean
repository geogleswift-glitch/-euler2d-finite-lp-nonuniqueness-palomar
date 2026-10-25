module

public import RequestProject.Euler.ContourFourfoldFourierSupport
public import RequestProject.Euler.CircularLowProjectionCalculus
public import RequestProject.Euler.CircularNeutralMeanDerivative

/-! The genuine linear area functional removes precisely the radial
first contour coefficient. On the original fourfold area tangent space,
the remaining low projection is an actual neutral tangential mean. -/

@[expose] public section

set_option maxHeartbeats 1000000

noncomputable section

open Complex Set Filter Topology Metric MeasureTheory
open scoped NNReal ContDiff

namespace Euler2D

local instance (priority := 2000) areaMeanLittle_group (γ : ℝ≥0) :
    NormedAddCommGroup (LittleContourSpace γ) := Submodule.normedAddCommGroup (LittleContourSpace γ)
local instance (priority := 2000) areaMeanLittle_space (γ : ℝ≥0) :
    NormedSpace ℝ (LittleContourSpace γ) := Submodule.normedSpace (LittleContourSpace γ)

theorem littleContourEllCLM_eq_first_fourierCoefficient {γ : ℝ≥0}
    (r : ℝ) (H : LittleContourSpace γ) :
    littleContourEllCLM γ r H =
      (2 * Real.pi * r) * (littleContourFourierCoefficient γ 1 H).re := by
  have hc (θ : ℝ) : contourCircleCharacter (-1) θ = exp (-((θ : ℂ) * I)) := by
    simp [contourCircleCharacter]
  have hi := Complex.reCLM.intervalIntegral_comp_comm (intervalIntegrable_littleContour_fourier H (-1))
  change (∫ θ in (0 : ℝ)..2 * Real.pi,
    (LittleContourSpace.lift γ H θ * contourCircleCharacter (-1) θ).re) =
      (∫ θ in (0 : ℝ)..2 * Real.pi,
        LittleContourSpace.lift γ H θ * contourCircleCharacter (-1) θ).re at hi
  have he : (∫ θ in (0 : ℝ)..2 * Real.pi,
      LittleContourSpace.lift γ H θ * contourCircleCharacter (-1) θ).re =
        ∫ θ in (0 : ℝ)..2 * Real.pi, (exp (-((θ : ℂ) * I)) * LittleContourSpace.lift γ H θ).re := by
    rw [← hi]
    congr 1
    funext θ
    rw [hc, mul_comm]
  rw [littleContourEllCLM_eq_ellFun]
  unfold ellFun littleContourFourierCoefficient
  have hreal (z : ℂ) : ((((2 * Real.pi : ℝ) : ℂ))⁻¹ * z).re = (2 * Real.pi)⁻¹ * z.re := by
    simp only [← Complex.ofReal_inv, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero]
  rw [hreal, he]
  field_simp [Real.pi_ne_zero]
  congr 1
  apply intervalIntegral.integral_congr
  intro θ _
  dsimp only
  rw [mul_comm I (θ : ℂ)]

theorem littleContourFourierCoefficient_one_re_zero_of_ell {γ : ℝ≥0}
    {r : ℝ} (hr : r ≠ 0) {H : LittleContourSpace γ} (hH : littleContourEllCLM γ r H = 0) :
    (littleContourFourierCoefficient γ 1 H).re = 0 := by
  rw [littleContourEllCLM_eq_first_fourierCoefficient] at hH
  exact (mul_eq_zero.mp hH).resolve_left
    (mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero) hr)

theorem circularTangentialMeanLittle_eq_fourierMode {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1) (τ : Fin 2 → ℝ) (i : Fin 2) :
    circularTangentialMeanLittle hγ hγ1 τ i =
      littleContourFourierMode hγ hγ1.le 1 ((circularContourRadii i : ℂ) * I * (τ i : ℂ)) := by
  apply Subtype.ext
  apply ContourC1Space.ext
  intro x
  obtain ⟨θ, rfl⟩ := QuotientAddGroup.mk_surjective x
  change LittleContourSpace.lift γ
    (τ i • contourParameterShiftLittleCLM γ (Real.pi / 2) (littleCircularReference hγ hγ1 i)) θ = _
  rw [LittleContourSpace.lift_smul]
  simp only [Pi.smul_apply]
  rw [lift_contourParameterShiftLittleCLM]
  change (τ i : ℂ) * refCircle (circularContourRadii i) (θ + Real.pi / 2) =
    ((circularContourRadii i : ℂ) * I * (τ i : ℂ)) * contourCircleCharacter 1 θ
  have hp : exp (((Real.pi / 2 : ℝ) : ℂ) * I) = I := by
    push_cast
    exact Complex.exp_pi_div_two_mul_I
  simp only [refCircle, contourCircleCharacter, Int.cast_one, one_mul,
    Complex.ofReal_add, add_mul, Complex.exp_add, hp]
  ring

theorem circularLowFourierProjection_eq_tangentialMean {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1) (H : Fin 2 → LittleContourSpace γ)
    (hfour : ∀ i, H i ∈ fourfoldLittleContourSubmodule γ)
    (harea : ∀ i, littleContourEllCLM γ (circularContourRadii i) (H i) = 0) :
    circularLowFourierProjectionCLM hγ hγ1.le H =
      circularTangentialMeanLittle hγ hγ1
        (fun i => (littleContourFourierCoefficient γ 1 (H i)).im / circularContourRadii i) := by
  funext i
  have h0 : littleContourFourierCoefficient γ 0 (H i) = 0 :=
    littleContourFourierCoefficient_fourfold_eq_zero (hfour i) 0 (by norm_num)
  have h2 : littleContourFourierCoefficient γ 2 (H i) = 0 :=
    littleContourFourierCoefficient_fourfold_eq_zero (hfour i) 2 (by norm_num)
  have hz (k : ℤ) : littleContourFourierMode hγ hγ1.le k 0 = 0 := by
    rw [← littleContourFourierModeCLM_apply]
    exact (littleContourFourierModeCLM hγ hγ1.le k).map_zero
  rw [circularLowFourierProjectionCLM_apply, h0, h2, hz, zero_add, hz, add_zero,
    circularTangentialMeanLittle_eq_fourierMode]
  apply congrArg (littleContourFourierMode hγ hγ1.le 1)
  let c := littleContourFourierCoefficient γ 1 (H i)
  have hr : (circularContourRadii i : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (circularContourRadii_bounds i).1.ne'
  have hc : c.re = 0 := littleContourFourierCoefficient_one_re_zero_of_ell
    (circularContourRadii_bounds i).1.ne' (harea i)
  have he := Complex.re_add_im c
  rw [hc, Complex.ofReal_zero, zero_add] at he
  calc
    _ = (c.im : ℂ) * I := he.symm
    _ = _ := by
      push_cast
      field_simp [hr]
      ring

theorem circularPeriod_derivative_low_fourfold_area {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1) {ρ : ℝ} (hρ : 0 < ρ)
    {X : (Fin 2 → LittleContourSpace γ) → ℝ → Fin 2 → LittleContourSpace γ}
    (hX : IsBanachFlowOn (circularBanachField hγ hγ1) (circularBanachDomain hγ hγ1)
      (ball (littleCircularReference hγ hγ1) ρ) period X)
    (hd : DifferentiableAt ℝ (fun W => X W period) (littleCircularReference hγ hγ1))
    (H : Fin 2 → LittleContourSpace γ)
    (hfour : ∀ i, H i ∈ fourfoldLittleContourSubmodule γ)
    (harea : ∀ i, littleContourEllCLM γ (circularContourRadii i) (H i) = 0) :
    fderiv ℝ (fun W => X W period) (littleCircularReference hγ hγ1)
      (circularLowFourierProjectionCLM hγ hγ1.le H) = circularLowFourierProjectionCLM hγ hγ1.le H := by
  rw [circularLowFourierProjection_eq_tangentialMean hγ hγ1 H hfour harea]
  exact circularPeriod_derivative_tangentialMean hγ hγ1 hρ hX hd _

end Euler2D

end
