module

public import RequestProject.Euler.ContourCircularCauchyModes
public import RequestProject.Euler.ContourCircularSignedLogModes

/-! The actual separated circular first variation on a pure integer
Fourier mode, reduced to the proved Cauchy and logarithmic integrals. -/

@[expose] public section

noncomputable section

open Complex Set MeasureTheory
open scoped ComplexConjugate

namespace Euler2D

def circularLogMode (r s : ℝ) (k : ℤ) : ℂ :=
  ∫ θ in (-Real.pi : ℝ)..Real.pi,
    (Real.log ‖(r : ℂ) - (s : ℂ) * contourCircleCharacter 1 θ‖ : ℂ) * contourCircleCharacter k θ

def circularContourModeVariation (r s : ℝ) (n : ℤ) (a b : ℂ) : ℂ :=
  ∫ θ in (-Real.pi : ℝ)..Real.pi,
    ((a - b * contourCircleCharacter n θ) /
      ((r : ℂ) - (s : ℂ) * contourCircleCharacter 1 θ)).re •
        (I * (s : ℂ) * contourCircleCharacter 1 θ) +
    Real.log ‖(r : ℂ) - (s : ℂ) * contourCircleCharacter 1 θ‖ •
      (I * (n : ℂ) * b * contourCircleCharacter n θ)

theorem circularSeparatedDenominator_ne_zero {r s : ℝ}
    (hr : 0 < r) (hs : 0 < s) (hrs : r ≠ s) (θ : ℝ) :
    (r : ℂ) - (s : ℂ) * contourCircleCharacter 1 θ ≠ 0 := by
  intro h
  have he := congrArg norm (sub_eq_zero.mp h)
  simp only [Complex.norm_of_nonneg hr.le, norm_mul, Complex.norm_of_nonneg hs.le,
    norm_contourCircleCharacter, mul_one] at he
  exact hrs he

theorem continuous_circularCauchyMode_integrand {r s : ℝ}
    (hr : 0 < r) (hs : 0 < s) (hrs : r ≠ s) (k : ℤ) :
    Continuous (fun θ : ℝ =>
      ((r : ℂ) - (s : ℂ) * contourCircleCharacter 1 θ)⁻¹ * contourCircleCharacter k θ) :=
  ((continuous_const.sub (continuous_const.mul (continuous_contourCircleCharacter 1))).inv₀
    (circularSeparatedDenominator_ne_zero hr hs hrs)).mul (continuous_contourCircleCharacter k)

theorem circularContourModeVariation_rational_identity (r s : ℝ) (n : ℤ) (a b : ℂ) (θ : ℝ) :
    ((a - b * contourCircleCharacter n θ) /
      ((r : ℂ) - (s : ℂ) * contourCircleCharacter 1 θ)).re •
        (I * (s : ℂ) * contourCircleCharacter 1 θ) =
      I * (s : ℂ) / 2 *
        (a * (((r : ℂ) - (s : ℂ) * contourCircleCharacter 1 θ)⁻¹ * contourCircleCharacter 1 θ) -
          b * (((r : ℂ) - (s : ℂ) * contourCircleCharacter 1 θ)⁻¹ * contourCircleCharacter (n + 1) θ) +
          conj a * conj (((r : ℂ) - (s : ℂ) * contourCircleCharacter 1 θ)⁻¹ * contourCircleCharacter (-1) θ) -
          conj b * conj (((r : ℂ) - (s : ℂ) * contourCircleCharacter 1 θ)⁻¹ * contourCircleCharacter (n - 1) θ)) := by
  rw [Complex.real_smul, Complex.re_eq_add_conj]
  rw [← contourCircleCharacter_mul n 1 θ, show n - 1 = n + (-1) by ring,
    ← contourCircleCharacter_mul n (-1) θ]
  simp only [map_mul, map_sub, map_inv₀, map_div₀, Complex.conj_ofReal,
    conj_contourCircleCharacter, neg_neg, div_eq_mul_inv]
  ring

set_option maxHeartbeats 600000 in
theorem circularContourModeVariation_formula {r s : ℝ}
    (hr : 0 < r) (hs : 0 < s) (hrs : r ≠ s) (n : ℤ) (a b : ℂ) :
    circularContourModeVariation r s n a b =
      I * (s : ℂ) / 2 *
        (a * circularCauchyMode r s 1 - b * circularCauchyMode r s (n + 1) +
          conj a * conj (circularCauchyMode r s (-1)) - conj b * conj (circularCauchyMode r s (n - 1))) +
      (I * (n : ℂ) * b) * circularLogMode r s n := by
  let A : ℤ → ℝ → ℂ := fun k θ =>
    ((r : ℂ) - (s : ℂ) * contourCircleCharacter 1 θ)⁻¹ * contourCircleCharacter k θ
  have hAc (k : ℤ) : Continuous (A k) := continuous_circularCauchyMode_integrand hr hs hrs k
  have hAi (k : ℤ) : IntervalIntegrable (A k) volume (-Real.pi) Real.pi :=
    (hAc k).intervalIntegrable _ _
  have hconj (k : ℤ) : (∫ θ in (-Real.pi : ℝ)..Real.pi, conj (A k θ)) =
      conj (circularCauchyMode r s k) := by
    exact Complex.conjCLE.toContinuousLinearMap.intervalIntegral_comp_comm (hAi k)
  have hi1 := (hAi 1).const_mul a
  have hi2 := (hAi (n + 1)).const_mul b
  have hi3 := ((continuous_conj.comp (hAc (-1))).intervalIntegrable
    (μ := volume) (-Real.pi) Real.pi).const_mul (conj a)
  have hi4 := ((continuous_conj.comp (hAc (n - 1))).intervalIntegrable
    (μ := volume) (-Real.pi) Real.pi).const_mul (conj b)
  change IntervalIntegrable (fun θ => conj a * conj (A (-1) θ)) volume (-Real.pi) Real.pi at hi3
  change IntervalIntegrable (fun θ => conj b * conj (A (n - 1) θ)) volume (-Real.pi) Real.pi at hi4
  have hrat : (∫ θ in (-Real.pi : ℝ)..Real.pi,
      ((a - b * contourCircleCharacter n θ) /
        ((r : ℂ) - (s : ℂ) * contourCircleCharacter 1 θ)).re •
          (I * (s : ℂ) * contourCircleCharacter 1 θ)) =
      I * (s : ℂ) / 2 *
        (a * circularCauchyMode r s 1 - b * circularCauchyMode r s (n + 1) +
          conj a * conj (circularCauchyMode r s (-1)) - conj b * conj (circularCauchyMode r s (n - 1))) := by
    simp_rw [circularContourModeVariation_rational_identity]
    rw [intervalIntegral.integral_const_mul]
    change I * (s : ℂ) / 2 * (∫ θ in (-Real.pi : ℝ)..Real.pi,
      a * A 1 θ - b * A (n + 1) θ + conj a * conj (A (-1) θ) - conj b * conj (A (n - 1) θ)) = _
    rw [intervalIntegral.integral_sub ((hi1.sub hi2).add hi3) hi4,
      intervalIntegral.integral_add (hi1.sub hi2) hi3,
      intervalIntegral.integral_sub hi1 hi2]
    simp only [intervalIntegral.integral_const_mul, hconj]
    rfl
  have hri : IntervalIntegrable (fun θ : ℝ =>
      ((a - b * contourCircleCharacter n θ) /
        ((r : ℂ) - (s : ℂ) * contourCircleCharacter 1 θ)).re •
          (I * (s : ℂ) * contourCircleCharacter 1 θ)) volume (-Real.pi) Real.pi := by
    apply Continuous.intervalIntegrable
    exact (Complex.continuous_re.comp
      ((continuous_const.sub (continuous_const.mul (continuous_contourCircleCharacter n))).div
        (continuous_const.sub (continuous_const.mul (continuous_contourCircleCharacter 1)))
        (circularSeparatedDenominator_ne_zero hr hs hrs))).smul
      (continuous_const.mul (continuous_contourCircleCharacter 1))
  have hlf : (fun θ : ℝ => Real.log ‖(r : ℂ) - (s : ℂ) * contourCircleCharacter 1 θ‖ •
      (I * (n : ℂ) * b * contourCircleCharacter n θ)) =
      (fun θ : ℝ => (I * (n : ℂ) * b) *
        ((Real.log ‖(r : ℂ) - (s : ℂ) * contourCircleCharacter 1 θ‖ : ℂ) * contourCircleCharacter n θ)) := by
    funext θ
    rw [Complex.real_smul]
    ring
  have hli : IntervalIntegrable (fun θ : ℝ =>
      Real.log ‖(r : ℂ) - (s : ℂ) * contourCircleCharacter 1 θ‖ •
        (I * (n : ℂ) * b * contourCircleCharacter n θ)) volume (-Real.pi) Real.pi := by
    rw [hlf]
    exact (intervalIntegrable_contourCircular_two_radii_logMode hr hs n).const_mul _
  unfold circularContourModeVariation
  rw [intervalIntegral.integral_add hri hli, hrat, hlf, intervalIntegral.integral_const_mul]
  rfl

end Euler2D

end
