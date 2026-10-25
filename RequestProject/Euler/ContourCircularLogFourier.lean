module

public import RequestProject.Euler.ContourCircularLogSeries

/-! Fourier coefficients of the actual real logarithmic kernel,
with the complex logarithm eliminated by conjugation. -/

@[expose] public section

noncomputable section

open Complex MeasureTheory
open scoped ComplexConjugate

namespace Euler2D

theorem continuous_contourCircular_log {q : ℂ} (hq : ‖q‖ < 1) :
    Continuous (fun θ : ℝ => log (1 - q * contourCircleCharacter 1 θ)) := by
  apply (continuous_const.sub (continuous_const.mul
    (continuous_contourCircleCharacter 1))).clog
  intro θ
  have hz : ‖-(q * contourCircleCharacter 1 θ)‖ < 1 := by
    simpa only [norm_neg, norm_mul, norm_contourCircleCharacter, mul_one] using hq
  simpa only [sub_eq_add_neg, Pi.add_apply, Pi.neg_apply, Pi.mul_apply] using
    mem_slitPlane_of_norm_lt_one hz

theorem integral_contourCircular_logNorm_positive {q : ℂ} (hq : ‖q‖ < 1)
    {m : ℕ} (hm : 0 < m) :
    (∫ θ in (0 : ℝ)..2 * Real.pi,
      (Real.log ‖1 - q * contourCircleCharacter 1 θ‖ : ℂ) *
        contourCircleCharacter (m : ℤ) θ) =
      -((conj q) ^ m / (m : ℂ)) * (Real.pi : ℂ) := by
  let A : ℝ → ℂ := fun θ => -log (1 - q * contourCircleCharacter 1 θ)
  have hc : Continuous A := (continuous_contourCircular_log hq).neg
  have hip := (hc.mul (continuous_contourCircleCharacter (m : ℤ))).intervalIntegrable
    (μ := volume) (a := (0 : ℝ)) (b := 2 * Real.pi)
  have hin := (hc.mul (continuous_contourCircleCharacter (-(m : ℤ)))).intervalIntegrable
    (μ := volume) (a := (0 : ℝ)) (b := 2 * Real.pi)
  have hic := (continuous_conj.comp (hc.mul
    (continuous_contourCircleCharacter (-(m : ℤ))))).intervalIntegrable
      (μ := volume) (a := (0 : ℝ)) (b := 2 * Real.pi)
  have he (θ : ℝ) : (Real.log ‖1 - q * contourCircleCharacter 1 θ‖ : ℂ) *
      contourCircleCharacter (m : ℤ) θ =
      -(A θ * contourCircleCharacter (m : ℤ) θ +
        conj (A θ * contourCircleCharacter (-(m : ℤ)) θ)) / 2 := by
    dsimp only [A]
    rw [← log_re, Complex.re_eq_add_conj]
    simp only [map_mul, map_neg, conj_contourCircleCharacter, neg_neg]
    ring
  have hconj := Complex.conjCLE.toContinuousLinearMap.intervalIntegral_comp_comm hin
  change (∫ θ in (0 : ℝ)..2 * Real.pi, conj (A θ * contourCircleCharacter (-(m : ℤ)) θ)) =
    conj (∫ θ in (0 : ℝ)..2 * Real.pi, A θ * contourCircleCharacter (-(m : ℤ)) θ) at hconj
  simp_rw [he]
  rw [intervalIntegral.integral_div, intervalIntegral.integral_neg,
    intervalIntegral.integral_add
      (f := fun θ => A θ * contourCircleCharacter (m : ℤ) θ)
      (g := fun θ => conj (A θ * contourCircleCharacter (-(m : ℤ)) θ)) hip hic, hconj,
    integral_contourCircular_negLog_positive hq hm,
    integral_contourCircular_negLog_negative hq m]
  simp only [map_mul, map_div₀, map_pow, map_natCast, Complex.conj_ofReal,
    map_ofNat, zero_add]
  ring

theorem integral_contourCircular_logNorm_real_positive {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1)
    {m : ℕ} (hm : 0 < m) :
    (∫ θ in (0 : ℝ)..2 * Real.pi,
      (Real.log ‖1 - (q : ℂ) * contourCircleCharacter 1 θ‖ : ℂ) *
        contourCircleCharacter (m : ℤ) θ) =
      -((q : ℂ) ^ m / (m : ℂ)) * (Real.pi : ℂ) := by
  simpa only [Complex.conj_ofReal] using integral_contourCircular_logNorm_positive
    (q := (q : ℂ)) (by simpa only [Complex.norm_of_nonneg hq0] using hq1) hm

end Euler2D

end
