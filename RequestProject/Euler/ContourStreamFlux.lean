module

public import RequestProject.Euler.ContourAreaVariation
public import RequestProject.Euler.ContourFanGreen

/-! Zero normal flux of an actual rotated real gradient is the genuine
one-dimensional fundamental theorem of calculus along the closed loop.
This is the scalar stream-function step used for area preservation. -/

@[expose] public section

noncomputable section

open Complex Set Filter Topology MeasureTheory intervalIntegral
open scoped ComplexConjugate NNReal

namespace Euler2D

theorem im_conj_I_gradient_mul (l : ℂ →L[ℝ] ℝ) (a : ℂ) :
    (conj (I * complexRealGradient l) * a).im = -l a := by
  rw [realLinearMap_complex_decomposition l a]
  simp only [complexRealGradient, Complex.mul_im, Complex.mul_re, Complex.conj_re,
    Complex.conj_im, Complex.add_re, Complex.add_im, Complex.I_re, Complex.I_im,
    Complex.ofReal_re, Complex.ofReal_im]
  ring

theorem integral_normalFlux_stream_zero {ψ : ℂ → ℝ} {dψ : ℂ → ℂ →L[ℝ] ℝ}
    {z dz : ℝ → ℂ}
    (hψ : ∀ x, HasFDerivAt ψ (dψ x) x) (hdψ : Continuous dψ)
    (hz : ∀ θ, HasDerivAt z (dz θ) θ) (hdzc : Continuous dz)
    (hp : Function.Periodic z (2 * Real.pi)) :
    (∫ θ in (0 : ℝ)..2 * Real.pi,
      (conj (I * complexRealGradient (dψ (z θ))) * dz θ).im) = 0 := by
  have hzc : Continuous z := continuous_iff_continuousAt.mpr (fun θ => (hz θ).continuousAt)
  have hder (θ : ℝ) : HasDerivAt (fun s => ψ (z s)) (dψ (z θ) (dz θ)) θ :=
    (hψ (z θ)).comp_hasDerivAt θ (hz θ)
  have hdc : Continuous (fun θ => dψ (z θ) (dz θ)) := (hdψ.comp hzc).clm_apply hdzc
  have hP : z (2 * Real.pi) = z 0 := by simpa only [zero_add] using hp 0
  have hi : (∫ θ in (0 : ℝ)..2 * Real.pi, dψ (z θ) (dz θ)) = 0 := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun θ _ => hder θ)
      (hdc.intervalIntegrable _ _), hP, sub_self]
  simp_rw [im_conj_I_gradient_mul]
  rw [intervalIntegral.integral_neg, hi, neg_zero]

theorem hasDerivAt_contourArea_zero_of_stream_velocity {γ : ℝ≥0}
    {Z : ℝ → ContourC1Space γ} {V : ContourC1Space γ} {t : ℝ}
    {ψ : ℂ → ℝ} {dψ : ℂ → ℂ →L[ℝ] ℝ}
    (hZ : HasDerivAt Z V t) (hψ : ∀ x, HasFDerivAt ψ (dψ x) x) (hdψ : Continuous dψ)
    (hV : ∀ θ, ContourC1Space.lift γ V θ =
      I * complexRealGradient (dψ (ContourC1Space.lift γ (Z t) θ))) :
    HasDerivAt (fun s => contourArea γ (Z s)) 0 t := by
  have hd := hasDerivAt_contourArea_along_curve hZ
  simp_rw [hV] at hd
  have hflux := integral_normalFlux_stream_zero hψ hdψ
    (fun θ => (ContourC1Space.hasDerivAt_lift (Z t) θ).differentiableAt.hasDerivAt)
    (contDiff_one_iff_deriv.mp (ContourC1Space.contDiff_lift (Z t))).2
    (ContourC1Space.periodic_lift (Z t))
  rw [hflux] at hd
  exact hd

end Euler2D
