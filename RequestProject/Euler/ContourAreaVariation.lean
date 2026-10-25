module

public import RequestProject.Euler.ContourAreaAnalytic

/-! The actual first variation of the original loop area. Periodic
integration by parts is proved from the true derivatives before the
Banach derivative is identified with the physical normal flux. -/

@[expose] public section

noncomputable section

open Complex Set Filter Topology MeasureTheory intervalIntegral
open scoped ComplexConjugate NNReal

namespace Euler2D

theorem integral_im_conj_mul_derivative_swap {z v dz dv : ℝ → ℂ}
    (hzc : Continuous z) (hvc : Continuous v) (hdzc : Continuous dz) (hdvc : Continuous dv)
    (hz : ∀ θ, HasDerivAt z (dz θ) θ) (hv : ∀ θ, HasDerivAt v (dv θ) θ)
    (hzp : Function.Periodic z (2 * Real.pi)) (hvp : Function.Periodic v (2 * Real.pi)) :
    (∫ θ in (0 : ℝ)..2 * Real.pi, (conj (z θ) * dv θ).im) =
      ∫ θ in (0 : ℝ)..2 * Real.pi, (conj (v θ) * dz θ).im := by
  let A : ℝ → ℝ := fun θ => (conj (z θ) * dv θ).im
  let B : ℝ → ℝ := fun θ => (conj (v θ) * dz θ).im
  have hAc : Continuous A := by dsimp only [A]; fun_prop
  have hBc : Continuous B := by dsimp only [B]; fun_prop
  have hder (θ : ℝ) : HasDerivAt (fun s => (conj (z s) * v s).im) (A θ - B θ) θ := by
    have hc := Complex.conjCLE.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt θ (hz θ)
    have hc' : HasDerivAt (fun s => conj (z s)) (conj (dz θ)) θ := hc
    have hp := hc'.mul (hv θ)
    have hi := Complex.imCLM.hasFDerivAt.comp_hasDerivAt θ hp
    convert hi using 1 <;>
      (try funext s) <;>
      simp only [A, B, Function.comp_def, Pi.mul_apply, Complex.imCLM_apply,
        Complex.add_im, Complex.mul_im, Complex.conj_re, Complex.conj_im] <;> ring
  have hPz : z (2 * Real.pi) = z 0 := by simpa only [zero_add] using hzp 0
  have hPv : v (2 * Real.pi) = v 0 := by simpa only [zero_add] using hvp 0
  have hi : (∫ θ in (0 : ℝ)..2 * Real.pi, A θ - B θ) = 0 := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun θ _ => hder θ)
      ((hAc.sub hBc).intervalIntegrable _ _), hPz, hPv, sub_self]
  rw [intervalIntegral.integral_sub (hAc.intervalIntegrable _ _) (hBc.intervalIntegrable _ _)] at hi
  exact sub_eq_zero.mp hi

theorem contourAreaForm_symmetric {γ : ℝ≥0} (Z V : ContourC1Space γ) :
    contourAreaForm γ Z V = contourAreaForm γ V Z := by
  rw [contourAreaForm_apply, contourAreaForm_apply]
  congr 1
  simp_rw [← ContourC1Space.deriv_lift]
  apply integral_im_conj_mul_derivative_swap
    (ContourC1Space.contDiff_lift Z).continuous (ContourC1Space.contDiff_lift V).continuous
    (contDiff_one_iff_deriv.mp (ContourC1Space.contDiff_lift Z)).2
    (contDiff_one_iff_deriv.mp (ContourC1Space.contDiff_lift V)).2
    (fun θ => (ContourC1Space.hasDerivAt_lift Z θ).differentiableAt.hasDerivAt)
    (fun θ => (ContourC1Space.hasDerivAt_lift V θ).differentiableAt.hasDerivAt)
    (ContourC1Space.periodic_lift Z) (ContourC1Space.periodic_lift V)

def contourAreaDerivative {γ : ℝ≥0} (Z : ContourC1Space γ) : ContourC1Space γ →L[ℝ] ℝ :=
  contourAreaForm γ Z + (contourAreaForm γ).flip Z

theorem hasFDerivAt_contourArea {γ : ℝ≥0} (Z : ContourC1Space γ) :
    HasFDerivAt (contourArea γ) (contourAreaDerivative Z) Z := by
  rw [contourArea_eq_diagonal]
  have hd := (contourAreaForm γ).hasFDerivAt_of_bilinear
    (hasFDerivAt_id Z) (hasFDerivAt_id Z)
  convert hd using 1 <;> ext V <;> simp [contourAreaDerivative, id_eq]

theorem contourAreaDerivative_apply {γ : ℝ≥0} (Z V : ContourC1Space γ) :
    contourAreaDerivative Z V =
      ∫ θ in (0 : ℝ)..2 * Real.pi,
        (conj (ContourC1Space.lift γ V θ) * deriv (ContourC1Space.lift γ Z) θ).im := by
  change contourAreaForm γ Z V + contourAreaForm γ V Z = _
  rw [contourAreaForm_symmetric Z V, contourAreaForm_apply]
  simp_rw [← ContourC1Space.deriv_lift]
  ring

theorem hasDerivAt_contourArea_along_curve {γ : ℝ≥0} {Z : ℝ → ContourC1Space γ}
    {V : ContourC1Space γ} {t : ℝ} (hZ : HasDerivAt Z V t) :
    HasDerivAt (fun s => contourArea γ (Z s))
      (∫ θ in (0 : ℝ)..2 * Real.pi,
        (conj (ContourC1Space.lift γ V θ) * deriv (ContourC1Space.lift γ (Z t)) θ).im) t := by
  have hd := (hasFDerivAt_contourArea (Z t)).comp_hasDerivAt t hZ
  simpa only [Function.comp_def, contourAreaDerivative_apply] using hd

end Euler2D
