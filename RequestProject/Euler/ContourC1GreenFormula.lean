module

public import RequestProject.Euler.ContourC1EnclosedDomain
public import RequestProject.Euler.ContourGreenFormula

/-! The genuine Green formula in the actual C¹ norm neighborhood. -/

@[expose] public section

noncomputable section

open Complex Set MeasureTheory intervalIntegral
open scoped NNReal

namespace Euler2D

theorem integral_gradient_contourC1EnclosedDomain {γ : ℝ≥0}
    (Z Z₀ : ContourC1Space γ) {r : ℝ} (hr : 0 < r)
    (href : ContourC1Space.lift γ Z₀ = refCircle r)
    (hsmall : ‖Z - Z₀‖ ≤ r / 4)
    {ψ : ℂ → ℝ} {dψ : ℂ → ℂ →L[ℝ] ℝ}
    (hψ : ∀ x, HasFDerivAt ψ (dψ x) x) (hdψ : Continuous dψ) :
    (∫ x in contourC1EnclosedDomain Z Z₀ hr href hsmall, complexRealGradient (dψ x)) =
      -I * ∫ θ in (0 : ℝ)..2 * Real.pi,
        (ψ (ContourC1Space.lift γ Z θ) : ℂ) * deriv (ContourC1Space.lift γ Z) θ := by
  exact integral_gradient_nearCircleEnclosedDomain hr (norm_nonneg _) hsmall
    (fun θ => (ContourC1Space.hasDerivAt_lift Z θ).differentiableAt.hasDerivAt)
    (contourC1_norm_sub_ref_le Z Z₀ href) (contourC1_norm_deriv_sub_ref_le Z Z₀ href)
    (contDiff_one_iff_deriv.mp (ContourC1Space.contDiff_lift Z)).2
    (ContourC1Space.periodic_lift Z) hψ hdψ

end Euler2D
