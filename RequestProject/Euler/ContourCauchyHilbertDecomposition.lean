module

public import RequestProject.Euler.ContourCauchyRemainderHolder
public import RequestProject.Euler.ContourHilbertEstimates

/-! Exact decomposition of the actual Cauchy increment into its universal
Hilbert increment and the actual bounded remainder operator. -/

@[expose] public section

noncomputable section

open Set MeasureTheory
open scoped NNReal

namespace Euler2D

theorem contourCauchyResidualIncrement_eq_cauchy_add_hilbert {z dz f : ℝ → ℂ} {θ : ℝ}
    (hC : IntegrableOn (contourCauchyIncrementIntegrand z dz f θ) (Icc (-Real.pi) Real.pi))
    (hH : IntegrableOn (hilbertIncrementIntegrand f θ) (Icc (-Real.pi) Real.pi)) :
    contourCauchyResidualIncrement z dz f Real.pi θ =
      contourCauchyIncrement z dz f θ + hilbertIncrement f θ := by
  have heq : contourCauchyResidualIncrementIntegrand z dz f θ =
      fun τ => contourCauchyIncrementIntegrand z dz f θ τ + hilbertIncrementIntegrand f θ τ := by
    ext τ
    dsimp only [contourCauchyResidualIncrementIntegrand, contourCauchyPoleIntegrand,
      contourCauchyIncrementIntegrand, hilbertIncrementIntegrand]
    ring
  unfold contourCauchyResidualIncrement contourCauchyIncrement hilbertIncrement
  rw [heq, integral_add hC hH]

/-- Exact identity between the literal three integrals on the actual contour spaces. -/
theorem contourC1CauchyIncrement_eq_residual_sub_hilbert {γ : ℝ≥0}
    (Z : ContourC1Space γ) (f : ContourHolderSpace γ) {θ c : ℝ}
    (hγ : 0 < (γ : ℝ)) (hc : 0 < c)
    (hchord : ∀ τ ∈ Icc (-Real.pi) Real.pi,
      c * |τ| ≤ ‖ContourC1Space.lift γ Z θ - ContourC1Space.lift γ Z (θ + τ)‖) :
    contourC1CauchyIncrement Z f θ =
      contourC1CauchyResidualIncrement Z f θ - contourHilbertIncrement f θ := by
  have hC := integrableOn_contourC1CauchyIncrementIntegrand Z f hγ hc hchord
  have hH := integrableOn_hilbertIncrementIntegrand
    (((HolderFunctionSpace.toBCF γ f).continuous.comp
      (AddCircle.continuous_mk' (2 * Real.pi))).measurable)
    hγ (norm_nonneg f) Real.pi_pos.le (fun τ _ => norm_contourHolder_lift_sub_le f θ τ)
  have h := contourCauchyResidualIncrement_eq_cauchy_add_hilbert hC hH
  exact eq_sub_iff_add_eq.mpr h.symm

end Euler2D
