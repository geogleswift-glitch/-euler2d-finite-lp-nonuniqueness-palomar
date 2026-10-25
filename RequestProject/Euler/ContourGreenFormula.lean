module

public import RequestProject.Euler.ContourFanChart
public import RequestProject.Euler.ContourFanIntegral

/-! Genuine Green's formula on the actual near-circle enclosed domain.
The domain is constructed from the original loop, the spatial integral
is changed by an actual injective Jacobian chart, and the parameter
integral is evaluated by actual one-dimensional FTC and Fubini. -/

@[expose] public section

noncomputable section

open Complex Set Filter Topology MeasureTheory intervalIntegral
open scoped ComplexConjugate

namespace Euler2D

theorem integral_contourFanParameterDomain_eq_rectangle {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (f : ℂ → E) :
    (∫ p in contourFanParameterDomain, f p) =
      ∫ p in Icc (0 : ℝ) (2 * Real.pi) ×ˢ Icc (0 : ℝ) 1, f ⟨p.2, p.1⟩ := by
  let e := Complex.measurableEquivRealProd
  have hm := Complex.volume_preserving_equiv_real_prod.symm
  have h := hm.setIntegral_preimage_emb e.symm.measurableEmbedding f contourFanParameterDomain
  have hpre : e.symm ⁻¹' contourFanParameterDomain =
      Ioo (0 : ℝ) 1 ×ˢ Ico (0 : ℝ) (2 * Real.pi) := rfl
  rw [hpre] at h
  rw [← h]
  rw [Measure.volume_eq_prod]
  rw [setIntegral_congr_set (Measure.set_prod_ae_eq Ioo_ae_eq_Icc Ico_ae_eq_Icc)]
  exact (setIntegral_prod_swap (Icc (0 : ℝ) 1) (Icc (0 : ℝ) (2 * Real.pi))
    (fun p : ℝ × ℝ => f (e.symm p))).symm

theorem integrableOn_continuous_nearCircleEnclosedDomain {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {z dz : ℝ → ℂ} {r ε : ℝ}
    (hr : 0 < r) (hε : 0 ≤ ε) (hsmall : ε ≤ r / 4)
    (hz : ∀ θ, HasDerivAt z (dz θ) θ)
    (hv : ∀ θ, ‖z θ - refCircle r θ‖ ≤ ε)
    (hd : ∀ θ, ‖dz θ - deriv (refCircle r) θ‖ ≤ ε)
    {f : ℂ → E} (hf : Continuous f) :
    IntegrableOn f (nearCircleEnclosedDomain hr hε hsmall hz hv hd) :=
  (hf.continuousOn.integrableOn_compact (isCompact_closedBall (0 : ℂ) (r + ε))).mono_set
    ((nearCircleEnclosedDomain_subset_ball hr hε hsmall hz hv hd).trans Metric.ball_subset_closedBall)

/-- Green's formula in complex gradient notation, on the actual domain. -/
theorem integral_gradient_nearCircleEnclosedDomain {ψ : ℂ → ℝ} {dψ : ℂ → ℂ →L[ℝ] ℝ}
    {z dz : ℝ → ℂ} {r ε : ℝ}
    (hr : 0 < r) (hε : 0 ≤ ε) (hsmall : ε ≤ r / 4)
    (hz : ∀ θ, HasDerivAt z (dz θ) θ)
    (hv : ∀ θ, ‖z θ - refCircle r θ‖ ≤ ε)
    (hd : ∀ θ, ‖dz θ - deriv (refCircle r) θ‖ ≤ ε)
    (hdz : Continuous dz) (hp : Function.Periodic z (2 * Real.pi))
    (hψ : ∀ x, HasFDerivAt ψ (dψ x) x) (hdψ : Continuous dψ) :
    (∫ x in nearCircleEnclosedDomain hr hε hsmall hz hv hd, complexRealGradient (dψ x)) =
      -I * ∫ θ in (0 : ℝ)..2 * Real.pi, (ψ (z θ) : ℂ) * dz θ := by
  rw [integral_nearCircleEnclosedDomain_eq_fan hr hε hsmall hz hv hd hp,
    integral_contourFanParameterDomain_eq_rectangle]
  exact integral_contourFan_gradient hψ hdψ hz hdz hp

end Euler2D
