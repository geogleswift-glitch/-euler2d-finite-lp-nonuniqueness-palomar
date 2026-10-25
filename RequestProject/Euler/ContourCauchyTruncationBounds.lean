module

public import RequestProject.Euler.ContourCauchyPrincipalValue

/-! Uniform bounds for the genuine constant-density Cauchy truncations,
including cutoffs larger than the integration radius. -/

@[expose] public section

noncomputable section

open Set MeasureTheory Filter Topology
open scoped NNReal

namespace Euler2D

theorem norm_symmetricContourTruncation_le_remainder {g : ℝ → ℂ} {r δ : ℝ}
    (hδ : 0 < δ)
    (hR : IntegrableOn (fun τ => g τ + (τ : ℂ)⁻¹) (Icc (-r) r)) :
    ‖∫ τ in symmetricContourTruncation r δ, g τ‖ ≤
      ∫ τ in Icc (-r) r, ‖g τ + (τ : ℂ)⁻¹‖ := by
  rw [integral_symmetricContourTruncation_eq_remainder hδ hR]
  exact (norm_integral_le_integral_norm _).trans
    (setIntegral_mono_set hR.norm (ae_of_all _ fun τ => norm_nonneg _)
      (ae_of_all _ fun τ hτ => symmetricContourTruncation_subset r δ hτ))

theorem norm_contourCauchyTruncated_le {z dz : ℝ → ℂ} {γ H c r δ : ℝ}
    (hzc : Continuous z) (hdzc : Continuous dz) (hγ : 0 < γ) (hH : 0 ≤ H)
    (hc : 0 < c) (hr : 0 ≤ r) (hδ : 0 < δ) (hz : ∀ s, HasDerivAt z (dz s) s)
    (hd : ∀ s t, ‖dz s - dz t‖ ≤ H * |s - t| ^ γ)
    (hchord : ∀ θ τ : ℝ, |τ| ≤ r → c * |τ| ≤ ‖z θ - z (θ + τ)‖) (θ : ℝ) :
    ‖contourCauchyTruncated z dz θ r δ‖ ≤ (2 * H / c) * (2 * r ^ γ / γ) := by
  have hR := integrableOn_contourCauchyPoleIntegrand hzc hdzc hγ hH hc hr hz hd hchord θ
  exact (norm_symmetricContourTruncation_le_remainder hδ hR).trans
    (integral_norm_contourCauchyPoleIntegrand_le hzc hdzc hγ hH hc hr hz hd hchord θ)

theorem norm_contourC1CauchyTruncated_le {γ : ℝ≥0} (Z : ContourC1Space γ)
    {c r δ : ℝ} (hγ : 0 < (γ : ℝ)) (hc : 0 < c) (hr : 0 ≤ r) (hδ : 0 < δ)
    (hchord : ∀ θ τ : ℝ, |τ| ≤ r → c * |τ| ≤
      ‖ContourC1Space.lift γ Z θ - ContourC1Space.lift γ Z (θ + τ)‖) (θ : ℝ) :
    ‖contourCauchyTruncated (ContourC1Space.lift γ Z)
      (deriv (ContourC1Space.lift γ Z)) θ r δ‖ ≤
        (2 * ‖Z‖ / c) * (2 * r ^ (γ : ℝ) / (γ : ℝ)) :=
  norm_contourCauchyTruncated_le (ContourC1Space.contDiff_lift Z).continuous
    (ContourC1Space.contDiff_lift Z).continuous_deriv_one hγ (norm_nonneg Z) hc hr hδ
    (fun s => (ContourC1Space.hasDerivAt_lift Z s).differentiableAt.hasDerivAt)
    (norm_contourC1_deriv_lift_sub_le Z) hchord θ

end Euler2D

end
