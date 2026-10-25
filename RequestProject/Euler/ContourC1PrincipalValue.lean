module

public import RequestProject.Euler.ContourNearCirclePrincipalValue
public import RequestProject.Euler.ContourCauchyWeightedPrincipalValue

/-! Actual near-circle Cauchy principal values in the genuine complete
C¹ Hölder space. No contour value or pole cancellation is assumed. -/

@[expose] public section

noncomputable section

open Set MeasureTheory Filter Topology Complex
open scoped NNReal

namespace Euler2D

theorem tendsto_contourC1CauchyTruncated_near_circle {γ : ℝ≥0}
    (Z Z₀ : ContourC1Space γ) {r : ℝ} (hr : 0 < r)
    (href : ContourC1Space.lift γ Z₀ = refCircle r)
    (hsmall : ‖Z - Z₀‖ < 2 * r / Real.pi) (θ : ℝ) :
    Tendsto (contourCauchyTruncated (ContourC1Space.lift γ Z)
      (deriv (ContourC1Space.lift γ Z)) θ Real.pi) (𝓝[>] (0 : ℝ))
      (𝓝 (-Complex.I * (Real.pi : ℂ))) := by
  have hp : ContDiff ℝ 1 (fun t : ℝ => ContourC1Space.lift γ Z t - refCircle r t) := by
    simpa only [ContourC1Space.lift_sub, Pi.sub_def, href] using
      (ContourC1Space.contDiff_lift (Z - Z₀))
  have hd : ∀ t : ℝ,
      ‖deriv (fun s : ℝ => ContourC1Space.lift γ Z s - refCircle r s) t‖ ≤ ‖Z - Z₀‖ := by
    intro t
    simpa only [ContourC1Space.lift_sub, Pi.sub_def, href] using
      (ContourC1Space.norm_deriv_lift_le (Z - Z₀) t)
  exact tendsto_nearCircleCauchyTruncated hr (norm_nonneg (Z - Z₀)) hsmall
    (ContourC1Space.contDiff_lift Z) hp hd (ContourC1Space.periodic_lift Z)

theorem integral_contourC1PoleIntegrand_near_circle {γ : ℝ≥0}
    (Z Z₀ : ContourC1Space γ) {r : ℝ} (hγ : 0 < (γ : ℝ)) (hr : 0 < r)
    (href : ContourC1Space.lift γ Z₀ = refCircle r)
    (hsmall : ‖Z - Z₀‖ < 2 * r / Real.pi) (θ : ℝ) :
    (∫ τ in Icc (-Real.pi) Real.pi,
      contourCauchyPoleIntegrand (ContourC1Space.lift γ Z)
        (deriv (ContourC1Space.lift γ Z)) θ τ) = -Complex.I * (Real.pi : ℂ) := by
  have hchord : ∀ θ τ : ℝ, |τ| ≤ Real.pi →
      (2 * r / Real.pi - ‖Z - Z₀‖) * |τ| ≤
        ‖ContourC1Space.lift γ Z θ - ContourC1Space.lift γ Z (θ + τ)‖ :=
    fun θ τ hτ => contourC1_chord_lower_of_norm_sub Z Z₀ hr.le href θ (abs_le.mp hτ)
  exact tendsto_nhds_unique
    (tendsto_contourC1CauchyTruncated Z hγ (sub_pos.mpr hsmall) Real.pi_pos.le hchord θ)
    (tendsto_contourC1CauchyTruncated_near_circle Z Z₀ hr href hsmall θ)

theorem tendsto_contourC1CauchyWeightedTruncated_near_circle {γ : ℝ≥0}
    (Z Z₀ : ContourC1Space γ) (f : ContourHolderSpace γ) {r : ℝ}
    (hγ : 0 < (γ : ℝ)) (hr : 0 < r)
    (href : ContourC1Space.lift γ Z₀ = refCircle r)
    (hsmall : ‖Z - Z₀‖ < 2 * r / Real.pi) (θ : ℝ) :
    Tendsto (contourCauchyWeightedTruncated (ContourC1Space.lift γ Z)
      (deriv (ContourC1Space.lift γ Z)) (fun t : ℝ => f (t : ContourCircle)) θ Real.pi)
      (𝓝[>] (0 : ℝ))
      (𝓝 ((-Complex.I * (Real.pi : ℂ)) * f (θ : ContourCircle) +
        contourC1CauchyIncrement Z f θ)) := by
  have hchord : ∀ θ τ : ℝ, |τ| ≤ Real.pi →
      (2 * r / Real.pi - ‖Z - Z₀‖) * |τ| ≤
        ‖ContourC1Space.lift γ Z θ - ContourC1Space.lift γ Z (θ + τ)‖ :=
    fun θ τ hτ => contourC1_chord_lower_of_norm_sub Z Z₀ hr.le href θ (abs_le.mp hτ)
  have h := tendsto_contourC1CauchyWeightedTruncated Z f hγ (sub_pos.mpr hsmall) hchord θ
  rwa [integral_contourC1PoleIntegrand_near_circle Z Z₀ hγ hr href hsmall θ] at h

end Euler2D

end
