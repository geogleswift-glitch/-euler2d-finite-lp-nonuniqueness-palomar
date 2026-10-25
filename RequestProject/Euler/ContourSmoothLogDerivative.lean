module

public import RequestProject.Euler.ContourLogLimitDerivative
public import RequestProject.Euler.ContourLogCauchyDerivative

/-! The original logarithmic self-interaction has the actual spatial
derivative for a genuine smooth periodic near-circle contour. All cutoff
limits, the phase density, and the derivative formula are constructed. -/

@[expose] public section

noncomputable section

open Complex Set Filter Topology MeasureTheory
open scoped NNReal ComplexConjugate ContDiff

namespace Euler2D

theorem hasDerivAt_contourSelfIntegral_smooth_near_circle {γ : ℝ≥0}
    (Z Z₀ : ContourC1Space γ) {c r : ℝ} (hγ : 0 < (γ : ℝ)) (hc : 0 < c)
    (hchord : ∀ θ τ : ℝ, |τ| ≤ Real.pi → c * |τ| ≤
      ‖ContourC1Space.lift γ Z θ - ContourC1Space.lift γ Z (θ + τ)‖)
    (hr : 0 < r) (href : ContourC1Space.lift γ Z₀ = refCircle r)
    (hsmall : ‖Z - Z₀‖ < 2 * r / Real.pi)
    (hs : ContDiff ℝ ∞ (ContourC1Space.lift γ Z)) (θ : ℝ) :
    HasDerivAt
      (contourSelfIntegral (ContourC1Space.lift γ Z) (deriv (ContourC1Space.lift γ Z)))
      ((1 / 2 : ℂ) * conj (deriv (ContourC1Space.lift γ Z) θ) *
        conj (contourC1CauchyIncrement Z (contourDerivativePhase Z hc hchord) θ)) θ := by
  have hds : ContDiff ℝ ∞ (deriv (ContourC1Space.lift γ Z)) :=
    (contDiff_infty_iff_deriv.mp hs).2
  have hdds : ContDiff ℝ ∞ (deriv (deriv (ContourC1Space.lift γ Z))) :=
    (contDiff_infty_iff_deriv.mp hds).2
  have hU := tendstoUniformly_contourC1LogCauchyTruncated_near_circle
    Z Z₀ hγ hc hchord hr href hsmall
  change TendstoUniformly
    (fun δ θ => ∫ τ in symmetricContourTruncation Real.pi δ,
      (deriv (ContourC1Space.lift γ Z) θ /
        (ContourC1Space.lift γ Z θ - ContourC1Space.lift γ Z (θ + τ))).re •
          deriv (ContourC1Space.lift γ Z) (θ + τ))
    (fun θ => (1 / 2 : ℂ) * conj (deriv (ContourC1Space.lift γ Z) θ) *
      conj (contourC1CauchyIncrement Z (contourDerivativePhase Z hc hchord) θ))
    (𝓝[>] (0 : ℝ)) at hU
  exact hasDerivAt_contourSelfIntegral_of_spatialCutoff_limit
    (ContourC1Space.contDiff_lift Z).continuous hds.continuous hdds.continuous
    hγ (norm_nonneg Z) hc
    (fun s => ContourC1Space.norm_eval_le Z (s : ContourCircle))
    (ContourC1Space.norm_deriv_lift_le Z)
    (fun s => (ContourC1Space.hasDerivAt_lift Z s).differentiableAt.hasDerivAt)
    (fun s => ((contDiff_infty_iff_deriv.mp hds).1 s).hasDerivAt)
    (norm_contourC1_deriv_lift_sub_le Z) hchord (ContourC1Space.periodic_lift Z)
    (periodic_deriv_contour (ContourC1Space.periodic_lift Z)
      ((ContourC1Space.contDiff_lift Z).differentiable one_ne_zero)) hU θ

end Euler2D

end
