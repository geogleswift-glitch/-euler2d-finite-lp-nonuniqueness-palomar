module

public import RequestProject.Euler.ContourLogBoundaryLimit
public import RequestProject.Euler.ContourCauchyIncrement

/-! Actual C¹ loop instances of logarithmic boundary regularization. -/

@[expose] public section

noncomputable section

open Complex Set Filter Topology
open scoped NNReal

namespace Euler2D

theorem tendsto_contourC1RegularizedLogBoundaryIntegral {γ : ℝ≥0}
    (Z : ContourC1Space γ) {c : ℝ} (hc : 0 < c)
    (hchord : ∀ θ τ : ℝ, |τ| ≤ Real.pi → c * |τ| ≤
      ‖ContourC1Space.lift γ Z θ - ContourC1Space.lift γ Z (θ + τ)‖) (x : ℂ) :
    Tendsto (fun δ : ℝ => contourRegularizedLogBoundaryIntegral
      (ContourC1Space.lift γ Z) (deriv (ContourC1Space.lift γ Z)) δ x) (𝓝 0)
      (𝓝 (contourLogBoundaryIntegral (ContourC1Space.lift γ Z)
        (deriv (ContourC1Space.lift γ Z)) x)) := by
  have hper : Function.Periodic (deriv (ContourC1Space.lift γ Z)) (2 * Real.pi) := by
    intro t
    rw [ContourC1Space.deriv_lift, ContourC1Space.deriv_lift, AddCircle.coe_add_period]
  exact tendsto_contourRegularizedLogBoundaryIntegral
    (ContourC1Space.contDiff_lift Z).continuous
    (contDiff_one_iff_deriv.mp (ContourC1Space.contDiff_lift Z)).2 hc
    (fun θ => ContourC1Space.norm_eval_le Z (θ : ContourCircle))
    (ContourC1Space.norm_deriv_lift_le Z) hchord
    (ContourC1Space.periodic_lift Z) hper x

theorem tendsto_contourC1RegularizedLogBoundaryIntegral_near_circle {γ : ℝ≥0}
    (Z Z₀ : ContourC1Space γ) {r : ℝ} (hr : 0 < r)
    (href : ContourC1Space.lift γ Z₀ = refCircle r)
    (hsmall : ‖Z - Z₀‖ < 2 * r / Real.pi) (x : ℂ) :
    Tendsto (fun δ : ℝ => contourRegularizedLogBoundaryIntegral
      (ContourC1Space.lift γ Z) (deriv (ContourC1Space.lift γ Z)) δ x) (𝓝 0)
      (𝓝 (contourLogBoundaryIntegral (ContourC1Space.lift γ Z)
        (deriv (ContourC1Space.lift γ Z)) x)) := by
  apply tendsto_contourC1RegularizedLogBoundaryIntegral Z (sub_pos.mpr hsmall)
  intro θ τ hτ
  exact contourC1_chord_lower_of_norm_sub Z Z₀ hr.le href θ (abs_le.mp hτ)

end Euler2D
