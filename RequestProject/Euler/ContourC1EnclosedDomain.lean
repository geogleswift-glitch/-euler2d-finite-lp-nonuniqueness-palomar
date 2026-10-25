module

public import RequestProject.Euler.ContourEnclosedArea

/-! The actual C¹ norm neighborhood supplies all inputs to the genuine
enclosed-domain construction. No radial-graph or area identity is assumed. -/

@[expose] public section

noncomputable section

open Complex Set MeasureTheory
open scoped NNReal

namespace Euler2D

section

variable {γ : ℝ≥0} (Z Z₀ : ContourC1Space γ) {r : ℝ}
  (hr : 0 < r) (href : ContourC1Space.lift γ Z₀ = refCircle r)
  (hsmall : ‖Z - Z₀‖ ≤ r / 4)

def contourC1EnclosedDomain : Set ℂ :=
  nearCircleEnclosedDomain hr (norm_nonneg _) hsmall
    (fun θ => (ContourC1Space.hasDerivAt_lift Z θ).differentiableAt.hasDerivAt)
    (contourC1_norm_sub_ref_le Z Z₀ href)
    (contourC1_norm_deriv_sub_ref_le Z Z₀ href)

include hr href hsmall

theorem isOpen_contourC1EnclosedDomain : IsOpen (contourC1EnclosedDomain Z Z₀ hr href hsmall) :=
  isOpen_nearCircleEnclosedDomain hr (norm_nonneg _) hsmall
    (fun θ => (ContourC1Space.hasDerivAt_lift Z θ).differentiableAt.hasDerivAt)
    (contourC1_norm_sub_ref_le Z Z₀ href) (contourC1_norm_deriv_sub_ref_le Z Z₀ href)
    (ContourC1Space.periodic_lift Z)

theorem frontier_contourC1EnclosedDomain :
    frontier (contourC1EnclosedDomain Z Z₀ hr href hsmall) = Set.range (ContourC1Space.lift γ Z) :=
  frontier_nearCircleEnclosedDomain hr (norm_nonneg _) hsmall
    (fun θ => (ContourC1Space.hasDerivAt_lift Z θ).differentiableAt.hasDerivAt)
    (contourC1_norm_sub_ref_le Z Z₀ href) (contourC1_norm_deriv_sub_ref_le Z Z₀ href)
    (ContourC1Space.periodic_lift Z)

theorem contourC1EnclosedDomain_subset_ball :
    contourC1EnclosedDomain Z Z₀ hr href hsmall ⊆ Metric.ball 0 (r + ‖Z - Z₀‖) :=
  nearCircleEnclosedDomain_subset_ball hr (norm_nonneg _) hsmall
    (fun θ => (ContourC1Space.hasDerivAt_lift Z θ).differentiableAt.hasDerivAt)
    (contourC1_norm_sub_ref_le Z Z₀ href) (contourC1_norm_deriv_sub_ref_le Z Z₀ href)

theorem ball_subset_contourC1EnclosedDomain :
    Metric.ball 0 (r - ‖Z - Z₀‖) ⊆ contourC1EnclosedDomain Z Z₀ hr href hsmall :=
  ball_subset_nearCircleEnclosedDomain hr (norm_nonneg _) hsmall
    (fun θ => (ContourC1Space.hasDerivAt_lift Z θ).differentiableAt.hasDerivAt)
    (contourC1_norm_sub_ref_le Z Z₀ href) (contourC1_norm_deriv_sub_ref_le Z Z₀ href)

theorem area_contourC1EnclosedDomain :
    volume.real (contourC1EnclosedDomain Z Z₀ hr href hsmall) =
      loopArea (ContourC1Space.lift γ Z) :=
  area_nearCircleEnclosedDomain hr (norm_nonneg _) hsmall
    (fun θ => (ContourC1Space.hasDerivAt_lift Z θ).differentiableAt.hasDerivAt)
    (contourC1_norm_sub_ref_le Z Z₀ href) (contourC1_norm_deriv_sub_ref_le Z Z₀ href)
    (contDiff_one_iff_deriv.mp (ContourC1Space.contDiff_lift Z)).2
    (ContourC1Space.periodic_lift Z)

end

end Euler2D
