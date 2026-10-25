module

public import RequestProject.Euler.ContourDerivativeLower
public import RequestProject.Euler.ContourHolderAlgebra

/-! The actual phase density conj(Z')/Z' is a genuine Hölder function.
Nonvanishing of Z' is deduced from the real short-chord bound. -/

@[expose] public section

noncomputable section

open Complex Set
open scoped NNReal ComplexConjugate

namespace Euler2D

theorem contourC1_derivative_norm_lower {γ : ℝ≥0} (Z : ContourC1Space γ) {c : ℝ}
    (hchord : ∀ θ τ : ℝ, |τ| ≤ Real.pi → c * |τ| ≤
      ‖ContourC1Space.lift γ Z θ - ContourC1Space.lift γ Z (θ + τ)‖) :
    ∀ x : ContourCircle, c ≤ ‖ContourC1Space.derivative γ Z x‖ := by
  intro x
  obtain ⟨θ, rfl⟩ := QuotientAddGroup.mk_surjective x
  simpa only [ContourC1Space.deriv_lift] using contourC1_norm_deriv_lift_lower Z hchord θ

def contourDerivativePhase {γ : ℝ≥0} (Z : ContourC1Space γ) {c : ℝ} (hc : 0 < c)
    (hchord : ∀ θ τ : ℝ, |τ| ≤ Real.pi → c * |τ| ≤
      ‖ContourC1Space.lift γ Z θ - ContourC1Space.lift γ Z (θ + τ)‖) : ContourHolderSpace γ :=
  HolderFunctionSpace.divideOfNormLower
    (HolderFunctionSpace.conjugate (ContourC1Space.derivative γ Z))
    (ContourC1Space.derivative γ Z) hc (contourC1_derivative_norm_lower Z hchord)

@[simp] theorem contourDerivativePhase_apply {γ : ℝ≥0} (Z : ContourC1Space γ) {c : ℝ} (hc : 0 < c)
    (hchord : ∀ θ τ : ℝ, |τ| ≤ Real.pi → c * |τ| ≤
      ‖ContourC1Space.lift γ Z θ - ContourC1Space.lift γ Z (θ + τ)‖) (θ : ℝ) :
    contourDerivativePhase Z hc hchord (θ : ContourCircle) =
      conj (deriv (ContourC1Space.lift γ Z) θ) / deriv (ContourC1Space.lift γ Z) θ := by
  simp only [contourDerivativePhase, HolderFunctionSpace.divideOfNormLower_apply,
    HolderFunctionSpace.conjugate_apply, ContourC1Space.deriv_lift]

theorem norm_contourDerivativePhase_value {γ : ℝ≥0} (Z : ContourC1Space γ) {c : ℝ} (hc : 0 < c)
    (hchord : ∀ θ τ : ℝ, |τ| ≤ Real.pi → c * |τ| ≤
      ‖ContourC1Space.lift γ Z θ - ContourC1Space.lift γ Z (θ + τ)‖) (θ : ℝ) :
    ‖contourDerivativePhase Z hc hchord (θ : ContourCircle)‖ = 1 := by
  rw [contourDerivativePhase_apply, norm_div, Complex.norm_conj]
  exact div_self (norm_ne_zero_iff.mpr (contourC1_deriv_lift_ne_zero Z hc hchord θ))

theorem norm_contourDerivativePhase_le {γ : ℝ≥0} (Z : ContourC1Space γ) {c : ℝ} (hc : 0 < c)
    (hchord : ∀ θ τ : ℝ, |τ| ≤ Real.pi → c * |τ| ≤
      ‖ContourC1Space.lift γ Z θ - ContourC1Space.lift γ Z (θ + τ)‖) :
    ‖contourDerivativePhase Z hc hchord‖ ≤
      2 * ‖ContourC1Space.derivative γ Z‖ *
        max c⁻¹ (‖ContourC1Space.derivative γ Z‖ / c ^ 2) := by
  have hh := HolderFunctionSpace.norm_divideOfNormLower_le
    (HolderFunctionSpace.conjugate (ContourC1Space.derivative γ Z))
    (ContourC1Space.derivative γ Z) hc (contourC1_derivative_norm_lower Z hchord)
  simpa only [contourDerivativePhase, HolderFunctionSpace.norm_conjugate] using hh

end Euler2D

end
