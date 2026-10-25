module

public import RequestProject.Euler.ContourSmoothLogDerivative
public import RequestProject.Euler.ContourCauchyOperator

/-! The actual logarithmic spatial derivative is a genuine Hölder
function, built from the proved Cauchy operator and actual phase density. -/

@[expose] public section

noncomputable section

open Complex Set Filter Topology MeasureTheory
open scoped NNReal ComplexConjugate ContDiff

namespace Euler2D

def contourLogDerivativeHolder {γ : ℝ≥0} (Z : ContourC1Space γ) {c : ℝ}
    (hγ : 0 < (γ : ℝ)) (hγ1 : (γ : ℝ) < 1) (hc : 0 < c)
    (hchord : ∀ θ τ : ℝ, |τ| ≤ Real.pi → c * |τ| ≤
      ‖ContourC1Space.lift γ Z θ - ContourC1Space.lift γ Z (θ + τ)‖) : ContourHolderSpace γ :=
  (1 / 2 : ℝ) • HolderFunctionSpace.pointwiseMul
    (HolderFunctionSpace.conjugate (ContourC1Space.derivative γ Z))
    (HolderFunctionSpace.conjugate
      (contourCauchyIncrementOperator Z hγ hγ1 hc hchord (contourDerivativePhase Z hc hchord)))

@[simp] theorem contourLogDerivativeHolder_apply {γ : ℝ≥0} (Z : ContourC1Space γ) {c : ℝ}
    (hγ : 0 < (γ : ℝ)) (hγ1 : (γ : ℝ) < 1) (hc : 0 < c)
    (hchord : ∀ θ τ : ℝ, |τ| ≤ Real.pi → c * |τ| ≤
      ‖ContourC1Space.lift γ Z θ - ContourC1Space.lift γ Z (θ + τ)‖) (θ : ℝ) :
    contourLogDerivativeHolder Z hγ hγ1 hc hchord (θ : ContourCircle) =
      (1 / 2 : ℂ) * conj (deriv (ContourC1Space.lift γ Z) θ) *
        conj (contourC1CauchyIncrement Z (contourDerivativePhase Z hc hchord) θ) := by
  change (1 / 2 : ℝ) •
    (conj (ContourC1Space.derivative γ Z (θ : ContourCircle)) *
      conj (contourCauchyIncrementOperator Z hγ hγ1 hc hchord
        (contourDerivativePhase Z hc hchord) (θ : ContourCircle))) = _
  rw [contourCauchyIncrementOperator_apply, ← ContourC1Space.deriv_lift, Complex.real_smul]
  push_cast
  ring

theorem norm_contourLogDerivativeHolder_le {γ : ℝ≥0} (Z : ContourC1Space γ) {c : ℝ}
    (hγ : 0 < (γ : ℝ)) (hγ1 : (γ : ℝ) < 1) (hc : 0 < c)
    (hchord : ∀ θ τ : ℝ, |τ| ≤ Real.pi → c * |τ| ≤
      ‖ContourC1Space.lift γ Z θ - ContourC1Space.lift γ Z (θ + τ)‖) :
    ‖contourLogDerivativeHolder Z hγ hγ1 hc hchord‖ ≤
      ‖ContourC1Space.derivative γ Z‖ *
        ‖contourCauchyIncrementOperator Z hγ hγ1 hc hchord‖ *
          ‖contourDerivativePhase Z hc hchord‖ := by
  unfold contourLogDerivativeHolder
  rw [norm_smul]
  norm_num only [Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
  have hm := HolderFunctionSpace.norm_pointwiseMul_le
    (HolderFunctionSpace.conjugate (ContourC1Space.derivative γ Z))
    (HolderFunctionSpace.conjugate
      (contourCauchyIncrementOperator Z hγ hγ1 hc hchord (contourDerivativePhase Z hc hchord)))
  rw [HolderFunctionSpace.norm_conjugate, HolderFunctionSpace.norm_conjugate] at hm
  have hop := (contourCauchyIncrementOperator Z hγ hγ1 hc hchord).le_opNorm
    (contourDerivativePhase Z hc hchord)
  have hp := mul_le_mul_of_nonneg_left hop (norm_nonneg (ContourC1Space.derivative γ Z))
  nlinarith

theorem hasDerivAt_contourSelfIntegral_smooth_near_circle_holder {γ : ℝ≥0}
    (Z Z₀ : ContourC1Space γ) {c r : ℝ} (hγ : 0 < (γ : ℝ)) (hγ1 : (γ : ℝ) < 1)
    (hc : 0 < c)
    (hchord : ∀ θ τ : ℝ, |τ| ≤ Real.pi → c * |τ| ≤
      ‖ContourC1Space.lift γ Z θ - ContourC1Space.lift γ Z (θ + τ)‖)
    (hr : 0 < r) (href : ContourC1Space.lift γ Z₀ = refCircle r)
    (hsmall : ‖Z - Z₀‖ < 2 * r / Real.pi)
    (hs : ContDiff ℝ ∞ (ContourC1Space.lift γ Z)) (θ : ℝ) :
    HasDerivAt
      (contourSelfIntegral (ContourC1Space.lift γ Z) (deriv (ContourC1Space.lift γ Z)))
      (contourLogDerivativeHolder Z hγ hγ1 hc hchord (θ : ContourCircle)) θ := by
  rw [contourLogDerivativeHolder_apply]
  exact hasDerivAt_contourSelfIntegral_smooth_near_circle Z Z₀ hγ hc hchord hr href hsmall hs θ

end Euler2D

end
