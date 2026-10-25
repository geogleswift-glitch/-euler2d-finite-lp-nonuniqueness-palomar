module

public import RequestProject.Euler.ContourHilbertOperator
public import RequestProject.Euler.ContourCauchyHilbertDecomposition
public import RequestProject.Euler.ContourC1PrincipalValue
public import RequestProject.Euler.ContourHolderScalar

/-! # The genuine bounded Cauchy increment operator -/

@[expose] public section

noncomputable section

open Set MeasureTheory Filter Topology Complex
open scoped NNReal

namespace Euler2D

/-- The actual Cauchy increment, decomposed into its proved bounded
remainder and its proved universal Hilbert operator. -/
def contourCauchyIncrementOperator {γ : ℝ≥0} (Z : ContourC1Space γ) {c : ℝ}
    (hγ : 0 < (γ : ℝ)) (hγ1 : (γ : ℝ) < 1) (hc : 0 < c)
    (hchord : ∀ θ τ : ℝ, |τ| ≤ Real.pi → c * |τ| ≤
      ‖ContourC1Space.lift γ Z θ - ContourC1Space.lift γ Z (θ + τ)‖) :
    ContourHolderSpace γ →L[ℝ] ContourHolderSpace γ :=
  contourCauchyResidualOperator Z hγ hc hchord - contourHilbertOperator hγ hγ1

@[simp] theorem contourCauchyIncrementOperator_apply {γ : ℝ≥0} (Z : ContourC1Space γ) {c : ℝ}
    (hγ : 0 < (γ : ℝ)) (hγ1 : (γ : ℝ) < 1) (hc : 0 < c)
    (hchord : ∀ θ τ : ℝ, |τ| ≤ Real.pi → c * |τ| ≤
      ‖ContourC1Space.lift γ Z θ - ContourC1Space.lift γ Z (θ + τ)‖)
    (f : ContourHolderSpace γ) (θ : ℝ) :
    contourCauchyIncrementOperator Z hγ hγ1 hc hchord f (θ : ContourCircle) =
      contourC1CauchyIncrement Z f θ := by
  change contourC1CauchyResidualIncrement Z f θ - contourHilbertIncrement f θ = _
  exact (contourC1CauchyIncrement_eq_residual_sub_hilbert Z f hγ hc (fun τ hτ =>
    hchord θ τ (abs_le.mpr ⟨hτ.1, hτ.2⟩))).symm

def contourCauchyIncrementOperatorConstant (γ L c : ℝ) : ℝ :=
  contourRemainderUniformConstant γ L c Real.pi +
    contourRemainderHolderConstant γ L L c Real.pi + hilbertOperatorConstant γ

theorem norm_contourCauchyIncrementOperator_le {γ : ℝ≥0} (Z : ContourC1Space γ) {c : ℝ}
    (hγ : 0 < (γ : ℝ)) (hγ1 : (γ : ℝ) < 1) (hc : 0 < c)
    (hchord : ∀ θ τ : ℝ, |τ| ≤ Real.pi → c * |τ| ≤
      ‖ContourC1Space.lift γ Z θ - ContourC1Space.lift γ Z (θ + τ)‖) :
    ‖contourCauchyIncrementOperator Z hγ hγ1 hc hchord‖ ≤
      contourCauchyIncrementOperatorConstant (γ : ℝ) ‖Z‖ c := by
  change ‖contourCauchyResidualOperator Z hγ hc hchord - contourHilbertOperator hγ hγ1‖ ≤ _
  exact (norm_sub_le (contourCauchyResidualOperator Z hγ hc hchord)
    (contourHilbertOperator hγ hγ1)).trans (add_le_add
      (norm_contourCauchyResidualOperator_le Z hγ hc hchord)
      (norm_contourHilbertOperator_le hγ hγ1))

/-- Add an actual complex constant-density contribution to the proved
increment operator.  The principal-value identification is made below
only where the corresponding value has been proved. -/
def contourCauchyOperatorWithConstant {γ : ℝ≥0} (Z : ContourC1Space γ) {c : ℝ}
    (hγ : 0 < (γ : ℝ)) (hγ1 : (γ : ℝ) < 1) (hc : 0 < c)
    (hchord : ∀ θ τ : ℝ, |τ| ≤ Real.pi → c * |τ| ≤
      ‖ContourC1Space.lift γ Z θ - ContourC1Space.lift γ Z (θ + τ)‖) (p : ℂ) :
    ContourHolderSpace γ →L[ℝ] ContourHolderSpace γ :=
  HolderFunctionSpace.valueMulOperator γ p + contourCauchyIncrementOperator Z hγ hγ1 hc hchord

@[simp] theorem contourCauchyOperatorWithConstant_apply {γ : ℝ≥0} (Z : ContourC1Space γ) {c : ℝ}
    (hγ : 0 < (γ : ℝ)) (hγ1 : (γ : ℝ) < 1) (hc : 0 < c)
    (hchord : ∀ θ τ : ℝ, |τ| ≤ Real.pi → c * |τ| ≤
      ‖ContourC1Space.lift γ Z θ - ContourC1Space.lift γ Z (θ + τ)‖)
    (p : ℂ) (f : ContourHolderSpace γ) (θ : ℝ) :
    contourCauchyOperatorWithConstant Z hγ hγ1 hc hchord p f (θ : ContourCircle) =
      p * f (θ : ContourCircle) + contourC1CauchyIncrement Z f θ := by
  change p * f (θ : ContourCircle) +
    contourCauchyIncrementOperator Z hγ hγ1 hc hchord f (θ : ContourCircle) = _
  rw [contourCauchyIncrementOperator_apply]

theorem norm_contourCauchyOperatorWithConstant_le {γ : ℝ≥0} (Z : ContourC1Space γ) {c : ℝ}
    (hγ : 0 < (γ : ℝ)) (hγ1 : (γ : ℝ) < 1) (hc : 0 < c)
    (hchord : ∀ θ τ : ℝ, |τ| ≤ Real.pi → c * |τ| ≤
      ‖ContourC1Space.lift γ Z θ - ContourC1Space.lift γ Z (θ + τ)‖) (p : ℂ) :
    ‖contourCauchyOperatorWithConstant Z hγ hγ1 hc hchord p‖ ≤
      2 * ‖p‖ + contourCauchyIncrementOperatorConstant (γ : ℝ) ‖Z‖ c := by
  exact (norm_add_le (HolderFunctionSpace.valueMulOperator γ p)
    (contourCauchyIncrementOperator Z hγ hγ1 hc hchord)).trans (add_le_add
      (HolderFunctionSpace.norm_valueMulOperator_le γ p)
      (norm_contourCauchyIncrementOperator_le Z hγ hγ1 hc hchord))

/-- The actual positively oriented near-circle Cauchy principal-value
operator, using the proved constant-density value `-Iπ`. -/
def contourCauchyPrincipalValueOperatorNearCircle {γ : ℝ≥0}
    (Z Z₀ : ContourC1Space γ) {r : ℝ} (hγ : 0 < (γ : ℝ)) (hγ1 : (γ : ℝ) < 1)
    (hr : 0 < r) (href : ContourC1Space.lift γ Z₀ = refCircle r)
    (hsmall : ‖Z - Z₀‖ < 2 * r / Real.pi) :
    ContourHolderSpace γ →L[ℝ] ContourHolderSpace γ :=
  contourCauchyOperatorWithConstant Z hγ hγ1 (sub_pos.mpr hsmall)
    (fun θ τ hτ => contourC1_chord_lower_of_norm_sub Z Z₀ hr.le href θ (abs_le.mp hτ))
    (-Complex.I * (Real.pi : ℂ))

@[simp] theorem contourCauchyPrincipalValueOperatorNearCircle_apply {γ : ℝ≥0}
    (Z Z₀ : ContourC1Space γ) {r : ℝ} (hγ : 0 < (γ : ℝ)) (hγ1 : (γ : ℝ) < 1)
    (hr : 0 < r) (href : ContourC1Space.lift γ Z₀ = refCircle r)
    (hsmall : ‖Z - Z₀‖ < 2 * r / Real.pi) (f : ContourHolderSpace γ) (θ : ℝ) :
    contourCauchyPrincipalValueOperatorNearCircle Z Z₀ hγ hγ1 hr href hsmall f
      (θ : ContourCircle) =
      (-Complex.I * (Real.pi : ℂ)) * f (θ : ContourCircle) + contourC1CauchyIncrement Z f θ := by
  simp only [contourCauchyPrincipalValueOperatorNearCircle, contourCauchyOperatorWithConstant_apply]

theorem tendsto_contourCauchyPrincipalValueOperatorNearCircle {γ : ℝ≥0}
    (Z Z₀ : ContourC1Space γ) {r : ℝ} (hγ : 0 < (γ : ℝ)) (hγ1 : (γ : ℝ) < 1)
    (hr : 0 < r) (href : ContourC1Space.lift γ Z₀ = refCircle r)
    (hsmall : ‖Z - Z₀‖ < 2 * r / Real.pi) (f : ContourHolderSpace γ) (θ : ℝ) :
    Tendsto (contourCauchyWeightedTruncated (ContourC1Space.lift γ Z)
      (deriv (ContourC1Space.lift γ Z)) (fun t : ℝ => f (t : ContourCircle)) θ Real.pi)
      (𝓝[>] (0 : ℝ))
      (𝓝 (contourCauchyPrincipalValueOperatorNearCircle Z Z₀ hγ hγ1 hr href hsmall f
        (θ : ContourCircle))) := by
  rw [contourCauchyPrincipalValueOperatorNearCircle_apply]
  exact tendsto_contourC1CauchyWeightedTruncated_near_circle Z Z₀ f hγ hr href hsmall θ

theorem norm_contourCauchyPrincipalValueOperatorNearCircle_le {γ : ℝ≥0}
    (Z Z₀ : ContourC1Space γ) {r : ℝ} (hγ : 0 < (γ : ℝ)) (hγ1 : (γ : ℝ) < 1)
    (hr : 0 < r) (href : ContourC1Space.lift γ Z₀ = refCircle r)
    (hsmall : ‖Z - Z₀‖ < 2 * r / Real.pi) :
    ‖contourCauchyPrincipalValueOperatorNearCircle Z Z₀ hγ hγ1 hr href hsmall‖ ≤
      2 * Real.pi + contourCauchyIncrementOperatorConstant (γ : ℝ) ‖Z‖
        (2 * r / Real.pi - ‖Z - Z₀‖) := by
  have hb := norm_contourCauchyOperatorWithConstant_le Z hγ hγ1 (sub_pos.mpr hsmall)
    (fun θ τ hτ => contourC1_chord_lower_of_norm_sub Z Z₀ hr.le href θ (abs_le.mp hτ))
    (-Complex.I * (Real.pi : ℂ))
  simpa only [contourCauchyPrincipalValueOperatorNearCircle, norm_mul, norm_neg,
    Complex.norm_I, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos, one_mul] using hb

end Euler2D

end
