module

public import RequestProject.Euler.ContourCauchyLocusContinuity

/-! # Joint curve/density continuity in the actual uniform contour norm -/

@[expose] public section

noncomputable section

open Complex Set Filter Topology Metric Real MeasureTheory
open scoped NNReal BoundedContinuousFunction

namespace Euler2D

theorem periodic_contourC1CauchyIncrement {γ : ℝ≥0}
    (Z : ContourC1Space γ) (f : ContourHolderSpace γ) :
    Function.Periodic (contourC1CauchyIncrement Z f) (2 * π) := by
  have hz := ContourC1Space.periodic_lift Z
  have hd : Function.Periodic (deriv (ContourC1Space.lift γ Z)) (2 * π) := by
    intro t
    rw [ContourC1Space.deriv_lift, ContourC1Space.deriv_lift, AddCircle.coe_add_period]
  have hf (t : ℝ) : f ((t + 2 * π : ℝ) : ContourCircle) = f (t : ContourCircle) :=
    congrArg f (AddCircle.coe_add_period (2 * π) t)
  intro θ
  have he : contourC1CauchyIncrementIntegrand Z f (θ + 2 * π) =
      contourC1CauchyIncrementIntegrand Z f θ := by
    funext τ
    dsimp only [contourC1CauchyIncrementIntegrand, contourCauchyIncrementIntegrand]
    rw [show θ + 2 * π + τ = (θ + τ) + 2 * π by ring,
      hd (θ + τ), hz θ, hz (θ + τ), hf (θ + τ), hf θ]
  exact congrArg (fun F : ℝ → ℂ => ∫ τ in Icc (-π) π, F τ) he

def contourCauchyIncrementOnCircle {γ : ℝ≥0} (Z : ContourC1Space γ)
    (f : ContourHolderSpace γ) : ContourCircle → ℂ :=
  (periodic_contourC1CauchyIncrement Z f).lift

@[simp] theorem contourCauchyIncrementOnCircle_coe {γ : ℝ≥0}
    (Z : ContourC1Space γ) (f : ContourHolderSpace γ) (θ : ℝ) :
    contourCauchyIncrementOnCircle Z f (θ : ContourCircle) = contourC1CauchyIncrement Z f θ := rfl

theorem continuous_contourCauchyIncrementOnCircle_on_positiveChordArc {γ : ℝ≥0}
    (hγ : 0 < (γ : ℝ)) :
    Continuous (fun q : ({Z : ContourC1Space γ // ContourC1Space.HasPositiveChordArc Z} ×
        ContourHolderSpace γ) × ContourCircle =>
      contourCauchyIncrementOnCircle q.1.1.val q.1.2 q.2) := by
  have hquot : IsOpenQuotientMap (fun θ : ℝ => (θ : ContourCircle)) :=
    QuotientAddGroup.isOpenQuotientMap_mk
  have hq : IsOpenQuotientMap
      (fun q : ({Z : ContourC1Space γ // ContourC1Space.HasPositiveChordArc Z} ×
          ContourHolderSpace γ) × ℝ => (q.1, (q.2 : ContourCircle))) :=
    IsOpenQuotientMap.id.prodMap hquot
  apply hq.isQuotientMap.continuous_iff.mpr
  simpa only [Function.comp_def, contourCauchyIncrementOnCircle_coe] using
    continuous_contourC1CauchyIncrement_on_positiveChordArc hγ

def contourCauchyIncrementContinuousMap {γ : ℝ≥0} (hγ : 0 < (γ : ℝ))
    (p : {Z : ContourC1Space γ // ContourC1Space.HasPositiveChordArc Z} × ContourHolderSpace γ) :
    C(ContourCircle, ℂ) where
  toFun := contourCauchyIncrementOnCircle p.1.val p.2
  continuous_toFun := by
    have hpair : Continuous (fun θ : ContourCircle => (p, θ)) :=
      continuous_const.prodMk continuous_id
    have hc : Continuous
        (fun q : ({Z : ContourC1Space γ // ContourC1Space.HasPositiveChordArc Z} ×
            ContourHolderSpace γ) × ContourCircle =>
          contourCauchyIncrementOnCircle q.1.1.val q.1.2 q.2) :=
      continuous_contourCauchyIncrementOnCircle_on_positiveChordArc hγ
    exact (hc.comp hpair).congr (fun _ => rfl)

/-- The true Cauchy increment in the genuine uniform function norm. -/
def contourCauchyIncrementBCF {γ : ℝ≥0} (hγ : 0 < (γ : ℝ))
    (p : {Z : ContourC1Space γ // ContourC1Space.HasPositiveChordArc Z} × ContourHolderSpace γ) :
    ContourCircle →ᵇ ℂ :=
  BoundedContinuousFunction.mkOfCompact (contourCauchyIncrementContinuousMap hγ p)

@[simp] theorem contourCauchyIncrementBCF_coe {γ : ℝ≥0} (hγ : 0 < (γ : ℝ))
    (p : {Z : ContourC1Space γ // ContourC1Space.HasPositiveChordArc Z} × ContourHolderSpace γ)
    (θ : ℝ) : contourCauchyIncrementBCF hγ p (θ : ContourCircle) =
      contourC1CauchyIncrement p.1.val p.2 θ := rfl

theorem continuous_contourCauchyIncrementBCF {γ : ℝ≥0} (hγ : 0 < (γ : ℝ)) :
    Continuous (contourCauchyIncrementBCF hγ) := by
  have hu : Continuous
      (Function.uncurry fun p : {Z : ContourC1Space γ // ContourC1Space.HasPositiveChordArc Z} ×
          ContourHolderSpace γ => fun θ : ContourCircle =>
        contourCauchyIncrementContinuousMap hγ p θ) :=
    (continuous_contourCauchyIncrementOnCircle_on_positiveChordArc hγ).congr (fun _ => rfl)
  have hc : Continuous (contourCauchyIncrementContinuousMap hγ) :=
    ContinuousMap.continuous_of_continuous_uncurry _ hu
  exact ((ContinuousMap.isometryEquivBoundedOfCompact ContourCircle ℂ).continuous.comp hc).congr
    (fun _ => rfl)

/-- Identification with every actual bounded Hölder realization of the
same kernel, independently of the selected positive chord constant. -/
theorem contourCauchyIncrementBCF_eq_operator {γ : ℝ≥0}
    (hγ : 0 < (γ : ℝ)) (hγ1 : (γ : ℝ) < 1)
    (p : {Z : ContourC1Space γ // ContourC1Space.HasPositiveChordArc Z} × ContourHolderSpace γ)
    {c : ℝ} (hc : 0 < c)
    (hchord : ∀ θ τ : ℝ, |τ| ≤ π → c * |τ| ≤
      ‖ContourC1Space.lift γ p.1.val θ - ContourC1Space.lift γ p.1.val (θ + τ)‖) :
    contourCauchyIncrementBCF hγ p = HolderFunctionSpace.toBCF γ
      (contourCauchyIncrementOperator p.1.val hγ hγ1 hc hchord p.2) := by
  apply BoundedContinuousFunction.ext
  intro x
  obtain ⟨θ, rfl⟩ := QuotientAddGroup.mk_surjective x
  change contourC1CauchyIncrement p.1.val p.2 θ =
    contourCauchyIncrementOperator p.1.val hγ hγ1 hc hchord p.2 (θ : ContourCircle)
  exact (contourCauchyIncrementOperator_apply p.1.val hγ hγ1 hc hchord p.2 θ).symm

end Euler2D

end
