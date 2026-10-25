module

public import RequestProject.Euler.ContourLogOperatorContinuity

/-!
# The actual logarithmic contour operator as a continuous C⁰-valued map

Periodicity descends the genuine relative-angle integral to the actual
quotient circle.  Joint continuity and compactness then give continuity
in the uniform norm of bounded continuous functions.
-/

@[expose] public section

noncomputable section

open Complex Set Filter Topology Metric Real MeasureTheory
open scoped BoundedContinuousFunction NNReal

namespace Euler2D

namespace ContourC1Space

variable {γ : ℝ≥0}

theorem periodic_selfLogIntegral (f : ContourC1Space γ) :
    Function.Periodic (selfLogIntegral f) (2 * π) := by
  have hd : Function.Periodic (deriv (lift γ f)) (2 * π) := by
    intro θ
    rw [deriv_lift, deriv_lift, AddCircle.coe_add_period]
  intro θ
  have he : contourSelfIntegrand (lift γ f) (deriv (lift γ f)) (θ + 2 * π) =
      contourSelfIntegrand (lift γ f) (deriv (lift γ f)) θ := by
    funext τ
    dsimp only [contourSelfIntegrand, contourLogIntegrand]
    rw [(periodic_lift f) θ,
      show θ + 2 * π + τ = (θ + τ) + 2 * π by ring,
      (periodic_lift f) (θ + τ), hd (θ + τ)]
  exact congrArg (fun F : ℝ → ℂ => ∫ τ in (-π)..π, F τ) he

/-- The same literal integral on the true quotient circle. -/
def selfLogCircle (f : ContourC1Space γ) : ContourCircle → ℂ :=
  (periodic_selfLogIntegral f).lift

@[simp] theorem selfLogCircle_coe (f : ContourC1Space γ) (θ : ℝ) :
    selfLogCircle f (θ : ContourCircle) = selfLogIntegral f θ := rfl

theorem continuous_selfLogCircle_on_positiveChordArc :
    Continuous (fun q : {f : ContourC1Space γ // HasPositiveChordArc f} × ContourCircle =>
      selfLogCircle q.1.val q.2) := by
  have hquot : IsOpenQuotientMap (fun θ : ℝ => (θ : ContourCircle)) :=
    QuotientAddGroup.isOpenQuotientMap_mk
  have hq : IsOpenQuotientMap
      (fun q : {f : ContourC1Space γ // HasPositiveChordArc f} × ℝ =>
        (q.1, (q.2 : ContourCircle))) := IsOpenQuotientMap.id.prodMap hquot
  apply hq.isQuotientMap.continuous_iff.mpr
  simpa only [Function.comp_def, selfLogCircle_coe] using
    (continuous_selfLogIntegral_on_positiveChordArc (γ := γ))

def selfLogCircleContinuousMap (f : {f : ContourC1Space γ // HasPositiveChordArc f}) :
    C(ContourCircle, ℂ) where
  toFun := selfLogCircle f.val
  continuous_toFun := by
    have hpair : Continuous (fun θ : ContourCircle => (f, θ)) :=
      continuous_const.prodMk continuous_id
    have hc : Continuous
        (fun q : {f : ContourC1Space γ // HasPositiveChordArc f} × ContourCircle =>
          selfLogCircle q.1.val q.2) := continuous_selfLogCircle_on_positiveChordArc
    exact (hc.comp hpair).congr (fun _ => rfl)

/-- The genuine contour operator with the actual uniform C⁰ norm. -/
def selfLogCircleBCF (f : {f : ContourC1Space γ // HasPositiveChordArc f}) :
    ContourCircle →ᵇ ℂ :=
  BoundedContinuousFunction.mkOfCompact (selfLogCircleContinuousMap f)

@[simp] theorem selfLogCircleBCF_coe
    (f : {f : ContourC1Space γ // HasPositiveChordArc f}) (θ : ℝ) :
    selfLogCircleBCF f (θ : ContourCircle) = selfLogIntegral f.val θ := rfl

theorem continuous_selfLogCircleBCF :
    Continuous (selfLogCircleBCF (γ := γ)) := by
  have hu : Continuous
      (Function.uncurry fun f : {f : ContourC1Space γ // HasPositiveChordArc f} =>
        fun θ : ContourCircle => selfLogCircleContinuousMap f θ) :=
    continuous_selfLogCircle_on_positiveChordArc.congr (fun _ => rfl)
  have hc : Continuous (selfLogCircleContinuousMap (γ := γ)) :=
    ContinuousMap.continuous_of_continuous_uncurry _ hu
  exact ((ContinuousMap.isometryEquivBoundedOfCompact ContourCircle ℂ).continuous.comp hc).congr
    (fun _ => rfl)

end ContourC1Space

namespace LittleContourSpace

variable {γ : ℝ≥0}

/-- The same actual chord condition, restricted to the closed little space. -/
def HasPositiveChordArc (f : LittleContourSpace γ) : Prop :=
  ContourC1Space.HasPositiveChordArc (inclusion γ f)

theorem isOpen_hasPositiveChordArc (γ : ℝ≥0) :
    IsOpen {f : LittleContourSpace γ | HasPositiveChordArc f} :=
  (ContourC1Space.isOpen_hasPositiveChordArc γ).preimage (inclusion γ).continuous

/-- Restriction of the genuine integral operator to the actual little space. -/
def selfLogCircleBCF (f : {f : LittleContourSpace γ // HasPositiveChordArc f}) :
    ContourCircle →ᵇ ℂ :=
  ContourC1Space.selfLogCircleBCF ⟨inclusion γ f.val, f.property⟩

@[simp] theorem selfLogCircleBCF_coe
    (f : {f : LittleContourSpace γ // HasPositiveChordArc f}) (θ : ℝ) :
    selfLogCircleBCF f (θ : ContourCircle) =
      contourSelfIntegral (lift γ f.val) (deriv (lift γ f.val)) θ := rfl

theorem continuous_selfLogCircleBCF :
    Continuous (selfLogCircleBCF (γ := γ)) := by
  have hi : Continuous
      (fun f : {f : LittleContourSpace γ // HasPositiveChordArc f} =>
        (⟨inclusion γ f.val, f.property⟩ :
          {g : ContourC1Space γ // ContourC1Space.HasPositiveChordArc g})) :=
    ((inclusion γ).continuous.comp continuous_subtype_val).subtype_mk _
  exact (ContourC1Space.continuous_selfLogCircleBCF.comp hi).congr (fun _ => rfl)

end LittleContourSpace

end Euler2D

end
