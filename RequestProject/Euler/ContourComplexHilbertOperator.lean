module

public import RequestProject.Euler.ContourComplexHolderSpace
public import RequestProject.Euler.ContourHilbertOperator

/-! The proved genuine Hilbert increment operator is complex-linear,
with its original Hölder norm estimate. -/

@[expose] public section

noncomputable section

open Set MeasureTheory
open scoped NNReal

namespace Euler2D

attribute [local instance] HolderFunctionSpace.complexScalarNormedSpace
  HolderFunctionSpace.complexScalarTower

theorem contourHilbertHolder_complex_smul {γ : ℝ≥0} (hγ : 0 < (γ : ℝ))
    (hγ1 : (γ : ℝ) < 1) (a : ℂ) (f : ContourHolderSpace γ) :
    contourHilbertHolder hγ hγ1 (a • f) = a • contourHilbertHolder hγ hγ1 f := by
  apply HolderFunctionSpace.ext
  intro x
  obtain ⟨θ, rfl⟩ := QuotientAddGroup.mk_surjective x
  change (∫ τ in Icc (-Real.pi) Real.pi,
    hilbertIncrementIntegrand (fun t : ℝ => a * f (t : ContourCircle)) θ τ) =
      a * (∫ τ in Icc (-Real.pi) Real.pi,
        hilbertIncrementIntegrand (fun t : ℝ => f (t : ContourCircle)) θ τ)
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with τ
  dsimp only [hilbertIncrementIntegrand]
  ring

def contourComplexHilbertOperator {γ : ℝ≥0} (hγ : 0 < (γ : ℝ)) (hγ1 : (γ : ℝ) < 1) :
    ContourHolderSpace γ →L[ℂ] ContourHolderSpace γ :=
  LinearMap.mkContinuous
    { toFun := contourHilbertHolder hγ hγ1
      map_add' := (contourHilbertLinearMap hγ hγ1).map_add
      map_smul' := contourHilbertHolder_complex_smul hγ hγ1 }
    (hilbertOperatorConstant (γ : ℝ)) (norm_contourHilbertHolder_le hγ hγ1)

@[simp] theorem contourComplexHilbertOperator_apply {γ : ℝ≥0}
    (hγ : 0 < (γ : ℝ)) (hγ1 : (γ : ℝ) < 1) (f : ContourHolderSpace γ) (θ : ℝ) :
    contourComplexHilbertOperator hγ hγ1 f (θ : ContourCircle) = contourHilbertIncrement f θ := rfl

theorem contourComplexHilbertOperator_restrictScalars {γ : ℝ≥0}
    (hγ : 0 < (γ : ℝ)) (hγ1 : (γ : ℝ) < 1) :
    (contourComplexHilbertOperator hγ hγ1).restrictScalars ℝ = contourHilbertOperator hγ hγ1 := by
  ext f x
  rfl

end Euler2D

end
