module

public import RequestProject.Euler.ContourJointNormalizedChord
public import RequestProject.Euler.ContourJointResidualOperator
public import RequestProject.Euler.ContourComplexHilbertOperator
public import RequestProject.Euler.ContourCauchyOperator

/-! Genuine complex analyticity of the actual contour Cauchy increment
operator.  The joint Hölder formula is identified with the literal
original residue integral before the analytic statement is applied. -/

@[expose] public section

noncomputable section

open Set Filter Topology MeasureTheory
open scoped NNReal

namespace Euler2D

attribute [local instance] HolderFunctionSpace.complexScalarNormedSpace
  HolderFunctionSpace.complexScalarTower ContourC1Space.complexScalarNormedSpace
  ContourC1Space.complexScalarTower

variable {γ : ℝ≥0}

local instance complexCauchyOperator_scalarTower (γ : ℝ≥0) :
    IsScalarTower ℝ ℂ (ContourHolderSpace γ →L[ℂ] ContourHolderSpace γ) where
  smul_assoc r a L := by
    apply ContinuousLinearMap.ext
    intro f
    exact smul_assoc r a (L f)

theorem contourJointNormalizedQuotient_sample (hγ : 0 < (γ : ℝ))
    (Z : ContourC1Space γ) {c : ℝ} (hc : 0 < c)
    (hZ : ContourC1Space.HasChordArcLower Z c) (θ τ : ℝ) (hτ : |τ| ≤ Real.pi) :
    contourJointSample (contourJointNormalizedQuotient hγ Z) (θ : ContourCircle) τ =
      deriv (ContourC1Space.lift γ Z) (θ + τ) /
        contourNormalizedChord hγ Z τ (θ : ContourCircle) := by
  rw [contourJointSample_of_mem _ _ _ (abs_le.mp hτ),
    contourJointNormalizedQuotient_apply hγ Z hc hZ]
  simp only [ContourC1Space.deriv_lift, AddCircle.coe_add]

theorem contourJointResidualIntegrand_eq_actual (hγ : 0 < (γ : ℝ))
    (Z : ContourC1Space γ) {c : ℝ} (hc : 0 < c)
    (hZ : ContourC1Space.HasChordArcLower Z c) (f : ContourHolderSpace γ)
    (θ τ : ℝ) (hτ : |τ| ≤ Real.pi) :
    contourJointResidualIntegrand (contourJointNormalizedQuotient hγ Z) f (θ : ContourCircle) τ =
      contourCauchyResidualIncrementIntegrand (ContourC1Space.lift γ Z)
        (deriv (ContourC1Space.lift γ Z)) (fun t : ℝ => f (t : ContourCircle)) θ τ := by
  by_cases ht : τ = 0
  · subst τ
    simp only [contourJointResidualIntegrand_zero,
      contourCauchyResidualIncrementIntegrand, add_zero, sub_self, mul_zero]
  · rw [contourJointResidualIntegrand, contourJointNormalizedQuotient_zero hγ Z hc hZ,
      contourJointNormalizedQuotient_sample hγ Z hc hZ θ τ hτ,
      contourCauchyResidualIncrementIntegrand, contourCauchyPoleIntegrand_eq_normalized hγ Z ht]
    simp only [contourDensityIncrement, AddCircle.coe_add, Complex.real_smul,
      Complex.ofReal_inv]
    ring

def contourComplexCauchyResidualShape (hγ : 0 < (γ : ℝ)) (Z : ContourC1Space γ) :
    ContourHolderSpace γ →L[ℂ] ContourHolderSpace γ :=
  contourJointResidualOperator hγ (contourJointNormalizedQuotient hγ Z)

theorem contourComplexCauchyResidualShape_apply (hγ : 0 < (γ : ℝ))
    (Z : ContourC1Space γ) {c : ℝ} (hc : 0 < c)
    (hZ : ContourC1Space.HasChordArcLower Z c) (f : ContourHolderSpace γ) (θ : ℝ) :
    contourComplexCauchyResidualShape hγ Z f (θ : ContourCircle) =
      contourC1CauchyResidualIncrement Z f θ := by
  change (∫ τ in Icc (-Real.pi) Real.pi,
    contourJointResidualIntegrand (contourJointNormalizedQuotient hγ Z) f (θ : ContourCircle) τ) = _
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Icc] with τ hτ
  exact contourJointResidualIntegrand_eq_actual hγ Z hc hZ f θ τ (abs_le.mpr hτ)

theorem contourComplexCauchyResidualShape_restrictScalars (hγ : 0 < (γ : ℝ))
    (Z : ContourC1Space γ) {c : ℝ} (hc : 0 < c)
    (hZ : ContourC1Space.HasChordArcLower Z c) :
    (contourComplexCauchyResidualShape hγ Z).restrictScalars ℝ =
      contourCauchyResidualOperator Z hγ hc hZ := by
  ext f x
  obtain ⟨θ, rfl⟩ := QuotientAddGroup.mk_surjective x
  exact contourComplexCauchyResidualShape_apply hγ Z hc hZ f θ

theorem analyticAt_contourComplexCauchyResidualShape (hγ : 0 < (γ : ℝ))
    (Z : ContourC1Space γ) {c : ℝ} (hc : 0 < c)
    (hZ : ContourC1Space.HasChordArcLower Z c) :
    AnalyticAt ℂ (contourComplexCauchyResidualShape hγ) Z := by
  exact (((contourJointResidualOperator hγ).analyticAt (contourJointNormalizedQuotient hγ Z)).comp
    (f := contourJointNormalizedQuotient hγ)
      (analyticAt_contourJointNormalizedQuotient hγ Z hc hZ)).congr
        (Eventually.of_forall (fun _ => rfl))

def contourComplexCauchyIncrementShape (hγ : 0 < (γ : ℝ)) (hγ1 : (γ : ℝ) < 1)
    (Z : ContourC1Space γ) : ContourHolderSpace γ →L[ℂ] ContourHolderSpace γ :=
  contourComplexCauchyResidualShape hγ Z - contourComplexHilbertOperator hγ hγ1

theorem contourComplexCauchyIncrementShape_apply (hγ : 0 < (γ : ℝ))
    (hγ1 : (γ : ℝ) < 1) (Z : ContourC1Space γ) {c : ℝ} (hc : 0 < c)
    (hZ : ContourC1Space.HasChordArcLower Z c) (f : ContourHolderSpace γ) (θ : ℝ) :
    contourComplexCauchyIncrementShape hγ hγ1 Z f (θ : ContourCircle) =
      contourC1CauchyIncrement Z f θ := by
  change contourComplexCauchyResidualShape hγ Z f (θ : ContourCircle) -
    contourComplexHilbertOperator hγ hγ1 f (θ : ContourCircle) = _
  rw [contourComplexCauchyResidualShape_apply hγ Z hc hZ,
    contourComplexHilbertOperator_apply]
  exact (contourC1CauchyIncrement_eq_residual_sub_hilbert Z f hγ hc
    (fun τ hτ => hZ θ τ (abs_le.mpr hτ))).symm

theorem contourComplexCauchyIncrementShape_restrictScalars (hγ : 0 < (γ : ℝ))
    (hγ1 : (γ : ℝ) < 1) (Z : ContourC1Space γ) {c : ℝ} (hc : 0 < c)
    (hZ : ContourC1Space.HasChordArcLower Z c) :
    (contourComplexCauchyIncrementShape hγ hγ1 Z).restrictScalars ℝ =
      contourCauchyIncrementOperator Z hγ hγ1 hc hZ := by
  unfold ContourC1Space.HasChordArcLower at hZ
  ext f x
  obtain ⟨θ, rfl⟩ := QuotientAddGroup.mk_surjective x
  rw [contourCauchyIncrementOperator_apply]
  exact contourComplexCauchyIncrementShape_apply hγ hγ1 Z hc hZ f θ

theorem analyticAt_contourComplexCauchyIncrementShape (hγ : 0 < (γ : ℝ))
    (hγ1 : (γ : ℝ) < 1) (Z : ContourC1Space γ) {c : ℝ} (hc : 0 < c)
    (hZ : ContourC1Space.HasChordArcLower Z c) :
    AnalyticAt ℂ (contourComplexCauchyIncrementShape hγ hγ1) Z :=
  (analyticAt_contourComplexCauchyResidualShape hγ Z hc hZ).sub analyticAt_const

theorem realAnalyticAt_contourComplexCauchyIncrementShape (hγ : 0 < (γ : ℝ))
    (hγ1 : (γ : ℝ) < 1) (Z : ContourC1Space γ) {c : ℝ} (hc : 0 < c)
    (hZ : ContourC1Space.HasChordArcLower Z c) :
    AnalyticAt ℝ (contourComplexCauchyIncrementShape hγ hγ1) Z :=
  (analyticAt_contourComplexCauchyIncrementShape hγ hγ1 Z hc hZ).restrictScalars

end Euler2D

end
