module

public import RequestProject.Euler.ContourComplexCauchyAnalytic
public import RequestProject.Euler.ContourDerivativePhaseAnalytic
public import RequestProject.Euler.ContourLogDerivativeHolder
public import RequestProject.Euler.ContourLogDerivativeContinuity

/-! Actual real analyticity of the genuine Hölder-valued spatial
derivative of the self-log contour operator. -/

@[expose] public section

noncomputable section

open Set Filter Topology
open scoped NNReal ContDiff

namespace Euler2D

attribute [local instance] HolderFunctionSpace.complexScalarNormedSpace
  HolderFunctionSpace.complexScalarTower ContourC1Space.complexScalarNormedSpace
  ContourC1Space.complexScalarTower

variable {γ : ℝ≥0}

private theorem real_analyticAt_complexOperator_apply
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedSpace ℂ V]
    [IsScalarTower ℝ ℂ V] (v : V) (L : V →L[ℂ] V) :
    AnalyticAt ℝ (fun p : V × (V →L[ℂ] V) => p.2 p.1) (v, L) :=
  ((ContinuousLinearMap.apply ℂ V (E := V)).bilinearRestrictScalars ℝ).analyticAt_bilinear (v, L)

def analyticContourLogDerivativeHolder (hγ : 0 < (γ : ℝ)) (hγ1 : (γ : ℝ) < 1)
    (Z : ContourC1Space γ) : ContourHolderSpace γ :=
  (1 / 2 : ℝ) • HolderFunctionSpace.pointwiseMul
    (HolderFunctionSpace.conjugate (ContourC1Space.derivative γ Z))
    (HolderFunctionSpace.conjugate
      (contourComplexCauchyIncrementShape hγ hγ1 Z (analyticContourDerivativePhase γ Z)))

theorem analyticContourLogDerivativeHolder_eq (hγ : 0 < (γ : ℝ)) (hγ1 : (γ : ℝ) < 1)
    (Z : ContourC1Space γ) {c : ℝ} (hc : 0 < c)
    (hZ : ContourC1Space.HasChordArcLower Z c) :
    analyticContourLogDerivativeHolder hγ hγ1 Z = contourLogDerivativeHolder Z hγ hγ1 hc hZ := by
  have he := congrArg
    (fun L : ContourHolderSpace γ →L[ℝ] ContourHolderSpace γ => L (contourDerivativePhase Z hc hZ))
    (contourComplexCauchyIncrementShape_restrictScalars hγ hγ1 Z hc hZ)
  unfold analyticContourLogDerivativeHolder contourLogDerivativeHolder
  rw [analyticContourDerivativePhase_eq Z hc hZ]
  exact congrArg (fun f : ContourHolderSpace γ => (1 / 2 : ℝ) •
    HolderFunctionSpace.pointwiseMul
      (HolderFunctionSpace.conjugate (ContourC1Space.derivative γ Z))
      (HolderFunctionSpace.conjugate f)) he

theorem analyticAt_contourLogDerivativeHolder (hγ : 0 < (γ : ℝ)) (hγ1 : (γ : ℝ) < 1)
    (Z : ContourC1Space γ) {c : ℝ} (hc : 0 < c)
    (hZ : ContourC1Space.HasChordArcLower Z c) :
    AnalyticAt ℝ (analyticContourLogDerivativeHolder hγ hγ1) Z := by
  have hp := analyticAt_contourDerivativePhase Z hc hZ
  have hC := realAnalyticAt_contourComplexCauchyIncrementShape hγ hγ1 Z hc hZ
  have hA := real_analyticAt_complexOperator_apply (analyticContourDerivativePhase γ Z)
    (contourComplexCauchyIncrementShape hγ hγ1 Z)
  have hCa : AnalyticAt ℝ (fun W : ContourC1Space γ =>
      contourComplexCauchyIncrementShape hγ hγ1 W (analyticContourDerivativePhase γ W)) Z :=
    hA.comp (f := fun W : ContourC1Space γ =>
      (analyticContourDerivativePhase γ W, contourComplexCauchyIncrementShape hγ hγ1 W))
      (hp.prod hC)
  have hD := ((HolderFunctionSpace.conjugateCLM (X := ContourCircle) γ).analyticAt
      (ContourC1Space.derivative γ Z)).comp ((ContourC1Space.derivative γ).analyticAt Z)
  have hCc := ((HolderFunctionSpace.conjugateCLM (X := ContourCircle) γ).analyticAt
      (contourComplexCauchyIncrementShape hγ hγ1 Z (analyticContourDerivativePhase γ Z))).comp
        (f := fun W : ContourC1Space γ =>
          contourComplexCauchyIncrementShape hγ hγ1 W (analyticContourDerivativePhase γ W)) hCa
  have hpair := hD.prod hCc
  exact ((((1 / 2 : ℝ) • (HolderFunctionSpace.pointwiseMulCLM (X := ContourCircle) γ)).analyticAt_bilinear
    (HolderFunctionSpace.conjugate (ContourC1Space.derivative γ Z),
      HolderFunctionSpace.conjugate
        (contourComplexCauchyIncrementShape hγ hγ1 Z (analyticContourDerivativePhase γ Z)))).comp
      (f := fun W : ContourC1Space γ =>
        (HolderFunctionSpace.conjugate (ContourC1Space.derivative γ W),
          HolderFunctionSpace.conjugate
            (contourComplexCauchyIncrementShape hγ hγ1 W (analyticContourDerivativePhase γ W))))
              hpair).congr (Eventually.of_forall (fun _ => rfl))

theorem analyticOnNhd_contourLogDerivativeHolder (hγ : 0 < (γ : ℝ)) (hγ1 : (γ : ℝ) < 1) :
    AnalyticOnNhd ℝ (analyticContourLogDerivativeHolder hγ hγ1)
      {Z : ContourC1Space γ | ContourC1Space.HasPositiveChordArc Z} := by
  rintro Z ⟨c, hc, hZ⟩
  exact analyticAt_contourLogDerivativeHolder hγ hγ1 Z hc hZ

theorem contDiffOn_contourLogDerivativeHolder (hγ : 0 < (γ : ℝ)) (hγ1 : (γ : ℝ) < 1)
    (n : WithTop ℕ∞) :
    ContDiffOn ℝ n (analyticContourLogDerivativeHolder hγ hγ1)
      {Z : ContourC1Space γ | ContourC1Space.HasPositiveChordArc Z} := by
  rintro Z ⟨c, hc, hZ⟩
  exact (analyticAt_contourLogDerivativeHolder hγ hγ1 Z hc hZ).contDiffAt.contDiffWithinAt

theorem contDiffAt_contourLogDerivativeHolder (hγ : 0 < (γ : ℝ)) (hγ1 : (γ : ℝ) < 1)
    (Z : ContourC1Space γ) {c : ℝ} (hc : 0 < c)
    (hZ : ContourC1Space.HasChordArcLower Z c) (n : WithTop ℕ∞) :
    ContDiffAt ℝ n (analyticContourLogDerivativeHolder hγ hγ1) Z :=
  (analyticAt_contourLogDerivativeHolder hγ hγ1 Z hc hZ).contDiffAt

theorem analyticContourLogDerivativeHolder_eq_positive
    (hγ : 0 < (γ : ℝ)) (hγ1 : (γ : ℝ) < 1) (Z : PositiveChordContour γ) :
    analyticContourLogDerivativeHolder hγ hγ1 Z.val = positiveContourLogDerivativeHolder hγ hγ1 Z :=
  analyticContourLogDerivativeHolder_eq hγ hγ1 Z.val (positiveChordConstant_pos Z)
    (hasChordArcLower_positiveChordConstant Z)

end Euler2D

end
