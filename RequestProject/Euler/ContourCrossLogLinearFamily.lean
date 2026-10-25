module

public import RequestProject.Euler.ContourCrossLogLittle
public import RequestProject.Euler.ContourHolderEvaluationNorm
public import RequestProject.Euler.ContourBaseDerivativeCoordinates
public import Mathlib.Analysis.Normed.Operator.Prod

/-! Actual linear features of the separated cross-log interaction. -/

@[expose] public section

noncomputable section

open Set Filter Topology
open scoped NNReal

namespace Euler2D

open HolderFunctionSpace

local instance (priority := 2000) crossLinearC1_normedAddCommGroup (γ : ℝ≥0) :
    NormedAddCommGroup (ContourC1Space γ) :=
  Submodule.normedAddCommGroup (contourC1GraphSubmodule γ)

local instance (priority := 2000) crossLinearC1_normedSpace (γ : ℝ≥0) :
    NormedSpace ℝ (ContourC1Space γ) := Submodule.normedSpace (contourC1GraphSubmodule γ)

local instance (priority := 2000) crossLinearHolder_normedAddCommGroup (γ : ℝ≥0) :
    NormedAddCommGroup (ContourHolderSpace γ) :=
  Submodule.normedAddCommGroup (holderGraphSubmodule ContourCircle ℂ γ)

local instance (priority := 2000) crossLinearHolder_normedSpace (γ : ℝ≥0) :
    NormedSpace ℝ (ContourHolderSpace γ) := Submodule.normedSpace (holderGraphSubmodule ContourCircle ℂ γ)

variable {γ : ℝ≥0}

def contourC1ValueHolderCLM (hγ1 : (γ : ℝ) ≤ 1) :
    ContourC1Space γ →L[ℝ] ContourHolderSpace γ :=
  ({ toFun := contourC1ValueHolder hγ1
     map_add' := fun Z W => by apply HolderFunctionSpace.ext; intro x; rfl
     map_smul' := fun a Z => by apply HolderFunctionSpace.ext; intro x; rfl } :
      ContourC1Space γ →ₗ[ℝ] ContourHolderSpace γ).mkContinuous
    (contourValueHolderConstant (γ : ℝ)) (norm_contourC1ValueHolder_le hγ1)

@[simp] theorem contourC1ValueHolderCLM_apply (hγ1 : (γ : ℝ) ≤ 1)
    (Z : ContourC1Space γ) : contourC1ValueHolderCLM hγ1 Z = contourC1ValueHolder hγ1 Z := rfl

theorem continuous_contourC1Eval_operator (hγ : 0 < (γ : ℝ)) (hγ1 : (γ : ℝ) ≤ 1) :
    Continuous (fun t : ℝ => ContourC1Space.eval γ (t : ContourCircle)) := by
  have he : Continuous (fun t : ℝ => HolderFunctionSpace.eval γ (E := ℂ) (t : ContourCircle)) :=
    (HolderFunctionSpace.continuous_eval_operator hγ).comp (AddCircle.continuous_mk' (2 * Real.pi))
  exact (he.clm_comp (continuous_const (y := contourC1ValueHolderCLM hγ1))).congr
    (fun t => by ext Z; rfl)

theorem continuous_contourC1DerivativeEval_operator (hγ : 0 < (γ : ℝ)) :
    Continuous (fun t : ℝ => ContourC1Space.derivativeEval γ (t : ContourCircle)) := by
  have he : Continuous (fun t : ℝ => HolderFunctionSpace.eval γ (E := ℂ) (t : ContourCircle)) :=
    (HolderFunctionSpace.continuous_eval_operator hγ).comp (AddCircle.continuous_mk' (2 * Real.pi))
  exact he.clm_comp (continuous_const (y := ContourC1Space.derivative γ))

def contourCrossDenominatorCLM (hγ1 : (γ : ℝ) ≤ 1) (t : ℝ) :
    (ContourC1Space γ × ContourC1Space γ) →L[ℝ] ContourHolderSpace γ :=
  (contourC1ValueHolderCLM hγ1).comp (ContinuousLinearMap.fst ℝ _ _) -
    (contourHolderConstantCLM γ).comp
      ((ContourC1Space.eval γ (t : ContourCircle)).comp (ContinuousLinearMap.snd ℝ _ _))

@[simp] theorem contourCrossDenominatorCLM_apply (hγ1 : (γ : ℝ) ≤ 1) (t : ℝ)
    (p : ContourC1Space γ × ContourC1Space γ) :
    contourCrossDenominatorCLM hγ1 t p = contourCrossDenominatorHolder hγ1 p.1 p.2 t := rfl

abbrev ContourCrossDerivativeFeatures (γ : ℝ≥0) :=
  ContourHolderSpace γ × (ContourHolderSpace γ × ℂ)

def contourCrossDerivativeFeatureCLM (hγ1 : (γ : ℝ) ≤ 1) (t : ℝ) :
    (ContourC1Space γ × ContourC1Space γ) →L[ℝ] ContourCrossDerivativeFeatures γ :=
  (contourCrossDenominatorCLM hγ1 t).prod
    (((ContourC1Space.derivative γ).comp (ContinuousLinearMap.fst ℝ _ _)).prod
      ((ContourC1Space.derivativeEval γ (t : ContourCircle)).comp
        (ContinuousLinearMap.snd ℝ _ _)))

theorem contourCrossDerivativeFeatureCLM_apply (hγ1 : (γ : ℝ) ≤ 1) (t : ℝ)
    (p : ContourC1Space γ × ContourC1Space γ) :
    contourCrossDerivativeFeatureCLM hγ1 t p =
      (contourCrossDenominatorHolder hγ1 p.1 p.2 t,
        ContourC1Space.derivative γ p.1, deriv (ContourC1Space.lift γ p.2) t) := by
  simp only [contourCrossDerivativeFeatureCLM, ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd',
    contourCrossDenominatorCLM_apply, ContourC1Space.derivativeEval_apply, ContourC1Space.deriv_lift]

private theorem continuous_cross_clm_prod {A X Y Z : Type*} [TopologicalSpace A]
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    {f : A → X →L[ℝ] Y} {g : A → X →L[ℝ] Z} (hf : Continuous f) (hg : Continuous g) :
    Continuous (fun a => (f a).prod (g a)) :=
  (ContinuousLinearMap.prodₗᵢ ℝ).continuous.comp (hf.prodMk hg)

theorem continuous_contourCrossDerivativeFeatureCLM (hγ : 0 < (γ : ℝ)) (hγ1 : (γ : ℝ) ≤ 1) :
    Continuous (contourCrossDerivativeFeatureCLM hγ1) := by
  have he := (continuous_contourC1Eval_operator hγ hγ1).clm_comp
    (continuous_const (y := ContinuousLinearMap.snd ℝ (ContourC1Space γ) (ContourC1Space γ)))
  have hd := (continuous_contourC1DerivativeEval_operator hγ).clm_comp
    (continuous_const (y := ContinuousLinearMap.snd ℝ (ContourC1Space γ) (ContourC1Space γ)))
  have hden : Continuous (contourCrossDenominatorCLM hγ1) :=
    continuous_const.sub ((continuous_const (y := contourHolderConstantCLM γ)).clm_comp he)
  exact continuous_cross_clm_prod hden (continuous_cross_clm_prod continuous_const hd)

end Euler2D

end
