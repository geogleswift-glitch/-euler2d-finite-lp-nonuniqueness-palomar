module

public import RequestProject.Euler.ContourCrossLogLinearFamily
public import RequestProject.Euler.ContourCompactLinearFamilyIntegral

/-! Genuine smooth dependence of the cross-log value at a fixed parameter. -/

@[expose] public section

noncomputable section

open Set Filter Topology MeasureTheory
open scoped NNReal ContDiff

namespace Euler2D

local instance (priority := 2000) crossValueC1_normedAddCommGroup (γ : ℝ≥0) :
    NormedAddCommGroup (ContourC1Space γ) := Submodule.normedAddCommGroup (contourC1GraphSubmodule γ)

local instance (priority := 2000) crossValueC1_normedSpace (γ : ℝ≥0) :
    NormedSpace ℝ (ContourC1Space γ) := Submodule.normedSpace (contourC1GraphSubmodule γ)

variable {γ : ℝ≥0}

def contourCrossValueFeatureCLM (θ t : ℝ) :
    (ContourC1Space γ × ContourC1Space γ) →L[ℝ] ℂ × ℂ :=
  (((ContourC1Space.eval γ (θ : ContourCircle)).comp (ContinuousLinearMap.fst ℝ _ _) -
      (ContourC1Space.eval γ (t : ContourCircle)).comp (ContinuousLinearMap.snd ℝ _ _))).prod
    ((ContourC1Space.derivativeEval γ (t : ContourCircle)).comp (ContinuousLinearMap.snd ℝ _ _))

theorem contourCrossValueFeatureCLM_apply (θ t : ℝ)
    (p : ContourC1Space γ × ContourC1Space γ) :
    contourCrossValueFeatureCLM θ t p =
      (ContourC1Space.lift γ p.1 θ - ContourC1Space.lift γ p.2 t,
        deriv (ContourC1Space.lift γ p.2) t) := by
  simp only [contourCrossValueFeatureCLM, ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', ContourC1Space.eval_apply,
    ContourC1Space.derivativeEval_apply, ContourC1Space.deriv_lift]
  rfl

theorem continuous_contourCrossValueFeatureCLM (hγ : 0 < (γ : ℝ)) (hγ1 : (γ : ℝ) ≤ 1)
    (θ : ℝ) : Continuous (contourCrossValueFeatureCLM (γ := γ) θ) := by
  have he := (continuous_contourC1Eval_operator hγ hγ1).clm_comp
    (continuous_const (y := ContinuousLinearMap.snd ℝ (ContourC1Space γ) (ContourC1Space γ)))
  have hd := (continuous_contourC1DerivativeEval_operator hγ).clm_comp
    (continuous_const (y := ContinuousLinearMap.snd ℝ (ContourC1Space γ) (ContourC1Space γ)))
  exact (ContinuousLinearMap.prodₗᵢ ℝ).continuous.comp ((continuous_const.sub he).prodMk hd)

def contourCrossValueNonlinearity (q : ℂ × ℂ) : ℂ := Real.log ‖q.1‖ • q.2

theorem contDiffOn_contourCrossValueNonlinearity :
    ContDiffOn ℝ ∞ contourCrossValueNonlinearity {q : ℂ × ℂ | q.1 ≠ 0} := by
  intro q hq
  exact (((contDiffAt_fst.norm ℂ hq).log (norm_ne_zero_iff.mpr hq)).smul
    contDiffAt_snd).contDiffWithinAt

theorem contourCrossValueNonlinearity_eq (p : ContourC1Space γ × ContourC1Space γ)
    (θ t : ℝ) :
    contourCrossValueNonlinearity (contourCrossValueFeatureCLM θ t p) =
      contourCrossLogIntegrand (ContourC1Space.lift γ p.1) (ContourC1Space.lift γ p.2)
        (deriv (ContourC1Space.lift γ p.2)) θ t := by
  rw [contourCrossValueFeatureCLM_apply]
  rfl

theorem contDiffOn_contourC1CrossLogIntegral_fixed (hγ : 0 < (γ : ℝ)) (hγ1 : (γ : ℝ) ≤ 1)
    (θ : ℝ) :
    ContDiffOn ℝ ∞ (fun p : ContourC1Space γ × ContourC1Space γ => contourC1CrossLogIntegral p.1 p.2 θ)
      {p : ContourC1Space γ × ContourC1Space γ | ∃ σ > 0, ContourCrossSeparated p.1 p.2 σ} := by
  let U : Set (ContourC1Space γ × ContourC1Space γ) :=
    {p | ∃ σ > 0, ContourCrossSeparated p.1 p.2 σ}
  let W : Set (ℂ × ℂ) := {q | q.1 ≠ 0}
  have hW : IsOpen W := isOpen_ne_fun continuous_fst continuous_const
  have himage (p : ContourC1Space γ × ContourC1Space γ) (hp : p ∈ U)
      (t : ℝ) (_ht : t ∈ Icc (-Real.pi) Real.pi) : contourCrossValueFeatureCLM θ t p ∈ W := by
    obtain ⟨σ, hσ, hsep⟩ := hp
    rw [contourCrossValueFeatureCLM_apply]
    exact norm_pos_iff.mp (hσ.trans_le (hsep (θ : ContourCircle) (t : ContourCircle)))
  have hi := contDiffOn_weightedIntegral_compactLinearFamily isCompact_Icc
    (integrableOn_const isCompact_Icc.measure_ne_top (C := (1 : ℝ)))
    (isOpen_positiveSeparatedContourPairs γ) hW
    (contourCrossValueFeatureCLM (γ := γ) θ) (fun _ => ContinuousLinearMap.id ℝ ℂ)
    contourCrossValueNonlinearity
    (continuous_contourCrossValueFeatureCLM hγ hγ1 θ).continuousOn
    continuous_const.continuousOn contDiffOn_contourCrossValueNonlinearity himage
  have heq : (fun p : ContourC1Space γ × ContourC1Space γ =>
      ∫ t in Icc (-Real.pi) Real.pi,
        (1 : ℝ) • (ContinuousLinearMap.id ℝ ℂ)
          (contourCrossValueNonlinearity (contourCrossValueFeatureCLM θ t p))) =
      (fun p => contourC1CrossLogIntegral p.1 p.2 θ) := by
    funext p
    apply integral_congr_ae
    filter_upwards [] with t
    simpa only [ContinuousLinearMap.id_apply, one_smul] using
      contourCrossValueNonlinearity_eq p θ t
  rw [heq] at hi
  exact hi

end Euler2D

end
