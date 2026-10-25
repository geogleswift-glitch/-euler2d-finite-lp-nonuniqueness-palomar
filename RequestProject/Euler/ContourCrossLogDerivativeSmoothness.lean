module

public import RequestProject.Euler.ContourCrossLogLinearFamily
public import RequestProject.Euler.ContourCompactLinearFamilyIntegral
public import RequestProject.Euler.ContourHolderInverseAnalytic

/-! Genuine Hölder-norm smooth dependence of the cross-log derivative. -/

@[expose] public section

noncomputable section

open Set Filter Topology MeasureTheory
open scoped NNReal ContDiff

namespace Euler2D

open HolderFunctionSpace

local instance (priority := 2000) crossSmoothC1_normedAddCommGroup (γ : ℝ≥0) :
    NormedAddCommGroup (ContourC1Space γ) := Submodule.normedAddCommGroup (contourC1GraphSubmodule γ)

local instance (priority := 2000) crossSmoothC1_normedSpace (γ : ℝ≥0) :
    NormedSpace ℝ (ContourC1Space γ) := Submodule.normedSpace (contourC1GraphSubmodule γ)

local instance (priority := 2000) crossSmoothHolder_normedAddCommGroup (γ : ℝ≥0) :
    NormedAddCommGroup (ContourHolderSpace γ) :=
  Submodule.normedAddCommGroup (holderGraphSubmodule ContourCircle ℂ γ)

local instance (priority := 2000) crossSmoothHolder_normedSpace (γ : ℝ≥0) :
    NormedSpace ℝ (ContourHolderSpace γ) := Submodule.normedSpace (holderGraphSubmodule ContourCircle ℂ γ)

variable {γ : ℝ≥0}

def contourPositiveHolderLowerDomain (γ : ℝ≥0) : Set (ContourHolderSpace γ) :=
  {f | ∃ c > 0, ∀ x, c ≤ ‖f x‖}

theorem isOpen_contourPositiveHolderLowerDomain (γ : ℝ≥0) :
    IsOpen (contourPositiveHolderLowerDomain γ) := by
  rw [Metric.isOpen_iff]
  rintro f ⟨c, hc, hf⟩
  refine ⟨c / 2, by positivity, ?_⟩
  intro g hg
  refine ⟨c / 2, by positivity, ?_⟩
  intro x
  have hd : ‖f - g‖ < c / 2 := by
    simpa only [Metric.mem_ball, dist_eq_norm, norm_sub_rev] using hg
  have he : ‖f x - g x‖ ≤ ‖f - g‖ := HolderFunctionSpace.norm_eval_le (f - g) x
  have hn := norm_sub_norm_le (f x) (g x)
  linarith [hf x]

def contourCrossDerivativeNonlinearity (γ : ℝ≥0)
    (q : ContourCrossDerivativeFeatures γ) : ContourHolderSpace γ :=
  pointwiseMul (contourHolderRealPart (pointwiseMul q.2.1 (reciprocal γ q.1)))
    (contourHolderConstantCLM γ q.2.2)

set_option maxHeartbeats 1000000 in
theorem contDiffAt_contourCrossDerivativeNonlinearity
    (q : ContourCrossDerivativeFeatures γ) (hq : q.1 ∈ contourPositiveHolderLowerDomain γ) :
    ContDiffAt ℝ ∞ (contourCrossDerivativeNonlinearity γ) q := by
  obtain ⟨c, hc, hf⟩ := hq
  have hm : ContDiff ℝ ∞ (fun p : ContourHolderSpace γ × ContourHolderSpace γ =>
      pointwiseMul p.1 p.2) := (pointwiseMulCLM (X := ContourCircle) γ).isBoundedBilinearMap.contDiff
  have hi : ContDiffAt ℝ ∞ (fun p : ContourCrossDerivativeFeatures γ => reciprocal γ p.1) q :=
    (contDiffAt_reciprocal q.1 hc hf ∞).comp q contDiffAt_fst
  have hprod : ContDiffAt ℝ ∞ (fun p : ContourCrossDerivativeFeatures γ =>
      pointwiseMul p.2.1 (reciprocal γ p.1)) q :=
    hm.contDiffAt.comp q (contDiffAt_snd.fst.prodMk hi)
  have hre : ContDiffAt ℝ ∞ (fun p : ContourCrossDerivativeFeatures γ =>
      contourHolderRealPart (pointwiseMul p.2.1 (reciprocal γ p.1))) q :=
    (contourHolderRealPartCLM γ).contDiff.contDiffAt.comp q hprod
  have hconst : ContDiffAt ℝ ∞ (fun p : ContourCrossDerivativeFeatures γ =>
      contourHolderConstantCLM γ p.2.2) q :=
    (contourHolderConstantCLM γ).contDiff.contDiffAt.comp q contDiffAt_snd.snd
  exact hm.contDiffAt.comp q (hre.prodMk hconst)

theorem contourCrossDerivativeNonlinearity_eq (hγ1 : (γ : ℝ) ≤ 1)
    (Z W : ContourC1Space γ) {σ : ℝ} (hσ : 0 < σ)
    (hsep : ContourCrossSeparated Z W σ) (t : ℝ) :
    contourCrossDerivativeNonlinearity γ (contourCrossDerivativeFeatureCLM hγ1 t (Z, W)) =
      contourCrossDerivativeKernelHolder hγ1 Z W hσ hsep t := by
  rw [contourCrossDerivativeFeatureCLM_apply]
  unfold contourCrossDerivativeNonlinearity
  rw [reciprocal_eq_inverseOfNormLower _ hσ
    (norm_contourCrossDenominatorHolder_lower hγ1 Z W hsep t)]
  rfl

def contourCrossLogDerivativeShape (hγ1 : (γ : ℝ) ≤ 1)
    (p : ContourC1Space γ × ContourC1Space γ) : ContourHolderSpace γ :=
  ∫ t in Icc (-Real.pi) Real.pi,
    contourCrossDerivativeNonlinearity γ (contourCrossDerivativeFeatureCLM hγ1 t p)

theorem contourCrossLogDerivativeShape_eq (hγ1 : (γ : ℝ) ≤ 1)
    (Z W : ContourC1Space γ) {σ : ℝ} (hσ : 0 < σ)
    (hsep : ContourCrossSeparated Z W σ) :
    contourCrossLogDerivativeShape hγ1 (Z, W) = contourCrossLogDerivativeHolder hγ1 Z W hσ hsep := by
  apply integral_congr_ae
  filter_upwards [] with t
  exact contourCrossDerivativeNonlinearity_eq hγ1 Z W hσ hsep t

theorem contDiffOn_contourCrossLogDerivativeShape (hγ : 0 < (γ : ℝ)) (hγ1 : (γ : ℝ) ≤ 1) :
    ContDiffOn ℝ ∞ (contourCrossLogDerivativeShape hγ1)
      {p : ContourC1Space γ × ContourC1Space γ | ∃ σ > 0, ContourCrossSeparated p.1 p.2 σ} := by
  let V := ContourCrossDerivativeFeatures γ
  let U : Set (ContourC1Space γ × ContourC1Space γ) :=
    {p | ∃ σ > 0, ContourCrossSeparated p.1 p.2 σ}
  let W : Set V := Prod.fst ⁻¹' contourPositiveHolderLowerDomain γ
  have hW : IsOpen W := (isOpen_contourPositiveHolderLowerDomain γ).preimage continuous_fst
  have hψ : ContDiffOn ℝ ∞ (contourCrossDerivativeNonlinearity γ) W :=
    fun q hq => (contDiffAt_contourCrossDerivativeNonlinearity q hq).contDiffWithinAt
  have himage (p : ContourC1Space γ × ContourC1Space γ) (hp : p ∈ U)
      (t : ℝ) (_ht : t ∈ Icc (-Real.pi) Real.pi) :
      contourCrossDerivativeFeatureCLM hγ1 t p ∈ W := by
    obtain ⟨σ, hσ, hsep⟩ := hp
    rw [contourCrossDerivativeFeatureCLM_apply]
    exact ⟨σ, hσ, norm_contourCrossDenominatorHolder_lower hγ1 p.1 p.2 hsep t⟩
  have hi := contDiffOn_weightedIntegral_compactLinearFamily isCompact_Icc
    (integrableOn_const isCompact_Icc.measure_ne_top (C := (1 : ℝ)))
    (isOpen_positiveSeparatedContourPairs γ) hW
    (contourCrossDerivativeFeatureCLM hγ1)
    (fun _ => ContinuousLinearMap.id ℝ (ContourHolderSpace γ))
    (contourCrossDerivativeNonlinearity γ)
    (continuous_contourCrossDerivativeFeatureCLM hγ hγ1).continuousOn
    continuous_const.continuousOn hψ himage
  simpa only [ContinuousLinearMap.id_apply, one_smul] using hi

end Euler2D

end
