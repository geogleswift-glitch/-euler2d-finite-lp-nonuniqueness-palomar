module

public import RequestProject.Euler.ContourCauchyShapeContinuity
public import RequestProject.Euler.ContourNearCircleSelfLog

/-! Genuine Hölder continuity of the spatial derivative, and genuine
C¹ Hölder continuity of the original logarithmic self-interaction. -/

@[expose] public section

noncomputable section

open Set Filter Topology
open scoped NNReal ComplexConjugate

namespace Euler2D

local instance (priority := 2000) logStrongC1_normedAddCommGroup (γ : ℝ≥0) :
    NormedAddCommGroup (ContourC1Space γ) :=
  Submodule.normedAddCommGroup (contourC1GraphSubmodule γ)

local instance (priority := 2000) logStrongC1_normedSpace (γ : ℝ≥0) :
    NormedSpace ℝ (ContourC1Space γ) :=
  Submodule.normedSpace (contourC1GraphSubmodule γ)

theorem continuous_positiveContourLogDerivativeHolder {γ : ℝ≥0}
    (hγ : 0 < (γ : ℝ)) (hγ1 : (γ : ℝ) < 1) :
    Continuous (positiveContourLogDerivativeHolder hγ hγ1) := by
  have hd : Continuous (fun Z : PositiveChordContour γ =>
      HolderFunctionSpace.conjugate (ContourC1Space.derivative γ Z.val)) :=
    (HolderFunctionSpace.conjugateCLM γ).continuous.comp
      ((ContourC1Space.derivative γ).continuous.comp continuous_subtype_val)
  have hi : Continuous (fun Z : PositiveChordContour γ =>
      HolderFunctionSpace.conjugate
        (contourCauchyIncrementOperatorOnLocus hγ hγ1 Z (positiveContourDerivativePhase Z))) :=
    (HolderFunctionSpace.conjugateCLM γ).continuous.comp
      ((continuous_contourCauchyIncrementOperatorOnLocus hγ hγ1).clm_apply
        (continuous_positiveContourDerivativePhase γ))
  have hmul : Continuous (fun p : ContourHolderSpace γ × ContourHolderSpace γ =>
      HolderFunctionSpace.pointwiseMul p.1 p.2) := by
    have hm := (HolderFunctionSpace.pointwiseMulCLM (X := ContourCircle) γ).continuous₂
    exact hm.congr (fun _ => rfl)
  have hm : Continuous (fun Z : PositiveChordContour γ =>
      HolderFunctionSpace.pointwiseMul
        (HolderFunctionSpace.conjugate (ContourC1Space.derivative γ Z.val))
        (HolderFunctionSpace.conjugate
          (contourCauchyIncrementOperatorOnLocus hγ hγ1 Z (positiveContourDerivativePhase Z)))) := by
    have hpair := hd.prodMk hi
    have hcomp := hmul.comp hpair
    exact hcomp.congr (fun _ => rfl)
  exact (hm.const_smul (1 / 2 : ℝ)).congr (fun _ => rfl)

theorem continuous_nearCircleSelfLogC1 {γ : ℝ≥0}
    (hγ : 0 < (γ : ℝ)) (hγ1 : (γ : ℝ) < 1) (Z₀ : ContourC1Space γ)
    {r : ℝ} (hr : 0 < r) (href : ContourC1Space.lift γ Z₀ = refCircle r) :
    Continuous (nearCircleSelfLogC1 hγ hγ1 Z₀ hr href) := by
  have hp := continuous_nearCirclePositiveContour Z₀ hr href
  have hf := ContourC1Space.continuous_selfLogCircleBCF.comp hp
  have hd := (continuous_positiveContourLogDerivativeHolder hγ hγ1).comp hp
  exact (hf.prodMk hd).subtype_mk _

end Euler2D

end
