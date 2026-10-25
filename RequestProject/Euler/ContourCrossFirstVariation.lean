module

public import RequestProject.Euler.ContourCompactFirstVariation
public import RequestProject.Euler.ContourCrossLogValueSmoothness

/-! The actual Fréchet derivative of the separated cross-log integral.
Both motions of the evaluation point and source boundary, including the
variation of the source derivative, appear in the proved formula. -/

@[expose] public section

noncomputable section

open Set Filter Topology MeasureTheory
open scoped NNReal ContDiff

namespace Euler2D

local instance (priority := 2000) crossVariationC1_group (γ : ℝ≥0) :
    NormedAddCommGroup (ContourC1Space γ) := Submodule.normedAddCommGroup (contourC1GraphSubmodule γ)
local instance (priority := 2000) crossVariationC1_space (γ : ℝ≥0) :
    NormedSpace ℝ (ContourC1Space γ) := Submodule.normedSpace (contourC1GraphSubmodule γ)

set_option maxHeartbeats 600000 in
theorem fderiv_contourC1CrossLogIntegral_fixed_apply {γ : ℝ≥0}
    (hγ : 0 < (γ : ℝ)) (hγ1 : (γ : ℝ) ≤ 1) (θ : ℝ)
    (Z H : ContourC1Space γ × ContourC1Space γ)
    (hZ : ∃ σ > 0, ContourCrossSeparated Z.1 Z.2 σ) :
    fderiv ℝ (fun p : ContourC1Space γ × ContourC1Space γ => contourC1CrossLogIntegral p.1 p.2 θ) Z H =
      ∫ φ in Icc (-Real.pi) Real.pi,
        ((ContourC1Space.lift γ H.1 θ - ContourC1Space.lift γ H.2 φ) /
          (ContourC1Space.lift γ Z.1 θ - ContourC1Space.lift γ Z.2 φ)).re •
            deriv (ContourC1Space.lift γ Z.2) φ +
        Real.log ‖ContourC1Space.lift γ Z.1 θ - ContourC1Space.lift γ Z.2 φ‖ •
          deriv (ContourC1Space.lift γ H.2) φ := by
  let U : Set (ContourC1Space γ × ContourC1Space γ) :=
    {p | ∃ σ > 0, ContourCrossSeparated p.1 p.2 σ}
  let W : Set (ℂ × ℂ) := {q | q.1 ≠ 0}
  let L := contourCrossValueFeatureCLM (γ := γ) θ
  have hW : IsOpen W := isOpen_ne_fun continuous_fst continuous_const
  have hL : ContinuousOn L (Icc (-Real.pi) Real.pi) :=
    (continuous_contourCrossValueFeatureCLM hγ hγ1 θ).continuousOn
  have himage (p : ContourC1Space γ × ContourC1Space γ) (hp : p ∈ U)
      (φ : ℝ) (_hφ : φ ∈ Icc (-Real.pi) Real.pi) : L φ p ∈ W := by
    obtain ⟨σ, hσ, hsep⟩ := hp
    change (L φ p).1 ≠ 0
    rw [contourCrossValueFeatureCLM_apply]
    exact norm_pos_iff.mp (hσ.trans_le (hsep (θ : ContourCircle) (φ : ContourCircle)))
  have heq : (fun p : ContourC1Space γ × ContourC1Space γ =>
      ∫ φ in Icc (-Real.pi) Real.pi,
        (1 : ℝ) • (ContinuousLinearMap.id ℝ ℂ) (contourSelfLogFiniteKernel (L φ p))) =
      (fun p => contourC1CrossLogIntegral p.1 p.2 θ) := by
    funext p
    apply integral_congr_ae
    filter_upwards [] with φ
    simp only [one_smul, ContinuousLinearMap.id_apply]
    rw [contourCrossValueFeatureCLM_apply]
    rfl
  have hd := fderiv_weightedIntegral_compactLinearFamily_apply isCompact_Icc
    (w := fun _ : ℝ => 1) (integrableOn_const isCompact_Icc.measure_ne_top)
    (isOpen_positiveSeparatedContourPairs γ) hW L (fun _ => ContinuousLinearMap.id ℝ ℂ)
    contourSelfLogFiniteKernel hL continuousOn_const
    (contDiffOn_contourSelfLogFiniteKernel.of_le (by simp)) himage hZ H
  rw [heq] at hd
  rw [hd]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Icc] with φ hφ
  rw [one_smul, ContinuousLinearMap.id_apply,
    fderiv_contourSelfLogFiniteKernel_apply (L φ Z) (L φ H) (himage Z hZ φ hφ),
    contourCrossValueFeatureCLM_apply, contourCrossValueFeatureCLM_apply]

end Euler2D

end
