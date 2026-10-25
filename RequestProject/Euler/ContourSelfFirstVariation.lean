module

public import RequestProject.Euler.ContourCompactFirstVariation

/-! The first variation of the original singular self-log integral.
The diagonal is treated through the actual normalized chord and the
fixed integrable logarithmic weight; no differentiation at a pole occurs. -/

@[expose] public section

noncomputable section

open Set Filter Topology MeasureTheory
open scoped NNReal ContDiff

namespace Euler2D

local instance (priority := 2000) selfVariationC1_group (γ : ℝ≥0) :
    NormedAddCommGroup (ContourC1Space γ) := Submodule.normedAddCommGroup (contourC1GraphSubmodule γ)
local instance (priority := 2000) selfVariationC1_space (γ : ℝ≥0) :
    NormedSpace ℝ (ContourC1Space γ) := Submodule.normedSpace (contourC1GraphSubmodule γ)

set_option maxHeartbeats 800000 in
theorem fderiv_selfLogIntegral_fixed_normalized {γ : ℝ≥0}
    (hγ : 0 < (γ : ℝ)) (θ : ℝ) (Z H : ContourC1Space γ)
    (hZ : ContourC1Space.HasPositiveChordArc Z) :
    fderiv ℝ (fun W : ContourC1Space γ => ContourC1Space.selfLogIntegral W θ) Z H =
      (∫ τ in Icc (-Real.pi) Real.pi, Real.log τ • deriv (ContourC1Space.lift γ H) (θ + τ)) +
      ∫ τ in Icc (-Real.pi) Real.pi,
        ((contourSelfLogLinearFamily hγ θ τ H).1 /
          (contourSelfLogLinearFamily hγ θ τ Z).1).re •
            deriv (ContourC1Space.lift γ Z) (θ + τ) +
        Real.log ‖(contourSelfLogLinearFamily hγ θ τ Z).1‖ •
          deriv (ContourC1Space.lift γ H) (θ + τ) := by
  let S : Set ℝ := Icc (-Real.pi) Real.pi
  let U : Set (ContourC1Space γ) := {W | ContourC1Space.HasPositiveChordArc W}
  let V : Set (ℂ × ℂ) := {q | q.1 ≠ 0}
  let L := contourSelfLogLinearFamily hγ θ
  have hU : IsOpen U := ContourC1Space.isOpen_hasPositiveChordArc γ
  have hV : IsOpen V := isOpen_ne_fun continuous_fst continuous_const
  have hL : ContinuousOn L S := (continuous_contourSelfLogLinearFamily hγ θ).continuousOn
  have hab : (-Real.pi : ℝ) ≤ Real.pi := by linarith [Real.pi_pos]
  have hw : IntegrableOn Real.log S :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mp intervalIntegral.intervalIntegrable_log'
  have himage (W : ContourC1Space γ) (hW : W ∈ U) (τ : ℝ) (hτ : τ ∈ S) : L τ W ∈ V := by
    obtain ⟨c, hc, hW⟩ := hW
    change (L τ W).1 ≠ 0
    rw [contourSelfLogLinearFamily_coe hγ θ τ (abs_le.mpr hτ)]
    exact neg_ne_zero.mpr (smoothContourNormalizedChord_ne_zero
      (ContourC1Space.contDiff_lift W) hc hW θ τ (abs_le.mpr hτ))
  have hD₁ := hasFDerivAt_weightedIntegral_compactLinearFamily isCompact_Icc hw hU isOpen_univ L
    (fun _ => ContinuousLinearMap.id ℝ ℂ) (fun q : ℂ × ℂ => q.2)
    hL continuousOn_const contDiff_snd.contDiffOn (fun _ _ _ _ => mem_univ _) hZ
  change HasFDerivAt (fun W : ContourC1Space γ => ∫ τ in S, Real.log τ • (L τ W).2) _ Z at hD₁
  have hD₂ := hasFDerivAt_weightedIntegral_compactLinearFamily isCompact_Icc
    (w := fun _ : ℝ => 1) (integrableOn_const isCompact_Icc.measure_ne_top)
    hU hV L (fun _ => ContinuousLinearMap.id ℝ ℂ) contourSelfLogFiniteKernel hL continuousOn_const
    (contDiffOn_contourSelfLogFiniteKernel.of_le (by simp)) himage hZ
  have he₂ : (fun W : ContourC1Space γ => ∫ τ in S,
      (1 : ℝ) • (ContinuousLinearMap.id ℝ ℂ) (contourSelfLogFiniteKernel (L τ W))) =
      (fun W => ∫ τ in S, contourSelfLogFiniteKernel (L τ W)) := by
    funext W
    simp only [one_smul, ContinuousLinearMap.id_apply]
  rw [he₂] at hD₂
  have he : (fun W : ContourC1Space γ => ContourC1Space.selfLogIntegral W θ) =ᶠ[𝓝 Z]
      contourSelfLogBasePresentation hγ θ := by
    filter_upwards [hU.mem_nhds hZ] with W hW
    obtain ⟨c, hc, hW⟩ := hW
    exact selfLogIntegral_eq_contourSelfLogBasePresentation hγ W hc hW θ
  rw [he.fderiv_eq]
  change fderiv ℝ (fun W : ContourC1Space γ =>
    (∫ τ in S, Real.log τ • (L τ W).2) +
      ∫ τ in S, contourSelfLogFiniteKernel (L τ W)) Z H = _
  rw [fderiv_fun_add hD₁.differentiableAt hD₂.differentiableAt, ContinuousLinearMap.add_apply]
  have hd₁ := fderiv_weightedIntegral_compactLinearFamily_apply isCompact_Icc hw hU isOpen_univ L
    (fun _ => ContinuousLinearMap.id ℝ ℂ) (fun q : ℂ × ℂ => q.2)
    hL continuousOn_const contDiff_snd.contDiffOn (fun _ _ _ _ => mem_univ _) hZ H
  simp only [ContinuousLinearMap.id_apply] at hd₁
  have hd₂ := fderiv_weightedIntegral_compactLinearFamily_apply isCompact_Icc
    (w := fun _ : ℝ => 1) (integrableOn_const isCompact_Icc.measure_ne_top)
    hU hV L (fun _ => ContinuousLinearMap.id ℝ ℂ) contourSelfLogFiniteKernel hL continuousOn_const
    (contDiffOn_contourSelfLogFiniteKernel.of_le (by simp)) himage hZ H
  rw [he₂] at hd₂
  rw [hd₁, hd₂]
  apply congrArg₂ (fun a b : ℂ => a + b)
  · apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Icc] with τ hτ
    rw [fderiv_snd]
    change Real.log τ • (L τ H).2 = _
    rw [contourSelfLogLinearFamily_coe hγ θ τ (abs_le.mpr hτ)]
  · apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Icc] with τ hτ
    rw [one_smul, ContinuousLinearMap.id_apply,
      fderiv_contourSelfLogFiniteKernel_apply (L τ Z) (L τ H) (himage Z hZ τ hτ)]
    rw [contourSelfLogLinearFamily_coe hγ θ τ (abs_le.mpr hτ),
      contourSelfLogLinearFamily_coe hγ θ τ (abs_le.mpr hτ)]

end Euler2D

end
