module

public import RequestProject.Euler.CircularActualCanonicalSectionMatching
public import RequestProject.Euler.CircularPeriodRotationCovariance

/-! One constant material and rotation alignment for the entire
handoff to the original ancient arc. It preserves the actual contour
field and forcing norm, and transports the section error exactly. -/

@[expose] public section

set_option maxHeartbeats 16000000
set_option maxRecDepth 6000

noncomputable section

open Set Filter Topology Metric
open scoped NNReal ContDiff

namespace Euler2D

attribute [local instance 2000] quadraticReferenceC1_group localGraphLittle_group localGraphLittle_space
  localGraphFamily_tower localGraphTangent_group localGraphTangent_space
  localGraphTangent_complete localGraphTangent_continuousAdd

theorem circularCoRotationCLM_mem_domain {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1) (t : ℝ)
    {Z : Fin 2 → LittleContourSpace γ} (hZ : Z ∈ circularBanachDomain hγ hγ1) :
    circularCoRotationCLM γ t Z ∈ circularBanachDomain hγ hγ1 :=
  circularBanachDomain_parameterShift hγ hγ1 _ hZ

theorem circularBanachField_coRotationCLM {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1) (t : ℝ)
    {Z : Fin 2 → LittleContourSpace γ} (hZ : Z ∈ circularBanachDomain hγ hγ1) :
    circularBanachField hγ hγ1 (circularCoRotationCLM γ t Z) =
      circularCoRotationCLM γ t (circularBanachField hγ hγ1 Z) :=
  circularBanachField_parameterShift hγ hγ1 _ hZ

def circularCanonicalHandoffAlignmentCLM (γ : ℝ≥0) (s b exit : ℝ) :
    (Fin 2 → LittleContourSpace γ) →L[ℝ] (Fin 2 → LittleContourSpace γ) :=
  (circularCoRotationCLM γ (-s)).comp
    ((contourRotationFamilyLittleCLM γ (-b)).comp (circularCoRotationCLM γ exit))

theorem norm_circularCanonicalHandoffAlignmentCLM {γ : ℝ≥0} (s b exit : ℝ)
    (Z : Fin 2 → LittleContourSpace γ) :
    ‖circularCanonicalHandoffAlignmentCLM γ s b exit Z‖ = ‖Z‖ := by
  unfold circularCanonicalHandoffAlignmentCLM
  simp only [ContinuousLinearMap.comp_apply, norm_circularCoRotationCLM,
    norm_contourRotationFamilyLittleCLM]

theorem circularCanonicalHandoffAlignment_section_error {γ : ℝ≥0} (s b exit : ℝ)
    (Z A : Fin 2 → LittleContourSpace γ) :
    ‖circularCanonicalHandoffAlignmentCLM γ s b exit Z - A‖ =
      ‖circularCoRotationCLM γ exit Z -
        contourRotationFamilyLittleCLM γ b (circularCoRotationCLM γ s A)‖ := by
  let S := circularCoRotationCLM γ (-s)
  let R := contourRotationFamilyLittleCLM (ι := Fin 2) γ (-b)
  have hrot (W : Fin 2 → LittleContourSpace γ) :
      R (contourRotationFamilyLittleCLM γ b W) = W := by
    funext i
    change contourRotationLittleCLM γ (-b) (contourRotationLittleCLM γ b (W i)) = W i
    rw [contourRotationLittleCLM_add, neg_add_cancel, contourRotationLittleCLM_zero]
  have htarget : S (R (contourRotationFamilyLittleCLM γ b (circularCoRotationCLM γ s A))) = A := by
    rw [hrot]
    change circularCoRotationCLM γ (-s) (circularCoRotationCLM γ s A) = A
    rw [circularCoRotationCLM_add, neg_add_cancel, circularCoRotationCLM_zero]
  change ‖S (R (circularCoRotationCLM γ exit Z)) - A‖ = _
  conv_lhs => rw [← htarget]
  rw [← S.map_sub, ← R.map_sub]
  exact (norm_circularCoRotationCLM (-s) _).trans (norm_contourRotationFamilyLittleCLM (-b) _)

attribute [local irreducible] circularBanachField circularBanachDomain circularCoRotationCLM
  circularCanonicalHandoffAlignmentCLM contourC1GraphSubmodule holderGraphSubmodule

theorem circularCanonicalHandoffAlignment_mem_domain {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1) (s b exit : ℝ)
    {Z : Fin 2 → LittleContourSpace γ} (hZ : Z ∈ circularBanachDomain hγ hγ1) :
    circularCanonicalHandoffAlignmentCLM γ s b exit Z ∈ circularBanachDomain hγ hγ1 := by
  unfold circularCanonicalHandoffAlignmentCLM
  exact circularCoRotationCLM_mem_domain hγ hγ1 (-s)
    (circularBanachDomain_rotation hγ hγ1 (-b) (circularCoRotationCLM_mem_domain hγ hγ1 exit hZ))

theorem circularBanachField_canonicalHandoffAlignment {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1) (s b exit : ℝ)
    {Z : Fin 2 → LittleContourSpace γ} (hZ : Z ∈ circularBanachDomain hγ hγ1) :
    circularBanachField hγ hγ1 (circularCanonicalHandoffAlignmentCLM γ s b exit Z) =
      circularCanonicalHandoffAlignmentCLM γ s b exit (circularBanachField hγ hγ1 Z) := by
  unfold circularCanonicalHandoffAlignmentCLM
  simp only [ContinuousLinearMap.comp_apply]
  rw [circularBanachField_coRotationCLM hγ hγ1 (-s)
    (circularBanachDomain_rotation hγ hγ1 (-b) (circularCoRotationCLM_mem_domain hγ hγ1 exit hZ)),
    circularBanachField_rotation hγ hγ1 (-b) (circularCoRotationCLM_mem_domain hγ hγ1 exit hZ),
    circularBanachField_coRotationCLM hγ hγ1 exit hZ]

theorem hasDerivAt_circularCanonicalHandoffAlignment_forced {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1) (s b exit t : ℝ)
    {y : ℝ → Fin 2 → LittleContourSpace γ} {p : Fin 2 → LittleContourSpace γ}
    (hm : y t ∈ circularBanachDomain hγ hγ1)
    (hd : HasDerivAt y (circularBanachField hγ hγ1 (y t) + p) t) :
    HasDerivAt (fun u => circularCanonicalHandoffAlignmentCLM γ s b exit (y u))
      (circularBanachField hγ hγ1 (circularCanonicalHandoffAlignmentCLM γ s b exit (y t)) +
        circularCanonicalHandoffAlignmentCLM γ s b exit p) t ∧
      ‖circularCanonicalHandoffAlignmentCLM γ s b exit p‖ = ‖p‖ := by
  let G := circularCanonicalHandoffAlignmentCLM γ s b exit
  have hh := G.hasFDerivAt.comp_hasDerivAt t hd
  change HasDerivAt (fun u => G (y u)) (G (circularBanachField hγ hγ1 (y t) + p)) t at hh
  rw [G.map_add, ← circularBanachField_canonicalHandoffAlignment hγ hγ1 s b exit hm] at hh
  exact ⟨hh, norm_circularCanonicalHandoffAlignmentCLM s b exit p⟩

end Euler2D

end
