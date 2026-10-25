module

public import RequestProject.Euler.FiniteContourPhaseField
public import RequestProject.Euler.FiniteContourFirstVariation

/-! The derivative of the actual phase field is the conjugate of the
actual near-circle derivative. This identifies the linearization along
every reference phase with the proved self and cross first variations. -/

@[expose] public section

noncomputable section

open Set Filter Topology
open scoped NNReal ContDiff

namespace Euler2D

local instance (priority := 2000) phaseVariationC1_group (γ : ℝ≥0) :
    NormedAddCommGroup (ContourC1Space γ) := Submodule.normedAddCommGroup (contourC1GraphSubmodule γ)
local instance (priority := 2000) phaseVariationLittle_group (γ : ℝ≥0) :
    NormedAddCommGroup (LittleContourSpace γ) := Submodule.normedAddCommGroup (LittleContourSpace γ)
local instance (priority := 2000) phaseVariationLittle_space (γ : ℝ≥0) :
    NormedSpace ℝ (LittleContourSpace γ) := Submodule.normedSpace (LittleContourSpace γ)

set_option maxHeartbeats 800000 in
theorem fderiv_finiteContourPhaseFieldTotal_conjugate {γ : ℝ≥0} {ι : Type} [Fintype ι]
    (hγ : 0 < (γ : ℝ)) (hγ1 : (γ : ℝ) < 1)
    (Z₀ : ι → ContourC1Space γ) (r : ι → ℝ) (hr : ∀ i, 0 < r i)
    (href : ∀ i, ContourC1Space.lift γ (Z₀ i) = refCircle (r i)) (g : ι → ℝ)
    (Z : AdmissibleLittleContourFamily Z₀ r) (b : ι → ℝ) (H : ι → LittleContourSpace γ) :
    fderiv ℝ (finiteContourPhaseFieldTotal hγ hγ1 Z₀ r hr href g)
        (contourParameterShiftFamilyCLM γ b Z.val) (contourParameterShiftFamilyCLM γ b H) =
      contourParameterShiftFamilyCLM γ b
        (fderiv ℝ (finiteContourMaterialFieldTotal hγ hγ1 Z₀ r hr href g) Z.val H) := by
  let Q := contourParameterShiftFamilyCLM γ b Z.val
  have hinv : contourParameterShiftFamilyCLM γ (-b) Q = Z.val := by
    dsimp only [Q]
    rw [contourParameterShiftFamilyCLM_add, neg_add_cancel, contourParameterShiftFamilyCLM_zero]
  have hQ : IsAdmissibleLittleContourFamily Z₀ r (contourParameterShiftFamilyCLM γ (-b) Q) := by
    rw [hinv]
    exact Z.property
  have he : finiteContourPhaseFieldTotal hγ hγ1 Z₀ r hr href g =ᶠ[𝓝 Q]
      finiteContourPhaseFieldChart hγ hγ1 Z₀ r hr href g b := by
    filter_upwards [(isOpen_contourPhaseChart Z₀ r b).mem_nhds hQ] with W hW
    exact finiteContourPhaseFieldTotal_eq_chart hγ hγ1 Z₀ r hr href g b W hW
  have hf : HasFDerivAt (finiteContourMaterialFieldTotal hγ hγ1 Z₀ r hr href g)
      (fderiv ℝ (finiteContourMaterialFieldTotal hγ hγ1 Z₀ r hr href g)
        (contourParameterShiftFamilyCLM γ (-b) Q)) (contourParameterShiftFamilyCLM γ (-b) Q) :=
    ((contDiffAt_finiteContourMaterialFieldTotal hγ hγ1 Z₀ r hr href g
      ⟨contourParameterShiftFamilyCLM γ (-b) Q, hQ⟩ 1).differentiableAt (by simp)).hasFDerivAt
  have hi : HasFDerivAt
      (fun W => finiteContourMaterialFieldTotal hγ hγ1 Z₀ r hr href g
        (contourParameterShiftFamilyCLM γ (-b) W))
      ((fderiv ℝ (finiteContourMaterialFieldTotal hγ hγ1 Z₀ r hr href g)
        (contourParameterShiftFamilyCLM γ (-b) Q)).comp (contourParameterShiftFamilyCLM γ (-b))) Q :=
    hf.comp Q (contourParameterShiftFamilyCLM γ (-b)).hasFDerivAt
  have hc : HasFDerivAt (finiteContourPhaseFieldChart hγ hγ1 Z₀ r hr href g b)
      ((contourParameterShiftFamilyCLM γ b).comp
        ((fderiv ℝ (finiteContourMaterialFieldTotal hγ hγ1 Z₀ r hr href g)
          (contourParameterShiftFamilyCLM γ (-b) Q)).comp (contourParameterShiftFamilyCLM γ (-b)))) Q :=
    (contourParameterShiftFamilyCLM γ b).hasFDerivAt.comp Q hi
  have hactual := hc.congr_of_eventuallyEq he
  have hd := congrArg (fun A : (ι → LittleContourSpace γ) →L[ℝ] (ι → LittleContourSpace γ) =>
    A (contourParameterShiftFamilyCLM γ b H)) hactual.fderiv
  simpa only [ContinuousLinearMap.comp_apply, hinv, contourParameterShiftFamilyCLM_add,
    neg_add_cancel, contourParameterShiftFamilyCLM_zero] using hd

end Euler2D

end
