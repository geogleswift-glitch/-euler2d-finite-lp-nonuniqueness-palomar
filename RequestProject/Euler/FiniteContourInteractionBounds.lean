module

public import RequestProject.Euler.FiniteContourSmoothField

/-! Quantitative bounds for the actual finite interaction operators.
The constants depend on genuine chord, separation and contour norm
bounds, without using compactness of an infinite-dimensional ball. -/

@[expose] public section

set_option maxHeartbeats 3500000

noncomputable section

open Set Filter Topology
open scoped NNReal BigOperators

namespace Euler2D

local instance (priority := 2000) finiteInteractionBoundLittle_group (γ : ℝ≥0) :
    NormedAddCommGroup (LittleContourSpace γ) := Submodule.normedAddCommGroup (LittleContourSpace γ)
local instance (priority := 2000) finiteInteractionBoundLittle_space (γ : ℝ≥0) :
    NormedSpace ℝ (LittleContourSpace γ) := Submodule.normedSpace (LittleContourSpace γ)
local instance (priority := 2000) finiteInteractionBoundC1_group (γ : ℝ≥0) :
    NormedAddCommGroup (ContourC1Space γ) := Submodule.normedAddCommGroup (contourC1GraphSubmodule γ)

theorem norm_finiteContourInteraction_sub_le {γ : ℝ≥0} {ι : Type} [Fintype ι]
    (hγ : 0 < (γ : ℝ)) (hγ1 : (γ : ℝ) < 1)
    (Z₀ : ι → ContourC1Space γ) (r : ι → ℝ) (hr : ∀ i, 0 < r i)
    (href : ∀ i, ContourC1Space.lift γ (Z₀ i) = refCircle (r i))
    (Z W : AdmissibleLittleContourFamily Z₀ r) (i j : ι)
    {c σ M : ℝ} (hc : 0 < c) (hσ : 0 < σ) (hM : 0 ≤ M)
    (hZc : ContourC1Space.HasChordArcLower (Z.val i).val c)
    (hWc : ContourC1Space.HasChordArcLower (W.val i).val c)
    (hZsep : i ≠ j → ContourCrossSeparated (Z.val i).val (Z.val j).val σ)
    (hWsep : i ≠ j → ContourCrossSeparated (W.val i).val (W.val j).val σ)
    (hZiM : ‖Z.val i‖ ≤ M) (hZjM : ‖Z.val j‖ ≤ M)
    (hWiM : ‖W.val i‖ ≤ M) (hWjM : ‖W.val j‖ ≤ M) :
    ‖finiteContourInteraction hγ hγ1 Z₀ r hr href i j Z -
        finiteContourInteraction hγ hγ1 Z₀ r hr href i j W‖ ≤
      max (contourSelfLogShapeConstant (γ : ℝ) c M)
        (2 * contourCrossLogShapeConstant (γ : ℝ) σ M) * ‖Z.val - W.val‖ := by
  classical
  have hi : ‖(Z.val i).val - (W.val i).val‖ ≤ ‖Z.val - W.val‖ :=
    norm_le_pi_norm (Z.val - W.val) i
  have hj : ‖(Z.val j).val - (W.val j).val‖ ≤ ‖Z.val - W.val‖ :=
    norm_le_pi_norm (Z.val - W.val) j
  by_cases hij : i = j
  · subst j
    simp only [finiteContourInteraction, dif_pos rfl]
    change ‖nearCircleSelfLogC1 hγ hγ1 (Z₀ i) (hr i) (href i)
        (finiteFamilyNearCircleComponent Z₀ r i Z) -
      nearCircleSelfLogC1 hγ hγ1 (Z₀ i) (hr i) (href i)
        (finiteFamilyNearCircleComponent Z₀ r i W)‖ ≤ _
    have hh := norm_nearCircleSelfLogC1_shape_sub_le hγ hγ1 (Z₀ i) (hr i) (href i)
      (finiteFamilyNearCircleComponent Z₀ r i Z) (finiteFamilyNearCircleComponent Z₀ r i W)
      hc hM hZc hWc hZiM hWiM
    exact hh.trans ((mul_le_mul_of_nonneg_left hi
      (contourSelfLogShapeConstant_nonneg hγ hγ1 hc hM)).trans
        (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)))
  · let pZ := finiteFamilySeparatedPair Z₀ r i j hij Z
    let pW := finiteFamilySeparatedPair Z₀ r i j hij W
    simp only [finiteContourInteraction, dif_neg hij]
    change ‖contourCrossLogC1OnLocus hγ1.le (separatedLittlePairToC1 pZ) -
      contourCrossLogC1OnLocus hγ1.le (separatedLittlePairToC1 pW)‖ ≤ _
    rw [contourCrossLogC1OnLocus_eq hγ1.le _ hσ (hZsep hij),
      contourCrossLogC1OnLocus_eq hγ1.le _ hσ (hWsep hij)]
    have hh := norm_contourCrossLogC1_shape_sub_le hγ1.le
      (Z.val i).val (Z.val j).val (W.val i).val (W.val j).val hσ (hZsep hij) (hWsep hij)
      hM hZiM hZjM hWiM hWjM
    have hC := contourCrossLogShapeConstant_nonneg (γ := (γ : ℝ)) hσ hM
    calc
      _ ≤ contourCrossLogShapeConstant (γ : ℝ) σ M *
          (‖(Z.val i).val - (W.val i).val‖ + ‖(Z.val j).val - (W.val j).val‖) := hh
      _ ≤ contourCrossLogShapeConstant (γ : ℝ) σ M * (2 * ‖Z.val - W.val‖) :=
        mul_le_mul_of_nonneg_left (by linarith) hC
      _ = (2 * contourCrossLogShapeConstant (γ : ℝ) σ M) * ‖Z.val - W.val‖ := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _)

end Euler2D

end
