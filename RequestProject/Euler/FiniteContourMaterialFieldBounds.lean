module

public import RequestProject.Euler.FiniteContourInteractionBounds

/-! Actual finite material-field bounds from the proved quantitative
interaction estimates. Constants may depend on the finite cutoff;
their finiteness suffices for a genuine endpoint continuation. -/

@[expose] public section

set_option maxHeartbeats 3500000

noncomputable section

open Set Filter Topology
open scoped NNReal BigOperators

namespace Euler2D

local instance (priority := 2000) finiteMaterialBoundLittle_group (γ : ℝ≥0) :
    NormedAddCommGroup (LittleContourSpace γ) := Submodule.normedAddCommGroup (LittleContourSpace γ)
local instance (priority := 2000) finiteMaterialBoundLittle_space (γ : ℝ≥0) :
    NormedSpace ℝ (LittleContourSpace γ) := Submodule.normedSpace (LittleContourSpace γ)
local instance (priority := 2000) finiteMaterialBoundC1_group (γ : ℝ≥0) :
    NormedAddCommGroup (ContourC1Space γ) := Submodule.normedAddCommGroup (contourC1GraphSubmodule γ)

theorem norm_finiteContourMaterialField_sub_le {γ : ℝ≥0} {ι : Type} [Fintype ι]
    (hγ : 0 < (γ : ℝ)) (hγ1 : (γ : ℝ) < 1)
    (Z₀ : ι → ContourC1Space γ) (r : ι → ℝ) (hr : ∀ i, 0 < r i)
    (href : ∀ i, ContourC1Space.lift γ (Z₀ i) = refCircle (r i)) (g : ι → ℝ)
    (Z W : AdmissibleLittleContourFamily Z₀ r)
    {c σ M : ℝ} (hc : 0 < c) (hσ : 0 < σ) (hM : 0 ≤ M)
    (hZc : ∀ i, ContourC1Space.HasChordArcLower (Z.val i).val c)
    (hWc : ∀ i, ContourC1Space.HasChordArcLower (W.val i).val c)
    (hZsep : ∀ i j, i ≠ j → ContourCrossSeparated (Z.val i).val (Z.val j).val σ)
    (hWsep : ∀ i j, i ≠ j → ContourCrossSeparated (W.val i).val (W.val j).val σ)
    (hZM : ∀ i, ‖Z.val i‖ ≤ M) (hWM : ∀ i, ‖W.val i‖ ≤ M) :
    ‖finiteContourMaterialFieldTotal hγ hγ1 Z₀ r hr href g Z.val -
        finiteContourMaterialFieldTotal hγ hγ1 Z₀ r hr href g W.val‖ ≤
      (|-1 / (2 * Real.pi)| * (∑ j, |g j|) *
        max (contourSelfLogShapeConstant (γ : ℝ) c M)
          (2 * contourCrossLogShapeConstant (γ : ℝ) σ M)) * ‖Z.val - W.val‖ := by
  classical
  let C := max (contourSelfLogShapeConstant (γ : ℝ) c M)
    (2 * contourCrossLogShapeConstant (γ : ℝ) σ M)
  have hC : 0 ≤ C := (contourSelfLogShapeConstant_nonneg hγ hγ1 hc hM).trans (le_max_left _ _)
  have hsum : 0 ≤ ∑ j, |g j| := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have hb : 0 ≤ (|-1 / (2 * Real.pi)| * (∑ j, |g j|) * C) * ‖Z.val - W.val‖ := by
    positivity
  apply (pi_norm_le_iff_of_nonneg hb).mpr
  intro i
  rw [finiteContourMaterialFieldTotal_of_mem hγ hγ1 Z₀ r hr href g Z,
    finiteContourMaterialFieldTotal_of_mem hγ hγ1 Z₀ r hr href g W]
  change ‖(-1 / (2 * Real.pi) : ℝ) • (∑ j, g j • finiteContourInteraction hγ hγ1 Z₀ r hr href i j Z) -
    (-1 / (2 * Real.pi) : ℝ) • (∑ j, g j • finiteContourInteraction hγ hγ1 Z₀ r hr href i j W)‖ ≤ _
  rw [← smul_sub, ← Finset.sum_sub_distrib, norm_smul, Real.norm_eq_abs]
  calc
    _ ≤ |-1 / (2 * Real.pi)| * ∑ j, |g j| * (C * ‖Z.val - W.val‖) := by
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      apply norm_sum_le_of_le
      intro j _
      rw [← smul_sub, norm_smul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left
        (norm_finiteContourInteraction_sub_le hγ hγ1 Z₀ r hr href Z W i j hc hσ hM
          (hZc i) (hWc i) (hZsep i j) (hWsep i j) (hZM i) (hZM j) (hWM i) (hWM j))
        (abs_nonneg _)
    _ = _ := by simp only [Finset.sum_mul, mul_assoc]

end Euler2D

end
