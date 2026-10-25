module

public import RequestProject.Euler.CircularFiniteRetardedPhysicalResponse

/-! The complete actual source budget has a single instantaneous
feedback coefficient and a baseline independent of the ancestor
index. Its coefficient retains the true b*rho^2 geometric factor. -/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped NNReal ENNReal

namespace Euler2D

def finiteRetardedAncestorFeedback (η b ρ c B L : ℝ) : ℝ :=
  (interiorContourNormBudget η 1 c B L * (4 * Real.pi * circularRadialPerturbationWeight)) *
    (b * ρ ^ 2) / (1 - b * ρ ^ 2)

def finiteRetardedSourceBaseline (η Ctorus b R ρ L Cb D e d : ℝ) : ℝ :=
  (finiteLabelMassBound * cauchyContourNormBudget 5 η 1 e L) *
    Cb ^ 4 * ρ ^ 6 * (1 + D) ^ 4 / (b * (1 - ρ ^ 2 / b)) +
  Ctorus * torusCorrectionContourBudget η L * d ^ 4 * circularFiniteL1Coefficient b ρ * R ^ 8

theorem finiteRetardedAncestorFeedback_nonneg {η b ρ c B L : ℝ}
    (hb : 0 < b) (houter : b * ρ ^ 2 < 1) (hB : 0 < B) :
    0 ≤ finiteRetardedAncestorFeedback η b ρ c B L := by
  have hC : 0 ≤ interiorContourNormBudget η 1 c B L :=
    (interiorSpatialDerivativeBudget_nonneg (by norm_num : (0 : ℝ) ≤ 1) hB 0).trans (le_max_left _ _)
  have hw : 0 ≤ circularRadialPerturbationWeight :=
    Finset.sum_nonneg (fun i _ => mul_nonneg (abs_nonneg _) (circularContourRadii_bounds i).1.le)
  have hden : 0 < 1 - b * ρ ^ 2 := sub_pos.mpr houter
  unfold finiteRetardedAncestorFeedback
  positivity

theorem circularFiniteL1Coefficient_nonneg_of_ratio {b ρ : ℝ}
    (hb : 0 < b) (hsmall : ρ ^ 2 < b) : 0 ≤ circularFiniteL1Coefficient b ρ := by
  have hd : 0 < 1 - ρ ^ 2 / b := sub_pos.mpr ((div_lt_one hb).mpr hsmall)
  unfold circularFiniteL1Coefficient finiteContourPatchMassBound
  exact add_nonneg (div_nonneg ENNReal.toReal_nonneg hd.le)
    (Finset.sum_nonneg (fun i _ => mul_nonneg (abs_nonneg _) measureReal_nonneg))

theorem finiteRetardedSourceBaseline_nonneg {η Ctorus b R ρ L Cb D e d : ℝ}
    (hCtorus : 0 ≤ Ctorus) (hb : 0 < b) (hsmall : ρ ^ 2 < b)
    (hL : 0 ≤ L) (he : 0 < e) :
    0 ≤ finiteRetardedSourceBaseline η Ctorus b R ρ L Cb D e d := by
  have hd : 0 < 1 - ρ ^ 2 / b := sub_pos.mpr ((div_lt_one hb).mpr hsmall)
  have hC : 0 ≤ cauchyContourNormBudget 5 η 1 e L :=
    (cauchySpatialDerivativeBudget_nonneg 5 (by norm_num : (0 : ℝ) ≤ 1) he 0).trans (le_max_left _ _)
  have hmass := circularFiniteL1Coefficient_nonneg_of_ratio hb hsmall
  have ht : 0 ≤ torusCorrectionContourBudget η L := by unfold torusCorrectionContourBudget; positivity
  unfold finiteRetardedSourceBaseline
  positivity [finiteLabelMassBound_nonneg]

theorem finiteRetardedContourResponseBudget_le_baseline_add_feedback
    {η Ctorus b R ρ c B L δ Cb D e d : ℝ} (hCtorus : 0 ≤ Ctorus)
    (hb : 0 < b) (hsmall : ρ ^ 2 < b) (houter : b * ρ ^ 2 < 1) (hL : 0 ≤ L) (k : ℕ) :
    finiteRetardedContourResponseBudget η Ctorus b R ρ c B L δ Cb D e d k ≤
      finiteRetardedSourceBaseline η Ctorus b R ρ L Cb D e d +
        finiteRetardedAncestorFeedback η b ρ c B L * δ := by
  have hmass := circularFiniteL1Coefficient_nonneg_of_ratio hb hsmall
  have ht : 0 ≤ torusCorrectionContourBudget η L := by unfold torusCorrectionContourBudget; positivity
  have hcoef : 0 ≤ Ctorus * torusCorrectionContourBudget η L * d ^ 4 *
      circularFiniteL1Coefficient b ρ * R ^ 8 := by positivity
  have hp : (b * ρ ^ 2) ^ k ≤ 1 := pow_le_one₀ (by positivity) houter.le
  have hterm := mul_le_of_le_one_right hcoef hp
  unfold finiteRetardedContourResponseBudget finiteRetardedSourceBaseline finiteRetardedAncestorFeedback
  calc
    _ ≤ (interiorContourNormBudget η 1 c B L * (4 * Real.pi * circularRadialPerturbationWeight)) *
          (δ * (b * ρ ^ 2) / (1 - b * ρ ^ 2)) +
        (finiteLabelMassBound * cauchyContourNormBudget 5 η 1 e L) *
          Cb ^ 4 * ρ ^ 6 * (1 + D) ^ 4 / (b * (1 - ρ ^ 2 / b)) +
        Ctorus * torusCorrectionContourBudget η L * d ^ 4 * circularFiniteL1Coefficient b ρ * R ^ 8 :=
      add_le_add le_rfl hterm
    _ = _ := by ring

end Euler2D

end
