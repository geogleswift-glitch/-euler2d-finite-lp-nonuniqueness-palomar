module

public import RequestProject.Euler.CircularFinitePrefixWeightedForcing

/-! The two actual deep-source terms have one cutoff- and rho-uniform
polynomial coefficient. The polynomial is in the local current time. -/

@[expose] public section

set_option maxHeartbeats 6000000

noncomputable section

open Set
open scoped NNReal

namespace Euler2D

def finitePrefixUniformDeepCoefficient (η e L Cd Cb b : ℝ) : ℝ :=
  2 * finiteLabelMassBound * Cb ^ 4 / b *
    (cauchyContourNormBudget 5 η 1 e L + Cd * torusCorrectionContourBudget η L)

theorem finitePrefixCompleteDeepBudget_le_uniform_polynomial
    {η e L Cd Cb b R ρ D t : ℝ}
    (he : 0 < e) (hL : 0 ≤ L) (hCd : 0 ≤ Cd) (hb : 0 < b)
    (hR : 0 ≤ R) (hR1 : R ≤ 1) (hsmall : ρ ^ 2 ≤ b / 2)
    (hD : 0 ≤ D) (hDt : D ≤ t) :
    finitePrefixCompleteDeepBudget η e L Cd Cb b R ρ D ≤
      finitePrefixUniformDeepCoefficient η e L Cd Cb b * ρ ^ 6 * (1 + t) ^ 4 := by
  let A := cauchyContourNormBudget 5 η 1 e L
  let B := Cd * torusCorrectionContourBudget η L
  have hA : 0 ≤ A :=
    (cauchySpatialDerivativeBudget_nonneg 5 (by norm_num : (0 : ℝ) ≤ 1) he 0).trans (le_max_left _ _)
  have htor : 0 ≤ torusCorrectionContourBudget η L := by unfold torusCorrectionContourBudget; positivity
  have hB : 0 ≤ B := mul_nonneg hCd htor
  have hRpow : R ^ 8 ≤ 1 := pow_le_one₀ hR hR1
  have hdenEq : b * (1 - ρ ^ 2 / b) = b - ρ ^ 2 := by field_simp
  have hden : 0 < b * (1 - ρ ^ 2 / b) := by rw [hdenEq]; linarith
  have hdenlo : b / 2 ≤ b * (1 - ρ ^ 2 / b) := by rw [hdenEq]; linarith
  have hnum : finiteLabelMassBound * Cb ^ 4 * (A + B * R ^ 8) * ρ ^ 6 * (1 + D) ^ 4 ≤
      finiteLabelMassBound * Cb ^ 4 * (A + B) * ρ ^ 6 * (1 + t) ^ 4 := by
    have hshape : A + B * R ^ 8 ≤ A + B := by nlinarith only [mul_le_mul_of_nonneg_left hRpow hB]
    have hpow : (1 + D) ^ 4 ≤ (1 + t) ^ 4 :=
      pow_le_pow_left₀ (by linarith) (by linarith) 4
    exact mul_le_mul (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hshape (by positivity [finiteLabelMassBound_nonneg])) (by positivity))
      hpow (by positivity) (by positivity [finiteLabelMassBound_nonneg])
  calc
    _ = (finiteLabelMassBound * Cb ^ 4 * (A + B * R ^ 8) * ρ ^ 6 * (1 + D) ^ 4) /
        (b * (1 - ρ ^ 2 / b)) := by unfold finitePrefixCompleteDeepBudget A B; ring
    _ ≤ (finiteLabelMassBound * Cb ^ 4 * (A + B) * ρ ^ 6 * (1 + t) ^ 4) /
        (b * (1 - ρ ^ 2 / b)) := div_le_div_of_nonneg_right hnum hden.le
    _ ≤ (finiteLabelMassBound * Cb ^ 4 * (A + B) * ρ ^ 6 * (1 + t) ^ 4) / (b / 2) :=
      div_le_div_of_nonneg_left (by positivity [finiteLabelMassBound_nonneg]) (by positivity) hdenlo
    _ = _ := by unfold finitePrefixUniformDeepCoefficient A B; ring

end Euler2D

end
