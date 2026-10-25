module

public import RequestProject.Euler.CircularRetardedBudgetFeedback

/-! The true same-S rho-six and torus R-eight source baselines have
one fixed rho-six polynomial envelope when R is chosen after rho.
The finite source mass coefficient is bounded before rho is chosen. -/

@[expose] public section

set_option maxHeartbeats 4000000

noncomputable section

open MeasureTheory
open scoped NNReal ENNReal

namespace Euler2D

def circularRetardedUniformMassCoefficient : ℝ :=
  2 * (eLpNorm cellW 1 volume).toReal +
    finiteContourPatchMassBound circularContourStrengths circularContourRadii

theorem circularFiniteL1Coefficient_le_uniform {b ρ : ℝ}
    (hb : 0 < b) (hsmall : ρ ^ 2 ≤ b / 2) :
    circularFiniteL1Coefficient b ρ ≤ circularRetardedUniformMassCoefficient := by
  have hdiv : ρ ^ 2 / b ≤ 1 / 2 := (div_le_iff₀ hb).mpr (by linarith)
  have hd : 0 < 1 - ρ ^ 2 / b := by linarith
  have hcellpos : 0 ≤ (eLpNorm cellW 1 volume).toReal := ENNReal.toReal_nonneg
  have hcell : (eLpNorm cellW 1 volume).toReal / (1 - ρ ^ 2 / b) ≤
      2 * (eLpNorm cellW 1 volume).toReal := by
    apply (div_le_iff₀ hd).mpr
    nlinarith [mul_nonneg hcellpos (show 0 ≤ 1 / 2 - ρ ^ 2 / b by linarith)]
  unfold circularFiniteL1Coefficient circularRetardedUniformMassCoefficient
  exact add_le_add hcell le_rfl

def finiteRetardedUniformBaselineCoefficient (η Ctorus b L Cb e d₀ : ℝ) : ℝ :=
  (2 / b) * (finiteLabelMassBound * cauchyContourNormBudget 5 η 1 e L) * Cb ^ 4 +
    Ctorus * torusCorrectionContourBudget η L * d₀ ^ 4 * circularRetardedUniformMassCoefficient

theorem finiteRetardedSourceBaseline_le_rhoSix_polynomial
    {η Ctorus b R ρ L Cb D e d d₀ : ℝ}
    (hCtorus : 0 ≤ Ctorus) (hb : 0 < b) (hR : 0 ≤ R) (hRρ : R ≤ ρ)
    (hρ : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (hhalf : ρ ^ 2 ≤ b / 2)
    (hL : 0 ≤ L) (hD : 0 ≤ D) (he : 0 < e) (hd : 0 ≤ d) (hd₀ : 0 ≤ d₀)
    (hdbound : d ≤ d₀ * (1 + D)) :
    finiteRetardedSourceBaseline η Ctorus b R ρ L Cb D e d ≤
      finiteRetardedUniformBaselineCoefficient η Ctorus b L Cb e d₀ * ρ ^ 6 * (1 + D) ^ 4 := by
  have hsmall : ρ ^ 2 < b := by linarith
  have hmass := circularFiniteL1Coefficient_nonneg_of_ratio hb hsmall
  have hmassBound := circularFiniteL1Coefficient_le_uniform hb hhalf
  have hM : 0 ≤ circularRetardedUniformMassCoefficient := hmass.trans hmassBound
  have hC : 0 ≤ cauchyContourNormBudget 5 η 1 e L :=
    (cauchySpatialDerivativeBudget_nonneg 5 (by norm_num : (0 : ℝ) ≤ 1) he 0).trans (le_max_left _ _)
  have ht : 0 ≤ torusCorrectionContourBudget η L := by unfold torusCorrectionContourBudget; positivity
  have hden : b / 2 ≤ b * (1 - ρ ^ 2 / b) := by
    rw [mul_sub, mul_one, mul_div_cancel₀ _ hb.ne']
    linarith
  have hinner : (finiteLabelMassBound * cauchyContourNormBudget 5 η 1 e L) *
        Cb ^ 4 * ρ ^ 6 * (1 + D) ^ 4 / (b * (1 - ρ ^ 2 / b)) ≤
      ((2 / b) * (finiteLabelMassBound * cauchyContourNormBudget 5 η 1 e L) * Cb ^ 4) *
        ρ ^ 6 * (1 + D) ^ 4 := by
    calc
      _ ≤ (finiteLabelMassBound * cauchyContourNormBudget 5 η 1 e L) *
          Cb ^ 4 * ρ ^ 6 * (1 + D) ^ 4 / (b / 2) :=
        div_le_div_of_nonneg_left (by positivity [finiteLabelMassBound_nonneg]) (half_pos hb) hden
      _ = _ := by ring
  have hRpow : R ^ 8 ≤ ρ ^ 6 := by
    calc
      _ ≤ ρ ^ 8 := pow_le_pow_left₀ hR hRρ 8
      _ = ρ ^ 6 * ρ ^ 2 := by ring
      _ ≤ _ := mul_le_of_le_one_right (pow_nonneg hρ 6) (pow_le_one₀ hρ hρ1)
  have hdpow : d ^ 4 ≤ d₀ ^ 4 * (1 + D) ^ 4 := by
    simpa only [mul_pow] using pow_le_pow_left₀ hd hdbound 4
  have htorus : Ctorus * torusCorrectionContourBudget η L * d ^ 4 *
        circularFiniteL1Coefficient b ρ * R ^ 8 ≤
      (Ctorus * torusCorrectionContourBudget η L * d₀ ^ 4 * circularRetardedUniformMassCoefficient) *
        ρ ^ 6 * (1 + D) ^ 4 := by
    calc
      _ ≤ Ctorus * torusCorrectionContourBudget η L * (d₀ ^ 4 * (1 + D) ^ 4) *
          circularRetardedUniformMassCoefficient * ρ ^ 6 := by gcongr
      _ = _ := by ring
  unfold finiteRetardedSourceBaseline finiteRetardedUniformBaselineCoefficient
  exact (add_le_add hinner htorus).trans_eq (by ring)

end Euler2D

end
