module

public import RequestProject.Euler.CircularUniformCanonicalJointStageScaleClosure

/-! The source coefficient used by actual parent capture has a fixed
fourth-degree warmup envelope. Its constants precede the warmup length;
the varying initial particle radius remains an explicit argument. -/

@[expose] public section

set_option maxHeartbeats 5000000

noncomputable section

namespace Euler2D

theorem finiteCurrentPolynomialForcingCoefficient_nonneg
    {η e L Cb b Cd : ℝ} (he : 0 < e) (hL : 0 ≤ L)
    (hb : 0 < b) (hCd : 0 ≤ Cd) :
    0 ≤ finiteCurrentPolynomialForcingCoefficient η e L Cb b Cd := by
  have hcauchy : 0 ≤ cauchyContourNormBudget 5 η 1 e L :=
    (cauchySpatialDerivativeBudget_nonneg 5 (by norm_num : (0 : ℝ) ≤ 1)
      he 0).trans (le_max_left _ _)
  have htor : 0 ≤ torusCorrectionContourBudget η L := by
    unfold torusCorrectionContourBudget
    positivity
  unfold finiteCurrentPolynomialForcingCoefficient
  positivity [finiteLabelMassBound_nonneg]

theorem finiteCurrentPolynomialForcingCoefficient_scale_radius
    (η e L Cb b Cd z : ℝ) :
    finiteCurrentPolynomialForcingCoefficient η e L (Cb * z) b Cd =
      finiteCurrentPolynomialForcingCoefficient η e L Cb b Cd * z ^ 4 := by
  unfold finiteCurrentPolynomialForcingCoefficient
  ring

theorem radialStageRadiusConstant_warmup_le {Cr Cw W b z : ℝ}
    (hCr : 0 < Cr) (hCw : 0 ≤ Cw) (hb : 0 < b) (hb1 : b < 1)
    (hz : 1 ≤ z) (hW : W ≤ Cw * z) :
    radialStageRadiusConstant Cr W b ≤ radialStageRadiusConstant Cr Cw b * z := by
  have hbase : 0 ≤ 2 + 4 * Cr / (b * (1 - b)) := by
    positivity [sub_pos.mpr hb1]
  have hscale := mul_nonneg hbase (sub_nonneg.mpr hz)
  unfold radialStageRadiusConstant
  nlinarith only [hW, hscale]

theorem finiteCurrentPolynomialForcingCoefficient_warmup_le
    {η e L Cr Cw W b Cd Δ z : ℝ}
    (he : 0 < e) (hL : 0 ≤ L) (hCr : 0 < Cr) (hCw : 0 ≤ Cw)
    (hb : 0 < b) (hb1 : b < 1) (hCd : 0 ≤ Cd) (hΔ : 0 ≤ Δ)
    (hz : 1 ≤ z) (hW0 : 0 ≤ W) (hW : W ≤ Cw * z) :
    finiteCurrentPolynomialForcingCoefficient η e L
        (radialStageRadiusConstant Cr W b) b Cd + Δ ≤
      (finiteCurrentPolynomialForcingCoefficient η e L
        (radialStageRadiusConstant Cr Cw b) b Cd + Δ) * z ^ 4 := by
  have hactual : 0 ≤ radialStageRadiusConstant Cr W b :=
    (radialStageRadiusConstant_pos hCr hW0 hb hb1).le
  have hradius := radialStageRadiusConstant_warmup_le hCr hCw hb hb1 hz hW
  have hpowers := pow_le_pow_left₀ hactual hradius 4
  have hcauchy : 0 ≤ cauchyContourNormBudget 5 η 1 e L :=
    (cauchySpatialDerivativeBudget_nonneg 5 (by norm_num : (0 : ℝ) ≤ 1)
      he 0).trans (le_max_left _ _)
  have htor : 0 ≤ torusCorrectionContourBudget η L := by
    unfold torusCorrectionContourBudget
    positivity
  have hfactor : 0 ≤ (2 / b) * (finiteLabelMassBound *
      cauchyContourNormBudget 5 η 1 e L +
      Cd * torusCorrectionContourBudget η L * finiteLabelMassBound) := by
    positivity [finiteLabelMassBound_nonneg]
  have hforcing : finiteCurrentPolynomialForcingCoefficient η e L
      (radialStageRadiusConstant Cr W b) b Cd ≤
      finiteCurrentPolynomialForcingCoefficient η e L
        (radialStageRadiusConstant Cr Cw b * z) b Cd := by
    unfold finiteCurrentPolynomialForcingCoefficient
    exact mul_le_mul_of_nonneg_left hpowers hfactor
  rw [finiteCurrentPolynomialForcingCoefficient_scale_radius] at hforcing
  have hz4 : 1 ≤ z ^ 4 := by
    simpa only [one_pow] using pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hz 4
  have hdelta : Δ ≤ Δ * z ^ 4 := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hz4 hΔ
  calc
    _ ≤ finiteCurrentPolynomialForcingCoefficient η e L
        (radialStageRadiusConstant Cr Cw b) b Cd * z ^ 4 + Δ * z ^ 4 :=
      add_le_add hforcing hdelta
    _ = _ := by ring

theorem exists_parentCapture_polynomial_warmup_budget
    {η e L Cr Cw b Cd Δ F : ℝ}
    (he : 0 < e) (hL : 0 ≤ L) (hCr : 0 < Cr) (hCw : 0 ≤ Cw)
    (hb : 0 < b) (hb1 : b < 1) (hCd : 0 ≤ Cd) (hΔ : 0 ≤ Δ) (hF : 0 ≤ F) :
    ∃ Bcapture : ℝ, 0 ≤ Bcapture ∧ ∀ Tblock : ℝ, 0 ≤ Tblock →
      ∀ nWarm : ℕ, ∀ W : ℝ, 0 ≤ W → W ≤ Cw * (1 + (nWarm : ℝ) * Tblock) →
      F * (finiteCurrentPolynomialForcingCoefficient η e L
        (radialStageRadiusConstant Cr W b) b Cd + Δ) ≤
        Bcapture * (1 + (nWarm : ℝ) * Tblock) ^ 4 := by
  let Bcapture := F * (finiteCurrentPolynomialForcingCoefficient η e L
    (radialStageRadiusConstant Cr Cw b) b Cd + Δ)
  have hB : 0 ≤ Bcapture := mul_nonneg hF
    (add_nonneg (finiteCurrentPolynomialForcingCoefficient_nonneg he hL hb hCd) hΔ)
  refine ⟨Bcapture, hB, ?_⟩
  intro Tblock hTblock nWarm W hW0 hW
  have hz : 1 ≤ 1 + (nWarm : ℝ) * Tblock :=
    le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg _) hTblock)
  have hbound := finiteCurrentPolynomialForcingCoefficient_warmup_le (η := η)
    he hL hCr hCw hb hb1 hCd hΔ hz hW0 hW
  convert mul_le_mul_of_nonneg_left hbound hF using 1 <;> dsimp only [Bcapture] <;> ring

end Euler2D

end
