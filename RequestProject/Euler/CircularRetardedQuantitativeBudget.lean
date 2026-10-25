module

public import RequestProject.Euler.CircularRetardedBaselineScale
public import RequestProject.Euler.CircularCumulativeStageClock
public import RequestProject.Euler.RetardedResponseSmallness

/-! The actual physical-clock response budget is bounded by the
same explicit logarithmic response whose smallness was proved. The
true source baseline and geometric cumulative duration are both used. -/

@[expose] public section

set_option maxHeartbeats 4000000

noncomputable section

open MeasureTheory
open scoped NNReal ENNReal

namespace Euler2D

theorem finiteRetardedUniformBaselineCoefficient_nonneg
    {η Ctorus b L Cb e d₀ : ℝ} (hCtorus : 0 ≤ Ctorus) (hb : 0 < b) (hL : 0 ≤ L) (he : 0 < e) :
    0 ≤ finiteRetardedUniformBaselineCoefficient η Ctorus b L Cb e d₀ := by
  have hC : 0 ≤ cauchyContourNormBudget 5 η 1 e L :=
    (cauchySpatialDerivativeBudget_nonneg 5 (by norm_num : (0 : ℝ) ≤ 1) he 0).trans (le_max_left _ _)
  have ht : 0 ≤ torusCorrectionContourBudget η L := by unfold torusCorrectionContourBudget; positivity
  have hmass : 0 ≤ circularRetardedUniformMassCoefficient := by
    unfold circularRetardedUniformMassCoefficient finiteContourPatchMassBound
    exact add_nonneg (by positivity)
      (Finset.sum_nonneg (fun i _ => mul_nonneg (abs_nonneg _) measureReal_nonneg))
  unfold finiteRetardedUniformBaselineCoefficient
  positivity [finiteLabelMassBound_nonneg]

theorem actual_physical_response_budget_le_logarithmic_closedResponse
    {η Ctorus b K A H R L Cb e d d₀ clock C x : ℝ}
    (hCtorus : 0 ≤ Ctorus) (hb : 0 < b) (hb1 : b < 1) (hK : 0 ≤ K)
    (hA : 0 < A) (hH : 0 ≤ H) (hR : 0 ≤ R) (hRρ : R ≤ Real.exp (-x))
    (hρ1 : Real.exp (-x) ≤ 1) (hhalf : Real.exp (-x) ^ 2 ≤ b / 2)
    (hL : 0 ≤ L) (hD : 0 ≤ clock * x + C) (he : 0 < e) (hd : 0 ≤ d) (hd₀ : 0 ≤ d₀)
    (hdbound : d ≤ d₀ * (1 + (clock * x + C)))
    (htime : H ≤ (clock * x + C) / ((1 - b) * A)) :
    2 * (b * A * H * Real.exp (b * A * K * H)) *
        finiteRetardedSourceBaseline η Ctorus b R (Real.exp (-x)) L Cb (clock * x + C) e d ≤
      retardedClosedResponse b K clock C
        (finiteRetardedUniformBaselineCoefficient η Ctorus b L Cb e d₀) x := by
  let D := clock * x + C
  let Dnorm := retardedLogHorizon b clock C x
  let Cbase := finiteRetardedUniformBaselineCoefficient η Ctorus b L Cb e d₀
  have hDnorm : 0 ≤ Dnorm := div_nonneg hD (sub_pos.mpr hb1).le
  have hDle : D ≤ Dnorm := by
    apply (le_div_iff₀ (sub_pos.mpr hb1)).mpr
    change D * (1 - b) ≤ D
    nlinarith only [mul_nonneg hD hb.le]
  have hCbase : 0 ≤ Cbase := finiteRetardedUniformBaselineCoefficient_nonneg hCtorus hb hL he
  have hbase := finiteRetardedSourceBaseline_le_rhoSix_polynomial (η := η) (Cb := Cb) hCtorus hb hR hRρ
    (Real.exp_pos _).le hρ1 hhalf hL hD he hd hd₀ hdbound
  have hbase' : finiteRetardedSourceBaseline η Ctorus b R (Real.exp (-x)) L Cb D e d ≤
      Cbase * Real.exp (-x) ^ 6 * (1 + Dnorm) ^ 4 := by
    exact hbase.trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by linarith) (by linarith) 4) (by positivity))
  have hF := cumulative_actual_response_factor_le hb.le hb1 hK hA hH htime
  have hsmall : Real.exp (-x) ^ 2 < b := by linarith
  have hbase0 : 0 ≤ finiteRetardedSourceBaseline η Ctorus b R (Real.exp (-x)) L Cb D e d :=
    finiteRetardedSourceBaseline_nonneg hCtorus hb hsmall hL he
  have hF0 : 0 ≤ 2 * (b * Dnorm * Real.exp (K * b * Dnorm)) := by positivity
  have hF' : 2 * (b * A * H * Real.exp (b * A * K * H)) ≤
      2 * (b * Dnorm * Real.exp (K * b * Dnorm)) := by
    convert mul_le_mul_of_nonneg_left hF (by norm_num : (0 : ℝ) ≤ 2) using 1 <;>
      dsimp only [Dnorm, retardedLogHorizon] <;> ring
  exact mul_le_mul hF' hbase' hbase0 hF0

end Euler2D

end
