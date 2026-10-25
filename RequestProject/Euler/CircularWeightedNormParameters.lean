module

public import RequestProject.Euler.SmallNonzeroTransferRatio
public import RequestProject.Euler.WeightedInteractionRowBudget

/-! The original nonzero transfer ratio is selected after the fixed
self/row constants and before rho. Its true weighted propagation rate
is then strictly below the unchanged current sigma. -/

@[expose] public section

set_option maxHeartbeats 4000000

noncomputable section

open Complex Set Filter Topology
open scoped NNReal

namespace Euler2D

def weightedNormPropagationExponent (K b Cup Cdown C₀ Ctorus R ρ : ℝ) : ℝ :=
  b * K + Ctorus * R ^ 8 + weightedInteractionRowFeedback b Cup Cdown C₀ ρ

theorem tendsto_weightedNormPropagationExponent_diag (K b Cup Cdown C₀ Ctorus : ℝ) :
    Tendsto (fun x : ℝ => weightedNormPropagationExponent K b Cup Cdown C₀ Ctorus
      (Real.exp (-x)) (Real.exp (-x))) atTop
      (𝓝 (b * K + b * (Cup / (C₀ - 1)))) := by
  have hpow := Real.tendsto_exp_neg_atTop_nhds_zero.pow 8
  have hζ := hpow.const_mul C₀
  have hone : Tendsto (fun _x : ℝ => (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
  have hden := hone.sub hζ
  have hratio := (hζ.const_mul Cdown).div hden (by norm_num : (1 : ℝ) - C₀ * 0 ^ 8 ≠ 0)
  have hbk : Tendsto (fun _x : ℝ => b * K) atTop (𝓝 (b * K)) := tendsto_const_nhds
  have hcup : Tendsto (fun _x : ℝ => Cup / (C₀ - 1)) atTop (𝓝 (Cup / (C₀ - 1))) := tendsto_const_nhds
  have hb : Tendsto (fun _x : ℝ => b) atTop (𝓝 b) := tendsto_const_nhds
  have hh := (hbk.add (hpow.const_mul Ctorus)).add (hb.mul (hcup.add hratio))
  simpa only [weightedNormPropagationExponent, weightedInteractionRowFeedback,
    Pi.div_apply, zero_pow (by norm_num : 8 ≠ 0), mul_zero, sub_zero, div_one, add_zero] using hh

namespace CircularMaterialTransferProfile

variable {γ : ℝ≥0} {hγ : 0 < γ} {hγ1 : (γ : ℝ) < 1}
    (P : CircularMaterialTransferProfile hγ hγ1)

theorem exists_nonzeroTransfer_weightedNorm_gap {K Cup Cdown C₀ : ℝ}
    (hK : 0 < K) (hup : 0 ≤ Cup) (hdown : 0 ≤ Cdown) (hC₀ : 1 < C₀) :
    ∃ b ∈ Ioo (0 : ℝ) (1 / 4),
      bilateral P.moment ((b : ℂ) * (sigma + 5 / 4 * I)) ≠ 0 ∧
      0 < b * K ∧ b * K + b * (Cup / (C₀ - 1)) < sigma / 4 ∧
      ∀ Ctorus : ℝ, 0 ≤ Ctorus → ∀ᶠ x : ℝ in atTop,
        C₀ * (Real.exp (-x)) ^ 8 < 1 ∧
        ∀ R : ℝ, 0 ≤ R → R ≤ Real.exp (-x) →
          b * K ≤ weightedNormPropagationExponent K b Cup Cdown C₀ Ctorus R (Real.exp (-x)) ∧
          weightedNormPropagationExponent K b Cup Cdown C₀ Ctorus R (Real.exp (-x)) ≤ sigma / 3 := by
  have hσ : 0 < sigma := P.laplace.sigma_pos
  have hC : 0 < C₀ - 1 := sub_pos.mpr hC₀
  have hratio : 0 ≤ Cup / (C₀ - 1) := div_nonneg hup hC.le
  have hB : 0 < sigma / (16 * (K + Cup / (C₀ - 1) + 1)) := div_pos hσ (by positivity)
  obtain ⟨b, hb, hsmall, hne⟩ := P.exists_nonzero_transfer_ratio_below hB
  have hsmall' := (lt_div_iff₀ (by positivity : 0 < 16 * (K + Cup / (C₀ - 1) + 1))).mp hsmall
  have hbasenn : 0 ≤ b * K + b * (Cup / (C₀ - 1)) :=
    add_nonneg (mul_nonneg hb.1.le hK.le) (mul_nonneg hb.1.le hratio)
  have hbase : b * K + b * (Cup / (C₀ - 1)) < sigma / 4 := by nlinarith only [hsmall', hb.1, hbasenn]
  refine ⟨b, hb, hne, mul_pos hb.1 hK, hbase, ?_⟩
  intro Ctorus htorus
  have hlim := tendsto_weightedNormPropagationExponent_diag K b Cup Cdown C₀ Ctorus
  have hexp : ∀ᶠ x : ℝ in atTop,
      weightedNormPropagationExponent K b Cup Cdown C₀ Ctorus (Real.exp (-x)) (Real.exp (-x)) < sigma / 3 :=
    hlim.eventually (gt_mem_nhds (by nlinarith only [hbase, hσ]))
  have hζlim := (Real.tendsto_exp_neg_atTop_nhds_zero.pow 8).const_mul C₀
  have hζev : ∀ᶠ x : ℝ in atTop, C₀ * (Real.exp (-x)) ^ 8 < 1 := by
    have hh : Tendsto (fun x : ℝ => C₀ * (Real.exp (-x)) ^ 8) atTop (𝓝 0) := by simpa using hζlim
    exact hh.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [hexp, hζev] with x hx hζ
  refine ⟨hζ, ?_⟩
  intro R hR hRmax
  have hfb := weightedInteractionRowFeedback_nonneg hb.1.le hup hdown hC₀ hζ
  constructor
  · unfold weightedNormPropagationExponent
    have hRpow : 0 ≤ Ctorus * R ^ 8 := by positivity
    linarith only [hfb, hRpow]
  · apply le_trans ?_ hx.le
    unfold weightedNormPropagationExponent
    exact add_le_add (add_le_add le_rfl (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ hR hRmax 8) htorus)) le_rfl

end CircularMaterialTransferProfile
end Euler2D

end
