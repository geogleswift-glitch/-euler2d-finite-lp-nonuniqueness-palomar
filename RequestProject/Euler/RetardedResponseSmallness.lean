module

public import RequestProject.Euler.RetardedLogarithmicAbsorption

/-! The closed delayed ancestor response tends to zero, and its
true geometric contribution to the current layer is little-o of the
rho-six seed. The complete logarithmic time loss remains explicit. -/

@[expose] public section

set_option maxHeartbeats 4000000

noncomputable section

open Filter Topology

namespace Euler2D

def retardedClosedResponse (b K L C B x : ℝ) : ℝ :=
  2 * (b * retardedLogHorizon b L C x * Real.exp (K * b * retardedLogHorizon b L C x)) *
    (B * Real.exp (-x) ^ 6 * (1 + retardedLogHorizon b L C x) ^ 4)

theorem tendsto_retardedClosedResponse (b K L C B : ℝ)
    (hgap : K * b * L / (1 - b) < 2) :
    Tendsto (retardedClosedResponse b K L C B) atTop (𝓝 0) := by
  have hp := tendsto_retardedResponse_geometric_polynomial b K L C 4 hgap
  have hden : Tendsto (fun x : ℝ => 1 - b * Real.exp (-x) ^ 2) atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.sub ((Real.tendsto_exp_neg_atTop_nhds_zero.pow 2).const_mul b)
  have hh := (hp.mul ((Real.tendsto_exp_neg_atTop_nhds_zero.pow 4).mul hden)).const_mul (2 * B)
  have hne : ∀ᶠ x : ℝ in atTop, 1 - b * Real.exp (-x) ^ 2 ≠ 0 :=
    hden.eventually_ne (by norm_num : (1 : ℝ) ≠ 0)
  have hh' : Tendsto (fun x : ℝ =>
      2 * B * ((Real.exp (-x) ^ 2 *
        (b * retardedLogHorizon b L C x * Real.exp (K * b * retardedLogHorizon b L C x)) *
        (1 + retardedLogHorizon b L C x) ^ 4 / (1 - b * Real.exp (-x) ^ 2)) *
          (Real.exp (-x) ^ 4 * (1 - b * Real.exp (-x) ^ 2)))) atTop (𝓝 0) := by
    simpa using hh
  apply hh'.congr'
  filter_upwards [hne] with x hx
  change 2 * B *
    ((Real.exp (-x) ^ 2 *
      (b * retardedLogHorizon b L C x * Real.exp (K * b * retardedLogHorizon b L C x)) *
      (1 + retardedLogHorizon b L C x) ^ 4 / (1 - b * Real.exp (-x) ^ 2)) *
        (Real.exp (-x) ^ 4 * (1 - b * Real.exp (-x) ^ 2))) = _
  have hcancel (N : ℝ) : N / (1 - b * Real.exp (-x) ^ 2) *
      (Real.exp (-x) ^ 4 * (1 - b * Real.exp (-x) ^ 2)) = N * Real.exp (-x) ^ 4 := by
    calc
      _ = (N / (1 - b * Real.exp (-x) ^ 2) * (1 - b * Real.exp (-x) ^ 2)) * Real.exp (-x) ^ 4 := by ring
      _ = _ := by rw [div_mul_cancel₀ _ hx]
  rw [hcancel]
  unfold retardedClosedResponse
  ring

theorem eventually_retardedResponse_seed_smallness (b K L C B feedback : ℝ)
    (hgap : K * b * L / (1 - b) < 2) {δ ε : ℝ} (hδ : 0 < δ) (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop,
      (2 * (b * retardedLogHorizon b L C x * Real.exp (K * b * retardedLogHorizon b L C x)) *
        (feedback * b * Real.exp (-x) ^ 2 / (1 - b * Real.exp (-x) ^ 2)) ≤ 1) ∧
      retardedClosedResponse b K L C B x ≤ δ ∧
      (feedback * b * Real.exp (-x) ^ 2 / (1 - b * Real.exp (-x) ^ 2)) *
        retardedClosedResponse b K L C B x ≤ ε * Real.exp (-x) ^ 6 := by
  have hq := (tendsto_retardedClosedResponse b K L C B hgap).eventually (gt_mem_nhds hδ)
  have hsmall := (tendsto_retardedResponse_geometric_polynomial b K L C 4 hgap).const_mul
    (2 * feedback * b * B)
  simp only [mul_zero] at hsmall
  have hs := hsmall.eventually (gt_mem_nhds hε)
  filter_upwards [eventually_retardedResponse_absorption b K L C feedback hgap, hq, hs] with x ha hqx hsx
  refine ⟨ha, hqx.le, ?_⟩
  have hm := mul_le_mul_of_nonneg_right hsx.le (pow_nonneg (Real.exp_pos (-x)).le 6)
  convert hm using 1 <;> unfold retardedClosedResponse <;> ring

end Euler2D

end
