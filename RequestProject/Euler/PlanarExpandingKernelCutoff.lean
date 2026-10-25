module

public import RequestProject.Euler.PlanarKernelBounds
public import RequestProject.Euler.PlanarWeakDivergenceMollification

/-! Actual expanding radial cutoffs of the genuine planar
Biot--Savart kernel. Each cutoff is integrable and distributionally
incompressible; the true kernel error tends uniformly to zero. -/

@[expose] public section

set_option maxHeartbeats 2000000

noncomputable section

open MeasureTheory Set Filter Topology Metric
open scoped NNReal ContDiff UniformConvergence

namespace Euler2D

def planarExpandingCutoffBump (n : ℕ) : ContDiffBump (0 : ℝ) where
  rIn := ((n : ℝ) + 1) ^ 2
  rOut := ((n : ℝ) + 1) ^ 2 + 1
  rIn_pos := by positivity
  rIn_lt_rOut := by linarith

def planarExpandingKernelCutoff (n : ℕ) : R2 → R2 :=
  cutoffKernelK (planarExpandingCutoffBump n)

theorem measurable_planarExpandingKernelCutoff (n : ℕ) : Measurable (planarExpandingKernelCutoff n) := by
  change Measurable (fun x : R2 => (planarExpandingCutoffBump n) (‖x‖ ^ 2) • kernelK x)
  exact ((planarExpandingCutoffBump n).continuous.measurable.comp
    (continuous_norm.measurable.pow_const 2)).smul measurable_kernelK

theorem norm_planarExpandingKernelCutoff_le (n : ℕ) (x : R2) :
    ‖planarExpandingKernelCutoff n x‖ ≤ ‖kernelK x‖ := by
  change ‖(planarExpandingCutoffBump n) (‖x‖ ^ 2) • kernelK x‖ ≤ _
  rw [norm_smul, Real.norm_of_nonneg ((planarExpandingCutoffBump n).nonneg)]
  exact mul_le_of_le_one_left (norm_nonneg _) (planarExpandingCutoffBump n).le_one

theorem integrable_planarExpandingKernelCutoff (n : ℕ) : Integrable (planarExpandingKernelCutoff n) := by
  have hc : ContDiff ℝ ∞ (planarExpandingCutoffBump n) := (planarExpandingCutoffBump n).contDiff
  exact integrable_cutoffKernelK hc.continuous (planarExpandingCutoffBump n).hasCompactSupport

theorem planarExpandingKernelCutoff_weakly_divergenceFree (n : ℕ) :
    IsPlanarWeaklyDivergenceFree (planarExpandingKernelCutoff n) := by
  intro ψ hψ hs
  have hc : ContDiff ℝ 1 (planarExpandingCutoffBump n) := (planarExpandingCutoffBump n).contDiff
  exact cutoffKernelK_weak_divergence hc hψ hs

theorem planarExpandingKernelCutoff_eq_kernelK (n : ℕ) {x : R2} (hx : ‖x‖ ≤ (n : ℝ) + 1) :
    planarExpandingKernelCutoff n x = kernelK x := by
  have hx2 : ‖x‖ ^ 2 ∈ closedBall (0 : ℝ) (((n : ℝ) + 1) ^ 2) := by
    rw [mem_closedBall, Real.dist_eq, sub_zero, abs_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (norm_nonneg x) hx 2
  have he := (planarExpandingCutoffBump n).one_of_mem_closedBall hx2
  simp only [planarExpandingKernelCutoff, cutoffKernelK, radialKernelCutoff, he, one_smul]

theorem norm_planarExpandingKernelCutoff_sub_le (n : ℕ) (x : R2) :
    ‖kernelK x - planarExpandingKernelCutoff n x‖ ≤ (2 * Real.pi)⁻¹ * ((n : ℝ) + 1)⁻¹ := by
  have hN : 0 < (n : ℝ) + 1 := by positivity
  have hχ0 := (planarExpandingCutoffBump n).nonneg (x := ‖x‖ ^ 2)
  have hχ1 := (planarExpandingCutoffBump n).le_one (x := ‖x‖ ^ 2)
  have hbound : ‖kernelK x - planarExpandingKernelCutoff n x‖ ≤ ‖kernelK x‖ := by
    change ‖kernelK x - (planarExpandingCutoffBump n) (‖x‖ ^ 2) • kernelK x‖ ≤ _
    have he : kernelK x - (planarExpandingCutoffBump n) (‖x‖ ^ 2) • kernelK x =
        (1 - (planarExpandingCutoffBump n) (‖x‖ ^ 2)) • kernelK x := by rw [sub_smul, one_smul]
    rw [he, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
    exact mul_le_of_le_one_left (norm_nonneg _) (by linarith)
  by_cases hx : ‖x‖ ≤ (n : ℝ) + 1
  · rw [planarExpandingKernelCutoff_eq_kernelK n hx, sub_self, norm_zero]
    positivity
  · have hn : (n : ℝ) + 1 ≤ ‖x‖ := (lt_of_not_ge hx).le
    apply hbound.trans
    rw [norm_planar_kernelK]
    gcongr

theorem tendstoUniformly_planarExpandingKernelCutoff :
    TendstoUniformly planarExpandingKernelCutoff kernelK atTop := by
  have hlim : Tendsto (fun n : ℕ => (2 * Real.pi)⁻¹ * ((n : ℝ) + 1)⁻¹) atTop (𝓝 0) := by
    simpa only [one_div, mul_zero] using tendsto_one_div_add_atTop_nhds_zero_nat.const_mul ((2 * Real.pi)⁻¹)
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  filter_upwards [hlim.eventually (eventually_lt_nhds hε)] with n hn x
  rw [dist_eq_norm]
  exact (norm_planarExpandingKernelCutoff_sub_le n x).trans_lt hn

end Euler2D

end
