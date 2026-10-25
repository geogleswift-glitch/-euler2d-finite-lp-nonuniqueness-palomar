module

public import RequestProject.Euler.PlanarExpandingKernelCutoff
public import RequestProject.Euler.PlanarConvolutionWeakDivergence

/-! The original planar Biot--Savart integral is actually integrable
at every point for bounded integrable vorticity. The same genuine
bound controls all expanding cutoff velocities, and their true error
tends uniformly to zero. -/

@[expose] public section

set_option maxHeartbeats 2000000

noncomputable section

open MeasureTheory Set Filter Topology Metric
open scoped NNReal ContDiff UniformConvergence

namespace Euler2D

theorem integrable_planarBiotSavart_integrand {w : R2 → ℝ} {M : ℝ}
    (hw : Integrable w) (hM : ∀ y, ‖w y‖ ≤ M) (x : R2) :
    Integrable (fun y => w y • kernelK (x - y)) := by
  have hnear := integrable_planarKernelVelocity_integrand (integrable_planarExpandingKernelCutoff 0) hw hM x
  have hm : AEStronglyMeasurable (fun y => kernelK (x - y) - planarExpandingKernelCutoff 0 (x - y)) :=
    ((measurable_kernelK.comp (measurable_const.sub measurable_id)).sub
      ((measurable_planarExpandingKernelCutoff 0).comp (measurable_const.sub measurable_id))).aestronglyMeasurable
  have hfar : Integrable (fun y => w y • (kernelK (x - y) - planarExpandingKernelCutoff 0 (x - y))) :=
    hw.smul_bdd ((2 * Real.pi)⁻¹) hm (ae_of_all _ (fun y => by
      simpa only [Nat.cast_zero, zero_add, inv_one, mul_one] using norm_planarExpandingKernelCutoff_sub_le 0 (x - y)))
  apply (hnear.add hfar).congr
  exact ae_of_all _ (fun y => by
    change w y • planarExpandingKernelCutoff 0 (x - y) +
      w y • (kernelK (x - y) - planarExpandingKernelCutoff 0 (x - y)) = w y • kernelK (x - y)
    rw [smul_sub]
    abel)

def planarBiotSavartBound (w : R2 → ℝ) (M : ℝ) : ℝ :=
  M * (∫ y, ‖planarExpandingKernelCutoff 0 y‖) + (2 * Real.pi)⁻¹ * ∫ y, ‖w y‖

theorem norm_planarKernelVelocity_le_planarBiotSavartBound
    {w : R2 → ℝ} {M : ℝ} (hw : Integrable w) (hM : ∀ y, ‖w y‖ ≤ M)
    {J : R2 → R2} (hJ : ∀ z, ‖J z‖ ≤ ‖kernelK z‖) (x : R2) :
    ‖planarKernelVelocity J w x‖ ≤ planarBiotSavartBound w M := by
  let K := planarExpandingKernelCutoff 0
  let c := (2 * Real.pi)⁻¹
  have hc : 0 ≤ c := by dsimp only [c]; positivity
  have hK (z : R2) : ‖kernelK z‖ ≤ ‖K z‖ + c := by
    calc
      _ ≤ ‖kernelK z - K z‖ + ‖K z‖ := norm_le_norm_sub_add _ _
      _ ≤ c + ‖K z‖ := add_le_add (by
        simpa only [Nat.cast_zero, zero_add, inv_one, mul_one] using norm_planarExpandingKernelCutoff_sub_le 0 z) le_rfl
      _ = _ := by ring
  have hnear : Integrable (fun y => M * ‖K (x - y)‖) :=
    (((integrable_planarExpandingKernelCutoff 0).comp_sub_left x).norm).const_mul M
  have hfar : Integrable (fun y => c * ‖w y‖) := hw.norm.const_mul c
  have hpoint (y : R2) : ‖w y • J (x - y)‖ ≤ M * ‖K (x - y)‖ + c * ‖w y‖ := by
    rw [norm_smul]
    calc
      _ ≤ ‖w y‖ * (‖K (x - y)‖ + c) := mul_le_mul_of_nonneg_left ((hJ _).trans (hK _)) (norm_nonneg _)
      _ ≤ M * ‖K (x - y)‖ + c * ‖w y‖ := by nlinarith [mul_le_mul_of_nonneg_right (hM y) (norm_nonneg (K (x - y)))]
  calc
    _ ≤ ∫ y, M * ‖K (x - y)‖ + c * ‖w y‖ := norm_integral_le_of_norm_le (hnear.add hfar) (ae_of_all _ hpoint)
    _ = _ := by
      have htrans : (∫ y, ‖K (x - y)‖) = ∫ y, ‖K y‖ :=
        integral_sub_left_eq_self (μ := volume) (fun y => ‖K y‖) x
      rw [integral_add hnear hfar, integral_const_mul, integral_const_mul, htrans]
      rfl

theorem norm_planarBiotSavart_sub_cutoff_velocity_le {w : R2 → ℝ} {M : ℝ}
    (hw : Integrable w) (hM : ∀ y, ‖w y‖ ≤ M) (n : ℕ) (x : R2) :
    ‖planarKernelVelocity kernelK w x - planarKernelVelocity (planarExpandingKernelCutoff n) w x‖ ≤
      ((2 * Real.pi)⁻¹ * ((n : ℝ) + 1)⁻¹) * ∫ y, ‖w y‖ := by
  have hI := integrable_planarBiotSavart_integrand hw hM x
  have hIn := integrable_planarKernelVelocity_integrand (integrable_planarExpandingKernelCutoff n) hw hM x
  unfold planarKernelVelocity
  rw [← integral_sub hI hIn]
  have he : (fun y => w y • kernelK (x - y) - w y • planarExpandingKernelCutoff n (x - y)) =
      (fun y => w y • (kernelK (x - y) - planarExpandingKernelCutoff n (x - y))) :=
    funext (fun y => (smul_sub _ _ _).symm)
  rw [he]
  calc
    _ ≤ ∫ y, ((2 * Real.pi)⁻¹ * ((n : ℝ) + 1)⁻¹) * ‖w y‖ := by
      apply norm_integral_le_of_norm_le (hw.norm.const_mul _) (ae_of_all _ (fun y => ?_))
      rw [norm_smul]
      exact (mul_le_mul_of_nonneg_left (norm_planarExpandingKernelCutoff_sub_le n (x - y)) (norm_nonneg _)).trans_eq (mul_comm _ _)
    _ = _ := integral_const_mul _ _

theorem tendstoUniformly_planarBiotSavart_cutoff_velocity {w : R2 → ℝ} {M : ℝ}
    (hw : Integrable w) (hM : ∀ y, ‖w y‖ ≤ M) :
    TendstoUniformly (fun n => planarKernelVelocity (planarExpandingKernelCutoff n) w)
      (planarKernelVelocity kernelK w) atTop := by
  have hlim : Tendsto (fun n : ℕ => ((2 * Real.pi)⁻¹ * ((n : ℝ) + 1)⁻¹) * ∫ y, ‖w y‖) atTop (𝓝 0) := by
    simpa only [one_div, mul_zero, zero_mul] using
      (tendsto_one_div_add_atTop_nhds_zero_nat.const_mul ((2 * Real.pi)⁻¹)).mul_const (∫ y, ‖w y‖)
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  filter_upwards [hlim.eventually (eventually_lt_nhds hε)] with n hn x
  rw [dist_eq_norm]
  exact (norm_planarBiotSavart_sub_cutoff_velocity_le hw hM n x).trans_lt hn

end Euler2D

end
