module

public import RequestProject.Euler.TorusRegularizedVelocityBounds
public import RequestProject.Euler.TorusKernelTimeContinuity

/-! Uniform logarithmic regularity and convergence of actual regularized velocities. -/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology Metric Real
open scoped ENNReal ContDiff

namespace Euler2D

theorem exists_uniform_logLip_regularizedKernelVelocity :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (ε : ℝ) (hε : 0 < ε), ε ≤ 1 →
      ∀ (w : R2 → ℝ) (M : ℝ), AEStronglyMeasurable w μT → 0 ≤ M →
        (∀ᵐ y ∂μT, ‖w y‖ ≤ M) → ∀ x z, ‖x - z‖ ≤ 1 / 2 →
        ‖torusKernelAverage w (regularizedTorusKernel ε hε) x -
          torusKernelAverage w (regularizedTorusKernel ε hε) z‖ ≤
          (M * C) * logFlowModulus ‖x - z‖ := by
  obtain ⟨C, hC, hbound⟩ := exists_torusKernelTranslationError_le_logFlowModulus
  refine ⟨C, hC, fun ε hε hε1 w M hw hM0 hM x z hxz => ?_⟩
  exact (norm_regularizedTorusVelocity_sub_le hε hε1 hw hM0 hM x z).trans
    (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (hbound (x - z) hxz) hM0)

theorem tendstoUniformly_regularizedTorusVelocity {ι : Type*} {l : Filter ι}
    (ε : ι → ℝ) (hε : ∀ i, 0 < ε i) (hlim : Tendsto ε l (𝓝 0))
    {W : ι → Lp ℝ 2 μT} {Z : Lp ℝ 2 μT} (hW : Tendsto W l (𝓝 Z))
    {M : ℝ} (hM0 : 0 ≤ M) (hM : ∀ i, ∀ᵐ y ∂μT, ‖W i y‖ ≤ M)
    (hZ : ∀ᵐ y ∂μT, ‖Z y‖ ≤ M) :
    TendstoUniformly (fun i => torusKernelAverage (W i) (regularizedTorusKernel (ε i) (hε i)))
      (torusKernelVelocity Z) l := by
  have htrue := tendstoUniformly_torusKernelVelocity_of_tendsto_L2 hW hM0 hM hZ
  have herr : Tendsto (fun i => M * regularizedTorusKernelL1Error (ε i) (hε i)) l (𝓝 0) := by
    simpa only [mul_zero] using (tendsto_regularizedTorusKernel_L1 ε hε hlim).const_mul M
  have heps : ∀ᶠ i in l, ε i ≤ 1 := by
    filter_upwards [hlim.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))] with i hi
    exact hi.le
  rw [Metric.tendstoUniformly_iff]
  intro δ hδ
  have hnear := Metric.tendstoUniformly_iff.mp htrue (δ / 2) (by linarith)
  filter_upwards [heps, hnear, herr.eventually (Iio_mem_nhds (by linarith : (0 : ℝ) < δ / 2))]
    with i hi hnear herr x
  have hb := norm_regularizedTorusVelocity_error_le (hε i) hi
    (Lp.aestronglyMeasurable _) (hM i) x
  have ht := hnear x
  rw [dist_eq_norm] at ht ⊢
  rw [norm_sub_rev] at hb
  exact (norm_sub_le_norm_sub_add_norm_sub _ (torusKernelVelocity (W i) x) _).trans_lt
    ((add_lt_add ht (hb.trans_lt herr)).trans_eq (by ring))

end Euler2D

end
