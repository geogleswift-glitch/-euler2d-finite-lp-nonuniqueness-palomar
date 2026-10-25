module

public import RequestProject.Euler.PlanarKernelLocalIntegrability
public import RequestProject.Euler.PlanarLocalConvolutionDivergence
public import RequestProject.Euler.BoundedLogVelocityApproximation

/-! Genuine compact smoothing of the original singular planar
kernel gives actual globally bounded Lipschitz, smooth, divergence-free
kernels. Their derivative bounds are proved from the original local
singularity and the actual compact smoothing function. -/

@[expose] public section

set_option maxHeartbeats 2500000

noncomputable section

open MeasureTheory Set Filter Topology Metric
open scoped NNReal ContDiff Convolution

namespace Euler2D

theorem exists_lipschitz_planarKernelVelocity_kernelK {φ : R2 → ℝ}
    (hs : HasCompactSupport φ) (hφ : ContDiff ℝ ∞ φ) :
    ∃ B : ℝ≥0, LipschitzWith B (planarKernelVelocity kernelK φ) := by
  let L := (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] R2 →L[ℝ] R2)
  let L' := L.precompL R2
  have hDc : Continuous (fderiv ℝ φ) := hφ.continuous_fderiv (by simp)
  obtain ⟨M, hM⟩ := (hs.fderiv ℝ).exists_bound_of_continuous hDc
  have hM0 : 0 ≤ M := (norm_nonneg (fderiv ℝ φ 0)).trans (hM 0)
  have hDint : Integrable (fun y => ‖fderiv ℝ φ y‖) :=
    (hDc.integrable_of_hasCompactSupport (hs.fderiv ℝ)).norm
  let K0 := planarExpandingKernelCutoff 0
  let c := (2 * Real.pi)⁻¹
  have hc : 0 ≤ c := by dsimp only [c]; positivity
  have hK (z : R2) : ‖kernelK z‖ ≤ ‖K0 z‖ + c := by
    calc
      _ ≤ ‖kernelK z - K0 z‖ + ‖K0 z‖ := norm_le_norm_sub_add _ _
      _ ≤ c + ‖K0 z‖ := add_le_add (by
        simpa only [Nat.cast_zero, zero_add, inv_one, mul_one] using norm_planarExpandingKernelCutoff_sub_le 0 z) le_rfl
      _ = _ := by ring
  let B := M * (∫ y, ‖K0 y‖) + c * ∫ y, ‖fderiv ℝ φ y‖
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  refine ⟨⟨B, hB⟩, ?_⟩
  apply lipschitzWith_of_nnnorm_fderiv_le
    ((contDiff_planarKernelVelocity_kernelK hs hφ).differentiable (by simp))
  intro x
  change ‖fderiv ℝ (φ ⋆[L, volume] kernelK) x‖ ≤ B
  have hd := hs.hasFDerivAt_convolution_left (μ := volume) (g := kernelK)
    L (hφ.of_le (by simp)) locallyIntegrable_planar_kernelK x
  rw [hd.fderiv]
  have hnear : Integrable (fun y => M * ‖K0 (x - y)‖) :=
    (((integrable_planarExpandingKernelCutoff 0).comp_sub_left x).norm).const_mul M
  have hfar : Integrable (fun y => c * ‖fderiv ℝ φ y‖) := hDint.const_mul c
  have hpoint (y : R2) : ‖L' (fderiv ℝ φ y) (kernelK (x - y))‖ ≤
      M * ‖K0 (x - y)‖ + c * ‖fderiv ℝ φ y‖ := by
    calc
      _ ≤ ‖fderiv ℝ φ y‖ * ‖kernelK (x - y)‖ := by
        apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (norm_nonneg _) (norm_nonneg _))
        intro v
        simp only [L', ContinuousLinearMap.precompL_apply, L,
          ContinuousLinearMap.lsmul_apply, norm_smul]
        calc
          ‖fderiv ℝ φ y v‖ * ‖kernelK (x - y)‖ ≤
              (‖fderiv ℝ φ y‖ * ‖v‖) * ‖kernelK (x - y)‖ :=
            mul_le_mul_of_nonneg_right ((fderiv ℝ φ y).le_opNorm v) (norm_nonneg _)
          _ = (‖fderiv ℝ φ y‖ * ‖kernelK (x - y)‖) * ‖v‖ := by ring
      _ ≤ ‖fderiv ℝ φ y‖ * (‖K0 (x - y)‖ + c) :=
        mul_le_mul_of_nonneg_left (hK _) (norm_nonneg (fderiv ℝ φ y))
      _ ≤ _ := by
        have he := mul_le_mul_of_nonneg_right (hM y) (norm_nonneg (K0 (x - y)))
        nlinarith
  have hi : Integrable (fun y => M * ‖K0 (x - y)‖ + c * ‖fderiv ℝ φ y‖) := by
    simpa only [Pi.add_def] using hnear.add hfar
  have he := norm_integral_le_of_norm_le hi (ae_of_all _ hpoint)
  have htrans : (∫ y, ‖K0 (x - y)‖) = ∫ y, ‖K0 y‖ :=
    integral_sub_left_eq_self (μ := volume) (fun y => ‖K0 y‖) x
  exact he.trans_eq (by
    rw [integral_add hnear hfar, integral_const_mul, integral_const_mul, htrans])

theorem exists_smooth_bounded_planarKernelVelocity_kernelK {φ : R2 → ℝ}
    (hs : HasCompactSupport φ) (hφ : ContDiff ℝ ∞ φ) :
    ∃ L M : ℝ≥0, ContDiff ℝ ∞ (planarKernelVelocity kernelK φ) ∧
      LipschitzWith L (planarKernelVelocity kernelK φ) ∧
      (∀ x, ‖planarKernelVelocity kernelK φ x‖ ≤ M) ∧
      ∀ x, pd 0 (planarKernelVelocity kernelK φ) x 0 + pd 1 (planarKernelVelocity kernelK φ) x 1 = 0 := by
  obtain ⟨L, hL⟩ := exists_lipschitz_planarKernelVelocity_kernelK hs hφ
  obtain ⟨M, hM, hbound⟩ := exists_norm_planarKernelVelocity_kernelK_bound hs hφ
  refine ⟨L, ⟨M, hM.le⟩, contDiff_planarKernelVelocity_kernelK hs hφ, hL, hbound, ?_⟩
  intro x
  exact divergence_planarLocalConvolution_zero hs hφ locallyIntegrable_planar_kernelK
    (fun ψ hψ hsψ => kernelK_weak_divergence hψ hsψ) x

def planarSmoothedBiotSavartKernel (n : ℕ) : R2 → R2 :=
  planarKernelVelocity kernelK (planarVelocityMollifier (planarVelocityApproxScale n) (planarVelocityApproxScale_pos n))

theorem exists_planarSmoothedBiotSavartKernel_bounds :
    ∃ L M : ℕ → ℝ≥0, ∀ n, ContDiff ℝ ∞ (planarSmoothedBiotSavartKernel n) ∧
      LipschitzWith (L n) (planarSmoothedBiotSavartKernel n) ∧
      (∀ x, ‖planarSmoothedBiotSavartKernel n x‖ ≤ M n) ∧
      ∀ x, pd 0 (planarSmoothedBiotSavartKernel n) x 0 + pd 1 (planarSmoothedBiotSavartKernel n) x 1 = 0 := by
  classical
  choose L M hbound using (fun n => exists_smooth_bounded_planarKernelVelocity_kernelK
    (planarVelocityMollifier_compact (planarVelocityApproxScale_pos n))
    (planarVelocityMollifier_smooth (planarVelocityApproxScale_pos n)))
  exact ⟨L, M, hbound⟩

end Euler2D

end
