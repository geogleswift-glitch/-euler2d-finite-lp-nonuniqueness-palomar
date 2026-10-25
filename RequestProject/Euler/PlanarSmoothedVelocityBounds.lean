module

public import RequestProject.Euler.PlanarSmoothKernel
public import RequestProject.Euler.PlanarBiotSavartConvolution
public import RequestProject.Euler.PlanarBiotSavartLogBounds

/-! The actual normalized smoothings preserve a common speed and
logarithmic spatial modulus for bounded integrable vorticity. Their
true velocity error tends to zero with the original mollifier scale. -/

@[expose] public section

set_option maxHeartbeats 2500000

noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal ContDiff

namespace Euler2D

def planarBiotSavartMassBound (M A : ℝ) : ℝ :=
  M * (∫ y, ‖planarExpandingKernelCutoff 0 y‖) + (2 * Real.pi)⁻¹ * A

theorem norm_planarBiotSavart_le_massBound {w : R2 → ℝ} {M A : ℝ}
    (hw : Integrable w) (hM : ∀ y, ‖w y‖ ≤ M) (hA : ∫ y, ‖w y‖ ≤ A) (x : R2) :
    ‖planarKernelVelocity kernelK w x‖ ≤ planarBiotSavartMassBound M A := by
  apply (norm_planarKernelVelocity_le_planarBiotSavartBound hw hM (fun z => le_refl ‖kernelK z‖) x).trans
  dsimp only [planarBiotSavartBound, planarBiotSavartMassBound]
  exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hA (by positivity))

theorem norm_planarSmoothedKernelVelocity_le_massBound {w : R2 → ℝ} {M A : ℝ}
    (hw : Integrable w) (hM : ∀ y, ‖w y‖ ≤ M) (hA : ∫ y, ‖w y‖ ≤ A) (n : ℕ) (x : R2) :
    ‖planarKernelVelocity (planarSmoothedBiotSavartKernel n) w x‖ ≤ planarBiotSavartMassBound M A := by
  let φ := planarVelocityMollifier (planarVelocityApproxScale n) (planarVelocityApproxScale_pos n)
  have hφ : Integrable φ := planarVelocityMollifier_integrable _
  let v : ℝ → R2 → R2 := fun _ => planarKernelVelocity kernelK w
  have hv : Continuous (Function.uncurry v) := (uniformContinuous_planarBiotSavart hw hM).continuous.comp continuous_snd
  have hMb (t : ℝ) (z : R2) : ‖v t z‖ ≤ planarBiotSavartMassBound M A := norm_planarBiotSavart_le_massBound hw hM hA z
  change ‖planarKernelVelocity (planarKernelVelocity kernelK φ) w x‖ ≤ _
  rw [planarBiotSavart_smoothing_convolution hφ hw hM x]
  exact norm_boundedVelocityMollification_le hφ (planarVelocityMollifier_nonneg _)
    (planarVelocityMollifier_integral _) hMb (t := 0) x

theorem planarSmoothedKernelVelocity_logFlowModulus_le {w : R2 → ℝ} {M A : ℝ}
    (hw : Integrable w) (hM : ∀ y, ‖w y‖ ≤ M) (hA : ∫ y, ‖w y‖ ≤ A) (n : ℕ)
    {x y : R2} (hxy : ‖x - y‖ ≤ 1 / 2) :
    ‖planarKernelVelocity (planarSmoothedBiotSavartKernel n) w x -
        planarKernelVelocity (planarSmoothedBiotSavartKernel n) w y‖ ≤
      (8 * (M + A)) * logFlowModulus ‖x - y‖ := by
  let φ := planarVelocityMollifier (planarVelocityApproxScale n) (planarVelocityApproxScale_pos n)
  have hφ : Integrable φ := planarVelocityMollifier_integrable _
  let v : ℝ → R2 → R2 := fun _ => planarKernelVelocity kernelK w
  have hv : Continuous (Function.uncurry v) := (uniformContinuous_planarBiotSavart hw hM).continuous.comp continuous_snd
  have hMb (t : ℝ) (z : R2) : ‖v t z‖ ≤ planarBiotSavartMassBound M A := norm_planarBiotSavart_le_massBound hw hM hA z
  change ‖planarKernelVelocity (planarKernelVelocity kernelK φ) w x -
    planarKernelVelocity (planarKernelVelocity kernelK φ) w y‖ ≤ _
  rw [planarBiotSavart_smoothing_convolution hφ hw hM x, planarBiotSavart_smoothing_convolution hφ hw hM y]
  exact boundedVelocityMollification_logFlowModulus_le hφ (planarVelocityMollifier_nonneg _)
    (planarVelocityMollifier_integral _) hv hMb
    (fun t a b hab => planarBiotSavart_logFlowModulus_le hw hM hA hab) 0 hxy

theorem norm_planarSmoothedKernelVelocity_sub_le {w : R2 → ℝ} {M A : ℝ}
    (hw : Integrable w) (hM : ∀ y, ‖w y‖ ≤ M) (hA : ∫ y, ‖w y‖ ≤ A) (n : ℕ) (x : R2) :
    ‖planarKernelVelocity (planarSmoothedBiotSavartKernel n) w x - planarKernelVelocity kernelK w x‖ ≤
      (8 * (M + A)) * logFlowModulus (planarVelocityApproxScale n) := by
  let φ := planarVelocityMollifier (planarVelocityApproxScale n) (planarVelocityApproxScale_pos n)
  have hφ : Integrable φ := planarVelocityMollifier_integrable _
  let v : ℝ → R2 → R2 := fun _ => planarKernelVelocity kernelK w
  have hv : Continuous (Function.uncurry v) := (uniformContinuous_planarBiotSavart hw hM).continuous.comp continuous_snd
  have hMb (t : ℝ) (z : R2) : ‖v t z‖ ≤ planarBiotSavartMassBound M A := norm_planarBiotSavart_le_massBound hw hM hA z
  have hM0 : 0 ≤ M := (norm_nonneg (w 0)).trans (hM 0)
  have hA0 : 0 ≤ A := (integral_nonneg (fun z => norm_nonneg (w z))).trans hA
  change ‖planarKernelVelocity (planarKernelVelocity kernelK φ) w x - planarKernelVelocity kernelK w x‖ ≤ _
  rw [planarBiotSavart_smoothing_convolution hφ hw hM x]
  exact norm_boundedVelocityMollification_sub_le hφ (planarVelocityMollifier_nonneg _)
    (planarVelocityMollifier_integral _) (fun z hz => planarVelocityMollifier_zero (planarVelocityApproxScale_pos n) hz)
    hv hMb (by positivity : 0 ≤ 8 * (M + A)) (planarVelocityApproxScale_pos n) (planarVelocityApproxScale_le_half n)
    (fun t a b hab => planarBiotSavart_logFlowModulus_le hw hM hA hab) 0 x

end Euler2D

end
