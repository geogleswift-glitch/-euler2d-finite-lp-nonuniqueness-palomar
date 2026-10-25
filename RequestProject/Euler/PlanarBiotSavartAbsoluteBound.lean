module

public import RequestProject.Euler.PlanarBiotSavartIntegrability

/-! The actual absolute planar Biot--Savart integral, before any
vector cancellation, has a uniform bound. This provides the genuine
Fubini domination for compact regularization of the singular kernel. -/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology

namespace Euler2D

theorem integral_norm_planarBiotSavart_integrand_le {w : R2 → ℝ} {M : ℝ}
    (hw : Integrable w) (hM : ∀ y, ‖w y‖ ≤ M) (x : R2) :
    (∫ y, ‖w y • kernelK (x - y)‖) ≤ planarBiotSavartBound w M := by
  let K0 := planarExpandingKernelCutoff 0
  let c := (2 * Real.pi)⁻¹
  have hK (z : R2) : ‖kernelK z‖ ≤ ‖K0 z‖ + c := by
    calc
      _ ≤ ‖kernelK z - K0 z‖ + ‖K0 z‖ := norm_le_norm_sub_add _ _
      _ ≤ c + ‖K0 z‖ := add_le_add (by
        simpa only [Nat.cast_zero, zero_add, inv_one, mul_one] using norm_planarExpandingKernelCutoff_sub_le 0 z) le_rfl
      _ = _ := by ring
  have hnear : Integrable (fun y => M * ‖K0 (x - y)‖) :=
    (((integrable_planarExpandingKernelCutoff 0).comp_sub_left x).norm).const_mul M
  have hfar : Integrable (fun y => c * ‖w y‖) := hw.norm.const_mul c
  have hpoint (y : R2) : ‖w y • kernelK (x - y)‖ ≤ M * ‖K0 (x - y)‖ + c * ‖w y‖ := by
    rw [norm_smul]
    have he := mul_le_mul_of_nonneg_left (hK (x - y)) (norm_nonneg (w y))
    have hm := mul_le_mul_of_nonneg_right (hM y) (norm_nonneg (K0 (x - y)))
    nlinarith
  have htrans : (∫ y, ‖K0 (x - y)‖) = ∫ y, ‖K0 y‖ :=
    integral_sub_left_eq_self (μ := volume) (fun y => ‖K0 y‖) x
  calc
    _ ≤ ∫ y, M * ‖K0 (x - y)‖ + c * ‖w y‖ :=
      integral_mono (integrable_planarBiotSavart_integrand hw hM x).norm (hnear.add hfar) hpoint
    _ = _ := by rw [integral_add hnear hfar, integral_const_mul, integral_const_mul, htrans]; rfl

end Euler2D

end
