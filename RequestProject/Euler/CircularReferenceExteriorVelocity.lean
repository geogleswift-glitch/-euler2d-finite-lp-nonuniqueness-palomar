module

public import RequestProject.Euler.CircularReferenceCoreVelocity

/-! The full exterior velocity of a zero-circulation circular
reference vanishes, as an identity of the actual singular integral. -/

@[expose] public section

set_option maxHeartbeats 2500000

noncomputable section

open Complex Set MeasureTheory Metric
open scoped NNReal

namespace Euler2D

theorem velocityC_circlePatch_outside {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : γ ≤ 1) {r : ℝ} (hr : 0 < r) {x : ℂ} (hx : r ≤ ‖x‖) :
    velocityC (circlePatchVorticity r) x =
      (r : ℂ) ^ 2 * ((I / 2) / (‖x‖ : ℂ) * exp ((x.arg : ℂ) * I)) := by
  rw [velocityC_circlePatch_eq_boundaryIntegral hγ hγ1 hr]
  have hn : 0 < ‖x‖ := hr.trans_le hx
  have hpolar : refCircle ‖x‖ x.arg = x := norm_mul_exp_arg_mul_I x
  rw [← hpolar, contourCircular_patchBoundaryVelocity hn hr x.arg,
    min_eq_right hx, max_eq_left hx]
  rw [hpolar]
  push_cast
  ring

theorem velocityC_finiteCircles_zero_outside {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : γ ≤ 1) {ι : Type*} [Fintype ι]
    (g r : ι → ℝ) (hr : ∀ i, 0 < r i)
    (hmass : ∑ i, g i * r i ^ 2 = 0) {x : ℂ} (hx : ∀ i, r i ≤ ‖x‖) :
    velocityC (fun y => ∑ i, g i * circlePatchVorticity (r i) y) x = 0 := by
  rw [velocityC_finite_sum_smul g (fun i => circlePatchVorticity (r i)) (fun _ => 1)
    (fun i => integrable_circlePatchVorticity (r i)) (fun i y => by
      by_cases hy : y ∈ ball (0 : ℂ) (r i) <;> simp [circlePatchVorticity, hy])]
  simp_rw [velocityC_circlePatch_outside hγ hγ1 (hr _) (hx _), ← mul_assoc]
  rw [← Finset.sum_mul]
  have hz : (∑ i, (g i : ℂ) * (r i : ℂ) ^ 2) = 0 := by
    exact_mod_cast hmass
  rw [← Finset.sum_mul, hz, zero_mul, zero_mul]

end Euler2D

end

