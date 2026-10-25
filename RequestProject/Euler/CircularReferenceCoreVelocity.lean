module

public import RequestProject.Euler.ContourAnnularPerturbation
public import RequestProject.Euler.ContourCircularBoundaryVelocity
public import RequestProject.Euler.ContourSmoothEmbedding

/-! The full rigid velocity of a circular reference in its core, proved
from the actual Biot--Savart integral and the already computed circular
boundary integral. This is stronger than vanishing radial velocity. -/

@[expose] public section

set_option maxHeartbeats 2000000

noncomputable section

open Complex Set MeasureTheory Metric
open scoped NNReal

namespace Euler2D

theorem velocityC_circlePatch_eq_boundaryIntegral {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : γ ≤ 1) {r : ℝ} (hr : 0 < r) (x : ℂ) :
    velocityC (circlePatchVorticity r) x =
      (-1 / (2 * Real.pi) : ℂ) * contourLogBoundaryIntegral (refCircle r) (deriv (refCircle r)) x := by
  let Z : ContourC1Space γ := (littleReferenceCircle hγ hγ1 r).val
  have href : ContourC1Space.lift γ Z = refCircle r := lift_littleReferenceCircle hγ hγ1 r
  have hsmall : ‖Z - Z‖ ≤ r / 4 := by simp only [sub_self, norm_zero]; positivity
  have hD : contourC1EnclosedDomain Z Z hr href hsmall = ball (0 : ℂ) r := by
    apply Set.Subset.antisymm
    · simpa only [sub_self, norm_zero, add_zero] using
        contourC1EnclosedDomain_subset_ball Z Z hr href hsmall
    · simpa only [sub_self, norm_zero, sub_zero] using
        ball_subset_contourC1EnclosedDomain Z Z hr href hsmall
  have hf : contourC1PatchVorticity Z Z hr href hsmall = circlePatchVorticity r := by
    simp only [contourC1PatchVorticity, circlePatchVorticity, hD]
  simpa only [hf, href] using velocityC_contourC1PatchVorticity Z Z hr href hsmall x

theorem contourLogBoundaryIntegral_circle_at_zero {r : ℝ} (hr : 0 < r) :
    contourLogBoundaryIntegral (refCircle r) (deriv (refCircle r)) 0 = 0 := by
  unfold contourLogBoundaryIntegral
  simp_rw [zero_sub, norm_neg, norm_refCircle_actual, abs_of_pos hr, deriv_refCircle,
    Complex.real_smul]
  have he : (fun θ : ℝ => (Real.log r : ℂ) *
      ((r : ℂ) * (I * exp ((θ : ℂ) * I)))) =
      (fun θ : ℝ => ((Real.log r : ℂ) * (r : ℂ) * I) * contourCircleCharacter 1 θ) := by
    funext θ
    simp only [contourCircleCharacter, Int.cast_one, one_mul]
    ring
  rw [he, intervalIntegral.integral_const_mul, integral_contourCircleCharacter]
  norm_num

theorem velocityC_circlePatch_inside_core {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : γ ≤ 1) {r : ℝ} (hr : 0 < r) {x : ℂ} (hx : ‖x‖ ≤ r) :
    velocityC (circlePatchVorticity r) x = (I / 2) * x := by
  rw [velocityC_circlePatch_eq_boundaryIntegral hγ hγ1 hr]
  by_cases hz : x = 0
  · subst x
    rw [contourLogBoundaryIntegral_circle_at_zero hr]
    simp
  have hn : 0 < ‖x‖ := norm_pos_iff.mpr hz
  have hpolar : refCircle ‖x‖ x.arg = x := norm_mul_exp_arg_mul_I x
  rw [← hpolar, contourCircular_patchBoundaryVelocity hn hr x.arg,
    min_eq_left hx, max_eq_right hx]
  unfold refCircle
  push_cast
  have hrc : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  field_simp [hrc]
  <;> ring

theorem velocityC_finiteCircles_inside_core {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : γ ≤ 1) {ι : Type*} [Fintype ι]
    (g r : ι → ℝ) (hr : ∀ i, 0 < r i) {x : ℂ} (hx : ∀ i, ‖x‖ ≤ r i) :
    velocityC (fun y => ∑ i, g i * circlePatchVorticity (r i) y) x =
      ((∑ i, g i : ℝ) : ℂ) * (I / 2) * x := by
  rw [velocityC_finite_sum_smul g (fun i => circlePatchVorticity (r i)) (fun _ => 1)
    (fun i => integrable_circlePatchVorticity (r i)) (fun i y => by
      by_cases hy : y ∈ ball (0 : ℂ) (r i) <;> simp [circlePatchVorticity, hy])]
  simp_rw [velocityC_circlePatch_inside_core hγ hγ1 (hr _) (hx _)]
  rw [Complex.ofReal_sum, Finset.sum_mul, Finset.sum_mul]
  simp only [mul_assoc]

end Euler2D

end
