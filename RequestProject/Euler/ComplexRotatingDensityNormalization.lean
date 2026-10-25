module

public import RequestProject.Euler.PlanarVelocityRotatingNormalization
public import RequestProject.Euler.ReferenceResponse
public import RequestProject.Euler.ComplexSourceMomentBounds

/-! Exact support, mass, moment and velocity transformations of the
same complex volume source under the actual amplitude/length/rotation
normalization used by the finite Euler parent cell. -/

@[expose] public section

set_option maxHeartbeats 10000000
set_option maxRecDepth 6500

noncomputable section

open Complex Set MeasureTheory
open scoped ComplexConjugate

namespace Euler2D

def normalizedRotatingComplexDensity (A r θ : ℝ) (w : ℂ → ℝ) (z : ℂ) : ℝ :=
  A⁻¹ * w (r • (Complex.exp ((θ : ℂ) * I) * z))

theorem normalizedRotatingComplexDensity_eq_scaled_rotation (A r θ : ℝ) (w : ℂ → ℝ) :
    normalizedRotatingComplexDensity A r θ w = fun z =>
      scaledComplexDensity A⁻¹ r⁻¹ w (rotation (Circle.exp θ) z) := by
  funext z
  simp only [normalizedRotatingComplexDensity, scaledComplexDensity, inv_inv,
    rotation_apply, Circle.coe_exp]

theorem integrable_normalizedRotatingComplexDensity {w : ℂ → ℝ} (hw : Integrable w)
    (A θ : ℝ) {r : ℝ} (hr : 0 < r) : Integrable (normalizedRotatingComplexDensity A r θ w) := by
  rw [normalizedRotatingComplexDensity_eq_scaled_rotation]
  exact (rotation (Circle.exp θ)).measurePreserving.integrable_comp_of_integrable
    (integrable_scaledComplexDensity hw A⁻¹ (inv_ne_zero hr.ne'))

theorem integral_normalizedRotatingComplexDensity (A θ : ℝ) {r : ℝ} (hr : 0 < r) (w : ℂ → ℝ) :
    (∫ z, normalizedRotatingComplexDensity A r θ w z) = A⁻¹ * r⁻¹ ^ 2 * ∫ z, w z := by
  rw [normalizedRotatingComplexDensity_eq_scaled_rotation]
  rw [(rotation (Circle.exp θ)).measurePreserving.integral_comp
    (rotation (Circle.exp θ)).toHomeomorph.measurableEmbedding]
  exact integral_scaledComplexDensity A⁻¹ (inv_pos.mpr hr).le w

theorem integral_abs_normalizedRotatingComplexDensity {A r : ℝ} (hA : 0 < A) (hr : 0 < r)
    (θ : ℝ) (w : ℂ → ℝ) :
    (∫ z, |normalizedRotatingComplexDensity A r θ w z|) = A⁻¹ * r⁻¹ ^ 2 * ∫ z, |w z| := by
  let a := Circle.exp θ
  let v := scaledComplexDensity A⁻¹ r⁻¹ w
  have hrot := (rotation a).measurePreserving.integral_comp
    (rotation a).toHomeomorph.measurableEmbedding (fun z => |v z|)
  have hscaled := absMoment_scaledComplexDensity A⁻¹ (inv_pos.mpr hr) w 0
  calc
    _ = ∫ z, |v (rotation a z)| := by
      simp only [v, a, normalizedRotatingComplexDensity, scaledComplexDensity, inv_inv,
        rotation_apply, Circle.coe_exp]
    _ = ∫ z, |v z| := hrot
    _ = _ := by
      simpa only [v, pow_zero, one_mul, Nat.reduceAdd, abs_of_pos (inv_pos.mpr hA)] using hscaled

theorem normalizedRotatingComplexDensity_support {w : ℂ → ℝ} {S r : ℝ}
    (hsupp : ∀ z, S < ‖z‖ → w z = 0) (hr : 0 < r) (A θ : ℝ) :
    ∀ z, S / r < ‖z‖ → normalizedRotatingComplexDensity A r θ w z = 0 := by
  intro z hz
  unfold normalizedRotatingComplexDensity
  rw [hsupp, mul_zero]
  rw [norm_smul, Real.norm_of_nonneg hr.le, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
  simpa only [mul_comm] using (div_lt_iff₀ hr).mp hz

theorem normalizedRotatingComplexDensity_fourfold {w : ℂ → ℝ}
    (hsym : ∀ z, w (I * z) = w z) (A r θ : ℝ) (z : ℂ) :
    normalizedRotatingComplexDensity A r θ w (I * z) = normalizedRotatingComplexDensity A r θ w z := by
  simp only [normalizedRotatingComplexDensity, Complex.real_smul]
  rw [show (r : ℂ) * (Complex.exp ((θ : ℂ) * I) * (I * z)) =
    I * ((r : ℂ) * (Complex.exp ((θ : ℂ) * I) * z)) by ring, hsym]

theorem momentN_normalizedRotatingComplexDensity_fourth (A θ : ℝ) {r : ℝ} (hr : 0 < r)
    (w : ℂ → ℝ) :
    momentN (normalizedRotatingComplexDensity A r θ w) 4 =
      (A⁻¹ : ℂ) * (r⁻¹ : ℂ) ^ 6 * Complex.exp (4 * (θ : ℂ) * I) * momentN w 4 := by
  let v := scaledComplexDensity A⁻¹ r⁻¹ w
  have hrot : momentN (fun z => v (rotation (Circle.exp θ) z)) 4 =
      Complex.exp (4 * (θ : ℂ) * I) * momentN v 4 := by
    simpa only [momentN, rotation_apply, Circle.coe_exp, Complex.ofReal_neg,
      mul_neg, neg_mul, neg_neg, mul_comm] using fourth_moment_rotation v (-θ)
  rw [normalizedRotatingComplexDensity_eq_scaled_rotation, hrot,
    momentN_scaledComplexDensity A⁻¹ (inv_pos.mpr hr)]
  norm_num only [Nat.reduceAdd, Complex.ofReal_inv]
  ring

theorem velocityC_normalizedRotatingComplexDensity {A r : ℝ} (hA : 0 < A) (hr : 0 < r)
    (θ : ℝ) (w : ℂ → ℝ) (z : ℂ) :
    velocityC (normalizedRotatingComplexDensity A r θ w) z =
      Complex.exp (-((θ : ℂ) * I)) *
        ((A * r)⁻¹ • velocityC w (r • (Complex.exp ((θ : ℂ) * I) * z))) := by
  unfold normalizedRotatingComplexDensity
  simpa only [Circle.coe_exp, ← Complex.exp_neg] using
    (velocityC_normalized_rotation A hA.ne' hr (Circle.exp θ) w z).symm

end Euler2D

end
