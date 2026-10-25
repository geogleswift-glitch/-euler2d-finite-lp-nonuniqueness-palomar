module

public import RequestProject.Euler.RotatingNormalizedFiniteParticleTransport
public import RequestProject.Euler.PlanarFourthMomentBounds
public import RequestProject.Euler.ComplexDensityScaling
public import RequestProject.Euler.ReferenceResponse

/-! Exact amplitude, length and rotation factors for the actual
conjugate fourth moment of the same single transported planar label. -/

@[expose] public section

set_option maxHeartbeats 5000000
set_option maxRecDepth 6500

noncomputable section

open Complex ComplexConjugate Set Filter Topology MeasureTheory
open scoped NNReal ENNReal

namespace Euler2D

theorem momentN_complexPhysicalPlane_fourth (w : R2 → ℝ) :
    momentN (fun z => w (complexPhysicalPlane z)) 4 = planarFourthMoment w := by
  have hh := complexPhysicalPlane.measurePreserving.integral_comp
    complexPhysicalPlane.toHomeomorph.measurableEmbedding (planarFourthMomentIntegrand w)
  simpa only [momentN, planarFourthMoment, planarFourthMomentIntegrand,
    LinearIsometryEquiv.symm_apply_apply] using hh

namespace BoundedEulerParticleSystem

variable {f : Lp ℝ 2 μT} {T : ℝ} (S : BoundedEulerParticleSystem f T)

theorem rotatingNormalizedPlanarLabelSource_complex_formula
    (q₀ : R2 → ℝ) (A r θ t : ℝ) (z : ℂ) :
    S.rotatingNormalizedPlanarLabelSource q₀ A r θ t (complexPhysicalPlane z) =
      A⁻¹ * q₀ (S.backward t (complexTorusPoint (r • (Complex.exp ((θ : ℂ) * I) * z)))) := by
  simp only [rotatingNormalizedPlanarLabelSource, normalizedPlanarLabelSource,
    planarRigidRotation_apply, LinearIsometryEquiv.symm_apply_apply, complexTorusPoint, map_smul]

theorem momentN_singlePlanar_eq_rotatingNormalizedFourthMoment
    (q₀ : R2 → ℝ) (A : ℝ) (hA : A ≠ 0) {r : ℝ} (hr : 0 < r) (θ t : ℝ) :
    momentN (fun z => q₀ (S.backward t (complexTorusPoint z))) 4 =
      (A : ℂ) * (r : ℂ) ^ 6 * Complex.exp (-(4 * (θ : ℂ) * I)) *
        planarFourthMoment (S.rotatingNormalizedPlanarLabelSource q₀ A r θ t) := by
  let w := S.rotatingNormalizedPlanarLabelSource q₀ A r θ t
  let F : ℂ → ℝ := fun z => w (complexPhysicalPlane z)
  let W : ℂ → ℝ := fun z => q₀ (S.backward t (complexTorusPoint z))
  have hphase : Complex.exp ((θ : ℂ) * I) * Complex.exp (-((θ : ℂ) * I)) = 1 := by
    rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero]
  have hcancel (z : ℂ) : r • (Complex.exp ((θ : ℂ) * I) *
      (Complex.exp (-((θ : ℂ) * I)) * (r⁻¹ • z))) = z := by
    rw [← mul_assoc, hphase, one_mul, smul_inv_smul₀ hr.ne']
  have hrec : scaledComplexDensity A r (fun z => F (Complex.exp (-((θ : ℂ) * I)) * z)) = W := by
    funext z
    dsimp only [scaledComplexDensity, F, w]
    rw [S.rotatingNormalizedPlanarLabelSource_complex_formula]
    rw [hcancel, ← mul_assoc, mul_inv_cancel₀ hA, one_mul]
  have hrot : momentN (fun z => F (Complex.exp (-((θ : ℂ) * I)) * z)) 4 =
      Complex.exp (-(4 * (θ : ℂ) * I)) * momentN F 4 := by
    simpa only [momentN, mul_comm] using fourth_moment_rotation F θ
  have hF : momentN F 4 = planarFourthMoment w := momentN_complexPhysicalPlane_fourth w
  change momentN W 4 = _
  rw [← hrec, momentN_scaledComplexDensity A hr, hrot, hF]
  norm_num only [Nat.reduceAdd]
  ring

theorem norm_singlePlanarMoment_sub_scaled_target
    (q₀ : R2 → ℝ) (A : ℝ) (hA : A ≠ 0) {r : ℝ} (hr : 0 < r) (θ t : ℝ) (N : ℂ) :
    ‖momentN (fun z => q₀ (S.backward t (complexTorusPoint z))) 4 -
        (A : ℂ) * (r : ℂ) ^ 6 * Complex.exp (-(4 * (θ : ℂ) * I)) * N‖ =
      |A| * r ^ 6 * ‖planarFourthMoment (S.rotatingNormalizedPlanarLabelSource q₀ A r θ t) - N‖ := by
  rw [S.momentN_singlePlanar_eq_rotatingNormalizedFourthMoment q₀ A hA hr θ t,
    ← mul_sub, norm_mul, norm_mul, norm_mul, norm_pow]
  have he : ‖Complex.exp (-(4 * (θ : ℂ) * I))‖ = 1 := by
    have harg : -(4 * (θ : ℂ) * I) = ((-(4 * θ) : ℝ) : ℂ) * I := by push_cast; ring
    rw [harg, Complex.norm_exp_ofReal_mul_I]
  simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr, he, mul_one]

theorem singlePlanarMoment_close_of_rotatingNormalized_close
    (q₀ : R2 → ℝ) {A r : ℝ} (hA : 0 < A) (hr : 0 < r) (θ t : ℝ) (N : ℂ) {η : ℝ}
    (hclose : ‖planarFourthMoment (S.rotatingNormalizedPlanarLabelSource q₀ A r θ t) - N‖ < η) :
    ‖momentN (fun z => q₀ (S.backward t (complexTorusPoint z))) 4 -
        (A : ℂ) * (r : ℂ) ^ 6 * Complex.exp (-(4 * (θ : ℂ) * I)) * N‖ < A * r ^ 6 * η := by
  rw [S.norm_singlePlanarMoment_sub_scaled_target q₀ A hA.ne' hr θ t N, abs_of_pos hA]
  exact mul_lt_mul_of_pos_left hclose (mul_pos hA (pow_pos hr 6))

end BoundedEulerParticleSystem
end Euler2D

end
