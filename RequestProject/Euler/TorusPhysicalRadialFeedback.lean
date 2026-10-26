module

public import RequestProject.Euler.TorusPhysicalRadialComparison

/-! Transfer the proved actual planar radial feedback to the original
real Euler particle velocity, retaining the genuine torus correction. -/

@[expose] public section

set_option maxHeartbeats 2000000

noncomputable section

open Complex ComplexConjugate Set MeasureTheory Metric
open scoped NNReal ENNReal

namespace Euler2D

theorem real_inner_eq_complex_radial_product (u v : R2) :
    inner ℝ u v = (planeComplexEquiv v * conj (planeComplexEquiv u)).re := by
  have h := complexPhysicalPlane.symm.inner_map_map u v
  rw [real_inner_eq_re_inner, RCLike.inner_apply] at h
  simpa only [complexPhysicalPlane_symm_eq_planeComplexEquiv,
    RCLike.re_eq_complex_re] using h.symm

theorem exists_uniform_actualEuler_realRadial_feedback :
    ∃ K : ℝ, 0 < K ∧ ∀ {f : Lp ℝ 2 μT} {T : ℝ} (S : BoundedEulerParticleSystem f T),
      IsFourfoldBoundedEulerParticleSystem S → ∀ {w : R2 → ℝ} {M a t V L : ℝ},
      w =ᵐ[μT] (f : R2 → ℝ) → (∀ y, ‖w y‖ ≤ M) → IsTorusPeriodic w →
      (∀ y, w (torusQuarterTurn y) = w y) → (∫ y in torusBox, f y) = 0 →
      0 < a → a ≤ 1 / 16 → t ∈ Icc (0 : ℝ) T →
      (∀ y ∈ torusBox, a < ‖y - torusCenter‖ → S.transportedScalar w t y = 0) →
      ∀ x : ℂ, ‖x‖ ≤ a →
      (velocityC (S.physicalComplexSource w t) x * conj x).re ≤ ‖x‖ * (V + L * ‖x‖ ^ 3) →
      inner ℝ (complexTorusPoint x - torusCenter)
        (particleVelocityRepresentative f S.backward S.backward_area t (complexTorusPoint x)) ≤
      ‖x‖ * (V + (L + K * (∫ y : ℂ, ‖y‖ ^ 4 * |S.physicalComplexSource w t y|)) * ‖x‖ ^ 3) := by
  obtain ⟨K, hK, hbound⟩ := exists_uniform_actualEuler_radialCorrection_bound
  refine ⟨K, hK, ?_⟩
  intro f T S hS w M a t V L hwf hwM hwper hwrot hm ha ha16 ht hsupp x hx hp
  have hc := hbound S hS hwf hwM hwper hwrot hm ha ha16 ht hsupp x hx
  have hcoord : planeComplexEquiv (complexTorusPoint x - torusCenter) = x := by
    rw [← normalizedComplexCoordinate_one, normalizedComplexCoordinate_one_complexTorusPoint]
  rw [real_inner_eq_complex_radial_product, hcoord]
  calc
    _ = ((planeComplexEquiv
          (particleVelocityRepresentative f S.backward S.backward_area t (complexTorusPoint x)) -
        velocityC (S.physicalComplexSource w t) x) * conj x).re +
        (velocityC (S.physicalComplexSource w t) x * conj x).re := by
      rw [sub_mul, sub_re]
      ring
    _ ≤ K * ‖x‖ ^ 4 * (∫ y : ℂ, ‖y‖ ^ 4 * |S.physicalComplexSource w t y|) +
        ‖x‖ * (V + L * ‖x‖ ^ 3) := add_le_add ((le_abs_self _).trans hc) hp
    _ = _ := by ring

end Euler2D

end
