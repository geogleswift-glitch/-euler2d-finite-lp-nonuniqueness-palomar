module

public import RequestProject.Euler.TorusPhysicalCorrectionIdentity
public import RequestProject.Euler.LocalizedTorusCancellation

/-! The actual finite Euler velocity is its genuine boxed planar
velocity plus the original torus correction on the small physical
chart. The correction has a uniform cubic radial feedback constant;
an auxiliary source supremum is used only for integrability. -/

@[expose] public section

set_option maxHeartbeats 2400000

noncomputable section

open Complex ComplexConjugate Set MeasureTheory Metric
open scoped NNReal ENNReal

namespace Euler2D

theorem complexTorusPoint_normalizedComplexCoordinate_one (y : R2) :
    complexTorusPoint (normalizedComplexCoordinate 1 y) = y := by
  rw [complexTorusPoint, normalizedComplexCoordinate_one,
    ← complexPhysicalPlane_symm_eq_planeComplexEquiv, LinearIsometryEquiv.apply_symm_apply,
    sub_add_cancel]

theorem localizedComplexVorticity_boxedComplexDensity (w : R2 → ℝ) (y : R2) :
    localizedComplexVorticity (boxedComplexDensity w) y = torusBox.indicator w y := by
  rw [localizedComplexVorticity, boxedComplexDensity, complexTorusPoint_normalizedComplexCoordinate_one]

theorem torusKernelVelocity_localized_boxedComplexDensity (w : R2 → ℝ) (x : R2) :
    torusKernelVelocity (localizedComplexVorticity (boxedComplexDensity w)) x = torusKernelVelocity w x := by
  unfold torusKernelVelocity
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_torusBox] with y hy
  rw [localizedComplexVorticity_boxedComplexDensity, indicator_of_mem hy]

namespace BoundedEulerParticleSystem

variable {f : Lp ℝ 2 μT} {T : ℝ} (S : BoundedEulerParticleSystem f T)

theorem norm_physicalComplexSource_le {w : R2 → ℝ} {M : ℝ}
    (hwM : ∀ y, ‖w y‖ ≤ M) (t : ℝ) (z : ℂ) : ‖S.physicalComplexSource w t z‖ ≤ M := by
  have hM : 0 ≤ M := (norm_nonneg _).trans (hwM 0)
  by_cases hz : complexTorusPoint z ∈ torusBox
  · rw [physicalComplexSource, boxedComplexDensity, indicator_of_mem hz]
    exact hwM _
  · rw [physicalComplexSource, boxedComplexDensity, indicator_of_notMem hz, norm_zero]
    exact hM

/-- Literal pointwise decomposition of the actual Euler velocity;
the planar integral uses the entire same-S physical density. -/
theorem actualVelocity_eq_planar_add_physicalCorrection {w : R2 → ℝ} {M a : ℝ}
    (hwf : w =ᵐ[μT] (f : R2 → ℝ)) (hwM : ∀ y, ‖w y‖ ≤ M) (ha16 : a ≤ 1 / 16)
    {t : ℝ} (hsupp : ∀ y ∈ torusBox, a < ‖y - torusCenter‖ → S.transportedScalar w t y = 0)
    {x : ℂ} (hx : ‖x‖ ≤ a) :
    planeComplexEquiv (particleVelocityRepresentative f S.backward S.backward_area t (complexTorusPoint x)) =
      velocityC (S.physicalComplexSource w t) x + actualTorusCorrectionVelocity (S.physicalComplexSource w t) x := by
  rw [S.particleVelocityRepresentative_eq_raw w hwf,
    ← torusKernelVelocity_localized_boxedComplexDensity]
  exact torusKernelVelocity_localized_eq_planar_add_remainder ha16
    (S.integrable_physicalComplexSource hwf t) (S.norm_physicalComplexSource_le hwM t)
    (S.physicalComplexSource_support hsupp) hx

theorem actualVelocity_eq_planar_add_correctionLabelField {w : R2 → ℝ} {M a : ℝ}
    (hwf : w =ᵐ[μT] (f : R2 → ℝ)) (hwM : ∀ y, ‖w y‖ ≤ M) (ha16 : a ≤ 1 / 16)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T)
    (hsupp : ∀ y ∈ torusBox, a < ‖y - torusCenter‖ → S.transportedScalar w t y = 0)
    {x : ℂ} (hx : ‖x‖ ≤ a) :
    planeComplexEquiv (particleVelocityRepresentative f S.backward S.backward_area t (complexTorusPoint x)) =
      velocityC (S.physicalComplexSource w t) x + planeComplexEquiv (S.correctionLabelField t (complexTorusPoint x)) := by
  rw [S.actualVelocity_eq_planar_add_physicalCorrection hwf hwM ha16 hsupp hx,
    S.actualTorusCorrectionVelocity_physicalComplexSource hwf ht]

end BoundedEulerParticleSystem

/-- The constant is fixed before the source radius, particle system,
time, source amplitude, and finite cutoff. -/
theorem exists_uniform_actualEuler_radialCorrection_bound :
    ∃ K : ℝ, 0 < K ∧ ∀ {f : Lp ℝ 2 μT} {T : ℝ} (S : BoundedEulerParticleSystem f T),
      IsFourfoldBoundedEulerParticleSystem S → ∀ {w : R2 → ℝ} {M a t : ℝ},
      w =ᵐ[μT] (f : R2 → ℝ) → (∀ y, ‖w y‖ ≤ M) → IsTorusPeriodic w →
      (∀ y, w (torusQuarterTurn y) = w y) → (∫ y in torusBox, f y) = 0 →
      0 < a → a ≤ 1 / 16 → t ∈ Icc (0 : ℝ) T →
      (∀ y ∈ torusBox, a < ‖y - torusCenter‖ → S.transportedScalar w t y = 0) →
      ∀ x : ℂ, ‖x‖ ≤ a →
      |((planeComplexEquiv (particleVelocityRepresentative f S.backward S.backward_area t (complexTorusPoint x)) -
        velocityC (S.physicalComplexSource w t) x) * conj x).re| ≤
        K * ‖x‖ ^ 4 * ∫ y : ℂ, ‖y‖ ^ 4 * |S.physicalComplexSource w t y| := by
  obtain ⟨K, hK, hb⟩ := actual_torusRemainderVelocity_cancellation (a := (1 / 16 : ℝ))
    (by norm_num) (by norm_num)
  refine ⟨K, hK, ?_⟩
  intro f T S hS w M a t hwf hwM hwper hwrot hm ha ha16 ht hsupp x hx
  have hs := S.physicalComplexSource_support hsupp
  have hs0 : ∀ y : ℂ, (1 / 16 : ℝ) < ‖y‖ → S.physicalComplexSource w t y = 0 :=
    fun y hy => hs y (ha16.trans_lt hy)
  have hy := S.physicalComplexSource_fourfold hS hwper hwrot (by linarith) ht hsupp
  have hz : (∫ y : ℂ, S.physicalComplexSource w t y) = 0 :=
    (S.integral_physicalComplexSource hwf t).trans hm
  have hn := hb _ (S.integrable_physicalComplexSource hwf t) hs0 hy hz x (hx.trans ha16)
  rw [S.actualVelocity_eq_planar_add_physicalCorrection hwf hwM ha16 hsupp hx, add_sub_cancel_left]
  calc
    _ ≤ ‖actualTorusCorrectionVelocity (S.physicalComplexSource w t) x * conj x‖ := abs_re_le_norm _
    _ = ‖actualTorusCorrectionVelocity (S.physicalComplexSource w t) x‖ * ‖x‖ := by rw [norm_mul, norm_conj]
    _ ≤ (K * ‖x‖ ^ 3 * ∫ y : ℂ, ‖y‖ ^ 4 * |S.physicalComplexSource w t y|) * ‖x‖ :=
      mul_le_mul_of_nonneg_right hn (norm_nonneg _)
    _ = _ := by ring

end Euler2D

end
