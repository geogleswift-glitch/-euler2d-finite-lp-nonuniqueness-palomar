module

public import RequestProject.Euler.ActualRotatingObservationStability

/-! The genuine rotating particle comparison only needs a concrete
Euler reference from a quarter-phase initial contour. This includes
the reference starting at a fixed negative canonical section, without
postulating a future C1 trajectory for the actual activated child. -/

@[expose] public section

set_option maxHeartbeats 7000000
set_option maxRecDepth 6500

noncomputable section

open Complex Set Filter Topology MeasureTheory Metric
open scoped NNReal ENNReal

namespace Euler2D

structure CircularPlanarParticleReference {γ : ℝ≥0} (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1) where
  initial : Fin 2 → LittleContourSpace γ
  initial_domain : initial ∈ circularQuarterPhaseDomain hγ hγ1
  positive : GlobalPlanarEulerParticleSystem (circularPhasePatchPlanarVorticity initial)

namespace CircularPlanarParticleReference

variable {γ : ℝ≥0} {hγ : 0 < γ} {hγ1 : (γ : ℝ) < 1}
    (R : CircularPlanarParticleReference hγ hγ1)

def positiveSpeedBound : ℝ :=
  planarBiotSavartMassBound (finiteContourPatchSupBound circularContourStrengths)
    (∫ x, ‖circularPhasePatchPlanarVorticity R.initial x‖)

theorem positive_norm_velocity_le (t : ℝ) (x : R2) :
    ‖R.positive.velocity t x‖ ≤ R.positiveSpeedBound :=
  R.positive.norm_velocity_le
    (integrable_circularPhasePatchPlanarVorticity hγ hγ1 R.initial_domain)
    (norm_circularPhasePatchPlanarVorticity_le hγ hγ1 R.initial_domain) t x

theorem positiveSpeedBound_nonneg : 0 ≤ R.positiveSpeedBound :=
  (norm_nonneg (R.positive.velocity 0 0)).trans (R.positive_norm_velocity_le 0 0)

def observationParticleRadius (D : ℝ) : ℝ :=
  5 / 4 + (finiteLabelAmplitudeBound + finiteLabelMassBound + 1) * D + 1 + R.positiveSpeedBound * D

theorem observationParticleRadius_nonneg {D : ℝ} (hD : 0 ≤ D) :
    0 ≤ R.observationParticleRadius D := by
  have hL := finiteLabelAmplitudeBound_nonneg
  have hM := finiteLabelMassBound_nonneg
  have hV := R.positiveSpeedBound_nonneg
  unfold observationParticleRadius
  positivity

theorem positive_velocity_eq_material {t : ℝ} (ht : 0 ≤ t) (x : R2) :
    R.positive.velocity t x = planarMaterialLabelVelocity kernelK
      (circularPhasePatchPlanarVorticity R.initial) (R.positive.homeomorph t ht) x := by
  rw [planarMaterialBiotSavart_eq_spatial _ _ (R.positive.forward_area t ht)]
  exact R.positive.selfconsistent t x

attribute [local irreducible] BoundedEulerParticleSystem.rotatingNormalizedRelativeParticleCurve
  BoundedEulerParticleSystem.rotatingNormalizedVelocityAt
  BoundedEulerParticleSystem.rotatingNormalizedPlanarLabelSource
  BoundedEulerParticleSystem.rotatingNormalizedRelativeHomeomorph
  planarMaterialLabelVelocity kernelK complexPhysicalPlane

theorem exists_actualRotating_particle_stability_of_source_error
    {D η : ℝ} (hD : 0 ≤ D) (hη : 0 < η) :
    ∃ δ > 0, ∃ ε > 0, ε ≤ 1 ∧
    ∀ {f : Lp ℝ 2 μT} {T : ℝ} (S : BoundedEulerParticleSystem f T)
      {M₀ : ℝ} (hM₀ : 0 ≤ M₀) (hfM : ∀ᵐ x ∂μT, ‖f x‖ ≤ M₀),
    ∀ (q₀ : R2 → ℝ) (A r entrance Ω θentry : ℝ) (hr : 0 < r)
      (he : entrance ∈ Icc (0 : ℝ) T)
      (hwindow : ∀ τ ∈ Icc (0 : ℝ) D, physicalTimeFromNormalized A entrance τ ∈ Icc (0 : ℝ) T),
    (∀ u ∈ Icc (0 : ℝ) T, MeasurePreserving (S.forward u) volume volume ∧
      MeasurePreserving (S.backward u) volume volume) →
    let w := S.rotatingNormalizedPlanarLabelSource q₀ A r θentry entrance
    Integrable w → (∀ z, ‖w z‖ ≤ finiteLabelAmplitudeBound) →
    (∫ z : R2, ‖w z‖) ≤ finiteLabelMassBound →
    (∀ z, w z ≠ 0 → ‖z‖ ≤ 5 / 4) →
    (∫ z : R2, ‖w z - circularPhasePatchPlanarVorticity R.initial z‖) < δ →
    (∀ (τ : ℝ) (hτ : τ ∈ Icc (0 : ℝ) D), ∀ z : R2, ‖z‖ ≤ R.observationParticleRadius D →
      ‖S.rotatingNormalizedVelocityAt A r Ω (physicalTimeFromNormalized A entrance τ)
          (θentry + (Ω / A) * τ) z -
        planarMaterialLabelVelocity kernelK w
          (S.rotatingNormalizedRelativeHomeomorph r hr.ne' entrance he
            (physicalTimeFromNormalized A entrance τ) (hwindow τ hτ) θentry (θentry + (Ω / A) * τ)) z‖ ≤ ε) →
    ∀ τ ∈ Icc (0 : ℝ) D, ∀ a : R2, ‖a‖ ≤ 5 / 4 →
      ‖S.rotatingNormalizedRelativeParticleCurve A r entrance Ω θentry a τ - R.positive.forward τ a‖ < η ∧
      ‖S.rotatingNormalizedRelativeParticleCurve A r entrance Ω θentry a τ‖ ≤ R.observationParticleRadius D ∧
      ‖R.positive.forward τ a‖ ≤ R.observationParticleRadius D := by
  let L := finiteLabelAmplitudeBound
  let M := finiteLabelMassBound
  let C := L + M + 1
  let B := R.observationParticleRadius D
  have hL : 0 ≤ L := finiteLabelAmplitudeBound_nonneg
  have hM : 0 ≤ M := finiteLabelMassBound_nonneg
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  have hV := R.positiveSpeedBound_nonneg
  have hB : 0 ≤ B := R.observationParticleRadius_nonneg hD
  have hBa : 5 / 4 + C * D + 1 ≤ B := by
    dsimp only [B, observationParticleRadius, C, L, M]
    nlinarith only [mul_nonneg hV hD]
  have hBp : 5 / 4 + R.positiveSpeedBound * D ≤ B := by
    change 5 / 4 + R.positiveSpeedBound * D ≤ 5 / 4 + C * D + 1 + R.positiveSpeedBound * D
    nlinarith only [mul_nonneg hC hD]
  obtain ⟨d, hd, hstable⟩ := planar_material_particle_stability_active
    (T := D) (B := L) (M := M) (H := 2 * B) hD hL hM (by positivity) hη
  obtain ⟨δ, hδ, hsource⟩ := exists_planar_source_L1_velocity_allowance (L := L) hd
  let ε := min 1 (d / 2)
  have hε : 0 < ε := lt_min zero_lt_one (half_pos hd)
  refine ⟨δ, hδ, ε, hε, min_le_left _ _, ?_⟩
  intro f T S M₀ hM₀ hfM q₀ A r entrance Ω θentry hr he hwindow harea
  dsimp only
  intro hw hwL hwM hsupport hclose herror
  let w := S.rotatingNormalizedPlanarLabelSource q₀ A r θentry entrance
  let fref := circularPhasePatchPlanarVorticity R.initial
  let X := fun τ a => S.rotatingNormalizedRelativeParticleCurve A r entrance Ω θentry a τ
  let Y := R.positive.forward
  let vx := fun τ a => S.rotatingNormalizedParticleVelocity A r entrance Ω θentry τ (X τ a)
  let vy := fun τ a => R.positive.velocity τ (Y τ a)
  let XH : Icc (0 : ℝ) D → R2 ≃ₜ R2 := fun τ =>
    S.rotatingNormalizedRelativeHomeomorph r hr.ne' entrance he
      (physicalTimeFromNormalized A entrance τ) (hwindow τ τ.property) θentry (θentry + (Ω / A) * τ)
  let YH : Icc (0 : ℝ) D → R2 ≃ₜ R2 := fun τ => R.positive.homeomorph τ τ.property.1
  have hXH (τ : Icc (0 : ℝ) D) : (XH τ : R2 → R2) = X τ := by
    funext a
    exact (S.rotatingNormalizedRelativeParticleCurve_eq_homeomorph A r entrance Ω θentry hr.ne' he a
      (hwindow τ τ.property)).symm
  have hYH (τ : Icc (0 : ℝ) D) : (YH τ : R2 → R2) = Y τ := rfl
  have hXmp (τ : Icc (0 : ℝ) D) : MeasurePreserving (XH τ) volume volume :=
    S.measurePreserving_rotatingNormalizedRelativeHomeomorph hr he (hwindow τ τ.property)
      (harea entrance he).2 (harea _ (hwindow τ τ.property)).1 _ _
  have hYmp (τ : Icc (0 : ℝ) D) : MeasurePreserving (YH τ) volume volume :=
    R.positive.forward_area τ τ.property.1
  have hfref : Integrable fref := integrable_circularPhasePatchPlanarVorticity hγ hγ1 R.initial_domain
  have hfrefL (z : R2) : ‖fref z‖ ≤ L :=
    (norm_circularPhasePatchPlanarVorticity_le hγ hγ1 R.initial_domain z).trans (le_max_right _ _)
  have hsource' : 2 * Real.sqrt (∫ z : R2, ‖w z - fref z‖) * Real.sqrt (2 * L) ≤ d / 2 :=
    hsource _ (integral_nonneg (fun z => norm_nonneg _)) hclose
  have hXradius : ∀ a : R2, ‖a‖ ≤ 5 / 4 → ∀ τ ∈ Icc (0 : ℝ) D, ‖X τ a‖ ≤ B := by
    intro a ha τ hτ
    have hh := S.rotatingNormalizedRelativeParticleCurve_bound_of_material_error q₀ A r entrance Ω θentry
      (R₀ := 5 / 4) (L := L) (M := M) (ε := 1) hr he hD (by norm_num) hwindow harea hw hwL hwM
      (by
        intro u hu z hz
        exact (herror u hu z (hz.trans hBa)).trans (min_le_left _ _)) a ha τ hτ
    have hcτ := mul_le_mul_of_nonneg_left hτ.2 hC
    exact hh.1.le.trans hBa
  have hYradius : ∀ a : R2, ‖a‖ ≤ 5 / 4 → ∀ τ ∈ Icc (0 : ℝ) D, ‖Y τ a‖ ≤ B := by
    intro a ha τ hτ
    have hh := R.positive.norm_forward_le R.positive_norm_velocity_le hτ.1 a
    have ht := mul_le_mul_of_nonneg_left hτ.2 hV
    exact hh.trans ((add_le_add ha ht).trans hBp)
  have hresult := hstable (w := w) (f := fref) hw hfref hwL hfrefL hwM hsource'
    (A := {a : R2 | ‖a‖ ≤ 5 / 4}) hsupport X Y vx vy XH YH hXH hYH hXmp hYmp
    (by
      intro a ha
      exact S.continuous_rotatingNormalized_curve_velocity A r entrance Ω θentry hM₀ hfM a)
    (by
      intro a ha
      exact R.positive.continuous_velocity.comp
        (continuous_id.prodMk (R.positive.continuous_forward.comp (continuous_id.prodMk continuous_const))))
    (by
      intro τ hτ a ha
      exact S.rotatingNormalizedRelativeParticleCurve_hasDerivAt_velocity A r entrance Ω θentry hr.ne' a (hwindow τ hτ))
    (by intro τ hτ a ha; exact R.positive.derivative τ hτ.1 a)
    (by
      intro a ha
      change ‖S.rotatingNormalizedRelativeParticleCurve A r entrance Ω θentry a 0 - R.positive.forward 0 a‖ ≤ d
      rw [S.rotatingNormalizedRelativeParticleCurve_initial A r entrance Ω θentry hr.ne' he, R.positive.initial,
        sub_self, norm_zero]
      exact hd.le)
    (by
      intro τ hτ a ha
      exact (norm_sub_le _ _).trans (by linarith only [hXradius a ha τ hτ, hYradius a ha τ hτ]))
    (by
      intro τ hτ a ha
      have he := herror τ hτ (X τ a) (hXradius a ha τ hτ)
      change ‖S.rotatingNormalizedVelocityAt A r Ω (physicalTimeFromNormalized A entrance τ)
        (θentry + (Ω / A) * τ) (X τ a) -
        planarMaterialLabelVelocity kernelK w (XH ⟨τ, hτ⟩) (X τ a)‖ ≤ ε at he
      rw [hXH] at he
      have hym : vy τ a = planarMaterialLabelVelocity kernelK fref (Y τ) (Y τ a) := by
        exact R.positive_velocity_eq_material hτ.1 (Y τ a)
      change ‖vx τ a - planarMaterialLabelVelocity kernelK w (X τ) (X τ a)‖ +
        ‖vy τ a - planarMaterialLabelVelocity kernelK fref (Y τ) (Y τ a)‖ ≤ d / 2
      rw [hym, sub_self, norm_zero, add_zero]
      simpa only [vx, BoundedEulerParticleSystem.rotatingNormalizedParticleVelocity_eq_velocityAt] using
        he.trans (min_le_right _ _))
  intro τ hτ a ha
  exact ⟨hresult τ hτ a ha, hXradius a ha τ hτ, hYradius a ha τ hτ⟩


end CircularPlanarParticleReference
end Euler2D

end

