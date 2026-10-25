module

public import RequestProject.Euler.ActualRotatingReferenceParticleStability

/-! Fourth-moment stability for the same actual rotating label
against a genuine circular Euler reference. When the reference starts
at a negative ancient section, its moment is identified separately
with the literal translate of the original canonical moment. -/

@[expose] public section

set_option maxHeartbeats 7000000
set_option maxRecDepth 6500

noncomputable section

open Complex Set Filter Topology MeasureTheory
open scoped NNReal ENNReal

namespace Euler2D
namespace CircularPlanarParticleReference

variable {γ : ℝ≥0} {hγ : 0 < γ} {hγ1 : (γ : ℝ) < 1}
    (R : CircularPlanarParticleReference hγ hγ1)

attribute [local irreducible] BoundedEulerParticleSystem.rotatingNormalizedRelativeParticleCurve
  BoundedEulerParticleSystem.rotatingNormalizedVelocityAt
  BoundedEulerParticleSystem.rotatingNormalizedPlanarLabelSource
  BoundedEulerParticleSystem.rotatingNormalizedRelativeHomeomorph
  planarMaterialLabelVelocity kernelK complexPhysicalPlane

theorem exists_actualRotating_moment_stability_of_source_error
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
    ∀ τ ∈ Icc (0 : ℝ) D,
      ‖planarFourthMoment (S.rotatingNormalizedPlanarLabelSource q₀ A r (θentry + (Ω / A) * τ)
          (physicalTimeFromNormalized A entrance τ)) - planarFourthMoment (R.positive.vorticity τ)‖ < η := by
  let B := R.observationParticleRadius D
  let M := finiteLabelMassBound
  let c := 4 * B ^ 3 * M
  let ηp := η / (4 * (c + 1))
  let e₁ := η / (4 * (B ^ 4 + 1))
  have hB : 0 ≤ B := R.observationParticleRadius_nonneg hD
  have hM : 0 ≤ M := finiteLabelMassBound_nonneg
  have hc : 0 ≤ c := by dsimp only [c]; positivity
  have hηp : 0 < ηp := by dsimp only [ηp]; positivity
  have he₁ : 0 < e₁ := by dsimp only [e₁]; positivity
  obtain ⟨δp, hδp, ε, hε, hε1, hstable⟩ :=
    R.exists_actualRotating_particle_stability_of_source_error hD hηp
  refine ⟨min δp e₁, lt_min hδp he₁, ε, hε, hε1, ?_⟩
  intro f T S M₀ hM₀ hfM q₀ A r entrance Ω θentry hr he hwindow harea
  dsimp only
  intro hw hwL hwM hsupport hclose herror
  let w := S.rotatingNormalizedPlanarLabelSource q₀ A r θentry entrance
  let fref := circularPhasePatchPlanarVorticity R.initial
  have hparticles := hstable S hM₀ hfM q₀ A r entrance Ω θentry hr he hwindow harea
    hw hwL hwM hsupport (hclose.trans_le (min_le_left _ _)) herror
  have hfref : Integrable fref := integrable_circularPhasePatchPlanarVorticity hγ hγ1 R.initial_domain
  have hsupportBoth (a : R2) (ha : w a ≠ 0 ∨ fref a ≠ 0) : ‖a‖ ≤ 5 / 4 := by
    rcases ha with ha | ha
    · exact hsupport a ha
    · exact norm_le_of_circularPhasePatchPlanarVorticity_ne_zero hγ hγ1 R.initial_domain ha
  have hL1 : (∫ z : R2, ‖w z - fref z‖) ≤ e₁ := hclose.le.trans (min_le_right _ _)
  have hηpId : ηp * (4 * (c + 1)) = η := by
    dsimp only [ηp]
    exact div_mul_cancel₀ η (by positivity)
  have he₁Id : e₁ * (4 * (B ^ 4 + 1)) = η := by
    dsimp only [e₁]
    exact div_mul_cancel₀ η (by positivity)
  have hpTerm : (4 * B ^ 3 * ηp) * M ≤ η / 4 := by
    calc
      _ = c * ηp := by dsimp only [c]; ring
      _ ≤ η / 4 := by nlinarith only [hηpId, hηp.le]
  have hsTerm : B ^ 4 * e₁ ≤ η / 4 := by nlinarith only [he₁Id, he₁.le]
  intro τ hτ
  let t := physicalTimeFromNormalized A entrance τ
  have ht : t ∈ Icc (0 : ℝ) T := hwindow τ hτ
  let θ := θentry + (Ω / A) * τ
  let XH := S.rotatingNormalizedRelativeHomeomorph r hr.ne' entrance he t ht θentry θ
  let YH := R.positive.homeomorph τ hτ.1
  have hXeq (a : R2) : XH a = S.rotatingNormalizedRelativeParticleCurve A r entrance Ω θentry a τ :=
    (S.rotatingNormalizedRelativeParticleCurve_eq_homeomorph A r entrance Ω θentry hr.ne' he a ht).symm
  have hXmp : MeasurePreserving XH volume volume :=
    S.measurePreserving_rotatingNormalizedRelativeHomeomorph hr he ht (harea entrance he).2 (harea t ht).1 θentry θ
  have hYmp : MeasurePreserving YH volume volume := R.positive.forward_area τ hτ.1
  have hXR (a : R2) (ha : w a ≠ 0 ∨ fref a ≠ 0) : ‖XH a‖ ≤ B := by
    rw [hXeq]
    exact (hparticles τ hτ a (hsupportBoth a ha)).2.1
  have hYR (a : R2) (ha : w a ≠ 0 ∨ fref a ≠ 0) : ‖YH a‖ ≤ B :=
    (hparticles τ hτ a (hsupportBoth a ha)).2.2
  have hdist (a : R2) (ha : w a ≠ 0) : ‖XH a - YH a‖ ≤ ηp := by
    rw [hXeq]
    exact (hparticles τ hτ a (hsupport a ha)).1.le
  have hm := norm_planarFourthMoment_material_sub_le hw hfref hB hηp.le XH YH hXmp hYmp hXR hYR hdist
  have hactual : S.rotatingNormalizedPlanarLabelSource q₀ A r θ t = fun z => w (XH.symm z) := by
    funext z
    exact S.rotatingNormalizedPlanarLabelSource_transport q₀ A r hr.ne' entrance he t ht θentry θ z
  have hmodel : R.positive.vorticity τ = fun z => fref (YH.symm z) := rfl
  change ‖planarFourthMoment (S.rotatingNormalizedPlanarLabelSource q₀ A r θ t) - planarFourthMoment (R.positive.vorticity τ)‖ < η
  rw [hactual, hmodel]
  have hbound := hm.trans (add_le_add
    (mul_le_mul_of_nonneg_left hwM (show 0 ≤ 4 * B ^ 3 * ηp by positivity))
    (mul_le_mul_of_nonneg_left hL1 (pow_nonneg hB 4)))
  exact hbound.trans_lt (by linarith only [hpTerm, hsTerm, hη])


end CircularPlanarParticleReference
end Euler2D

end

