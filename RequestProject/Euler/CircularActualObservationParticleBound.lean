module

public import RequestProject.Euler.CircularActualRotatingMaterialDynamics
public import RequestProject.Euler.CircularNormalizedLabelUniformBounds
public import RequestProject.Euler.StoppedTrajectorySpeedBound

/-! The actual original rotating particles stay in a fixed ball over
a fixed observation window. The bound is obtained by a first-exit
argument using their literal material self velocity and actual small
Euler residual. No radius bound on the current particles is assumed. -/

@[expose] public section

set_option maxHeartbeats 12000000
set_option maxRecDepth 6500

noncomputable section

open Complex Set Filter Topology MeasureTheory
open scoped NNReal ENNReal

namespace Euler2D
namespace BoundedEulerParticleSystem

variable {f : Lp ℝ 2 μT} {T : ℝ} (S : BoundedEulerParticleSystem f T)

theorem rotatingNormalizedRelativeParticleCurve_initial
    (A r entrance Ω θentry : ℝ) (hr : r ≠ 0)
    (he : entrance ∈ Icc (0 : ℝ) T) (a : R2) :
    S.rotatingNormalizedRelativeParticleCurve A r entrance Ω θentry a 0 = a := by
  have ht0 : physicalTimeFromNormalized A entrance 0 ∈ Icc (0 : ℝ) T := by
    simpa only [physicalTimeFromNormalized, zero_div, add_zero] using he
  rw [S.rotatingNormalizedRelativeParticleCurve_eq_homeomorph A r entrance Ω θentry hr he a ht0]
  simp only [physicalTimeFromNormalized, zero_div, add_zero, mul_zero]
  exact S.rotatingNormalizedRelativeHomeomorph_entrance r hr entrance he θentry a

attribute [local irreducible] rotatingNormalizedRelativeParticleCurve rotatingNormalizedVelocityAt
  rotatingNormalizedPlanarLabelSource rotatingNormalizedRelativeHomeomorph
  planarMaterialLabelVelocity kernelK complexPhysicalPlane

theorem rotatingNormalizedRelativeParticleCurve_bound_of_material_error
    (q₀ : R2 → ℝ) (A r entrance Ω θentry : ℝ) {D R₀ L M ε : ℝ}
    (hr : 0 < r) (he : entrance ∈ Icc (0 : ℝ) T) (hD : 0 ≤ D) (hε : 0 ≤ ε)
    (hwindow : ∀ τ ∈ Icc (0 : ℝ) D, physicalTimeFromNormalized A entrance τ ∈ Icc (0 : ℝ) T)
    (harea : ∀ u ∈ Icc (0 : ℝ) T, MeasurePreserving (S.forward u) volume volume ∧
      MeasurePreserving (S.backward u) volume volume)
    (hw : Integrable (S.rotatingNormalizedPlanarLabelSource q₀ A r θentry entrance))
    (hL : ∀ z, ‖S.rotatingNormalizedPlanarLabelSource q₀ A r θentry entrance z‖ ≤ L)
    (hM : (∫ z : R2, ‖S.rotatingNormalizedPlanarLabelSource q₀ A r θentry entrance z‖) ≤ M)
    (herror : ∀ (τ : ℝ) (hτ : τ ∈ Icc (0 : ℝ) D), ∀ z : R2, ‖z‖ ≤ R₀ + (L + M + ε) * D + 1 →
      ‖S.rotatingNormalizedVelocityAt A r Ω (physicalTimeFromNormalized A entrance τ)
          (θentry + (Ω / A) * τ) z -
        planarMaterialLabelVelocity kernelK (S.rotatingNormalizedPlanarLabelSource q₀ A r θentry entrance)
          (S.rotatingNormalizedRelativeHomeomorph r hr.ne' entrance he
            (physicalTimeFromNormalized A entrance τ) (hwindow τ hτ) θentry (θentry + (Ω / A) * τ)) z‖ ≤ ε) :
    ∀ a : R2, ‖a‖ ≤ R₀ →
      let X := S.rotatingNormalizedRelativeParticleCurve A r entrance Ω θentry a
      ∀ τ ∈ Icc (0 : ℝ) D,
        ‖X τ‖ < R₀ + (L + M + ε) * D + 1 ∧
        ‖X τ - a‖ ≤ (L + M + ε) * τ ∧ ‖X τ‖ ≤ R₀ + (L + M + ε) * τ := by
  intro a ha
  dsimp only
  let C := L + M + ε
  let B := R₀ + C * D + 1
  let X := S.rotatingNormalizedRelativeParticleCurve A r entrance Ω θentry a
  let v := fun τ => S.rotatingNormalizedVelocityAt A r Ω (physicalTimeFromNormalized A entrance τ)
    (θentry + (Ω / A) * τ) (X τ)
  have hL0 : 0 ≤ L := (norm_nonneg _).trans (hL 0)
  have hM0 : 0 ≤ M := (integral_nonneg (fun z : R2 => norm_nonneg _)).trans hM
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  have hinit : X 0 = a := S.rotatingNormalizedRelativeParticleCurve_initial A r entrance Ω θentry hr.ne' he a
  have hXc : Continuous X :=
    (S.continuous_rotatingNormalizedRelativeParticleCurve A r entrance Ω θentry).comp
      (continuous_id.prodMk continuous_const)
  have hderiv (τ : ℝ) (hτ : τ ∈ Icc (0 : ℝ) D) (_hbound : ‖X τ‖ ≤ B) : HasDerivAt X (v τ) τ := by
    have hd := S.rotatingNormalizedRelativeParticleCurve_hasDerivAt_velocity A r entrance Ω θentry hr.ne' a
      (hwindow τ hτ)
    rw [S.rotatingNormalizedParticleVelocity_eq_velocityAt] at hd
    exact hd
  have hspeed (τ : ℝ) (hτ : τ ∈ Icc (0 : ℝ) D) (hbound : ‖X τ‖ ≤ B) : ‖v τ‖ ≤ C := by
    let t := physicalTimeFromNormalized A entrance τ
    have ht : t ∈ Icc (0 : ℝ) T := hwindow τ hτ
    let θ := θentry + (Ω / A) * τ
    let H := S.rotatingNormalizedRelativeHomeomorph r hr.ne' entrance he t ht θentry θ
    have hH : MeasurePreserving H volume volume :=
      S.measurePreserving_rotatingNormalizedRelativeHomeomorph hr he ht (harea entrance he).2 (harea t ht).1 θentry θ
    have herr := herror τ hτ (X τ) hbound
    have hself := norm_planarMaterialBiotSavart_le_sum hw hL H hH (X τ)
    have htri := norm_le_norm_sub_add (v τ) (planarMaterialLabelVelocity kernelK
      (S.rotatingNormalizedPlanarLabelSource q₀ A r θentry entrance) H (X τ))
    change ‖v τ - planarMaterialLabelVelocity kernelK
      (S.rotatingNormalizedPlanarLabelSource q₀ A r θentry entrance) H (X τ)‖ ≤ ε at herr
    dsimp only [C]
    linarith only [htri, herr, hself, hM]
  have hbounds := trajectory_bound_of_stopped_speed hD hC X v hXc.continuousOn
    (show ‖X 0‖ ≤ R₀ by rw [hinit]; exact ha)
    (show R₀ + C * D < B by dsimp only [B]; linarith) hderiv hspeed
  intro τ hτ
  simpa only [hinit] using hbounds τ hτ

end BoundedEulerParticleSystem

namespace CircularMaterialTransferProfile

variable {γ : ℝ≥0} {hγ : 0 < γ} {hγ1 : (γ : ℝ) < 1}
    (P : CircularMaterialTransferProfile hγ hγ1)

attribute [local irreducible] finiteBaseCurlL2 finiteBaseLp
  BoundedEulerParticleSystem.rotatingNormalizedRelativeParticleCurve
  BoundedEulerParticleSystem.rotatingNormalizedVelocityAt
  BoundedEulerParticleSystem.rotatingNormalizedPlanarLabelSource
  BoundedEulerParticleSystem.rotatingNormalizedRelativeHomeomorph
  planarMaterialLabelVelocity kernelK complexPhysicalPlane

theorem eventually_actualFinite_rotating_observation_particle_bound
    {s A₀ b q T c C₀ K D R₀ : ℝ} [Fact (1 ≤ ENNReal.ofReal q)]
    (hs : s ≤ 0) (hA : 0 < A₀) (hb : 0 < b) (hb1 : b ≤ 1)
    (hq : 0 < q) (hqE : 2 ≤ ENNReal.ofReal q) (hT : 0 ≤ T)
    (hc : 0 < c) (hC₀ : 0 < C₀) (hK : 0 ≤ K) (hD : 0 ≤ D) (hR₀ : 0 ≤ R₀) :
    let C := finiteLabelAmplitudeBound + finiteLabelMassBound + 1
    let B := R₀ + C * D + 1
    ∀ᶠ ξ : ℝ in atTop,
      let ρ := Real.exp (-ξ)
      let hρ := Real.exp_pos (-ξ)
      ∀ (N k : ℕ) (hkN : k ≤ N), ∀ S : BoundedEulerParticleSystem
        (finiteBaseCurlL2 (A₀ := A₀) (b := b) (ρ := ρ) hρ hρ hq hqE
          (P.finiteBaseLp (A₀ := A₀) (b := b) (ρ := ρ) (q := q) hs hρ hρ) N) T,
      IsFourfoldBoundedEulerParticleSystem S →
      (∀ u ∈ Icc (0 : ℝ) T, MeasurePreserving (S.forward u) volume volume ∧
        MeasurePreserving (S.backward u) volume volume) →
      ∀ entrance : ℝ, ∀ he : entrance ∈ Icc (0 : ℝ) T, ∀ θentry : ℝ,
      (∀ τ ∈ Icc (0 : ℝ) D,
        physicalTimeFromNormalized (ampScale A₀ b k) entrance τ ∈ Icc (0 : ℝ) T) →
      ∀ {δ : ℝ} (G : ∀ τ ∈ Icc (0 : ℝ) D, ∀ j : Fin k,
        P.FiniteOuterMaterialTube s ρ ρ N (finiteAncestorPointwiseIndex hkN j) S
          (physicalTimeFromNormalized (ampScale A₀ b k) entrance τ) c δ),
      (∀ τ hτ (j : Fin k) i,
        let l := finiteAncestorPointwiseIndex hkN j
        ‖contourParameterShiftC1 ((G τ hτ j).shifts (l, i)) ((G τ hτ j).contours (l, i)) -
          (G τ hτ j).reference (l, i)‖ ≤ radScale ρ ρ j * ((C₀ * ρ ^ 6) ^ (k - (j : ℕ)) * K)) →
      ∀ a : R2, ‖a‖ ≤ R₀ →
      let X := S.rotatingNormalizedRelativeParticleCurve (ampScale A₀ b k) (radScale ρ ρ k)
        entrance (finiteAncestorAngularVelocity A₀ b k) θentry a
      ∀ τ ∈ Icc (0 : ℝ) D,
        ‖X τ‖ < B ∧ ‖X τ - a‖ ≤ C * τ ∧ ‖X τ‖ ≤ R₀ + C * τ := by
  let C := finiteLabelAmplitudeBound + finiteLabelMassBound + 1
  let B := R₀ + C * D + 1
  have hC : 0 ≤ C := by
    dsimp only [C]
    linarith only [finiteLabelAmplitudeBound_nonneg, finiteLabelMassBound_nonneg]
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have herror := P.eventually_actualFinite_rotating_material_velocity_error_le
    (B := B) (ε := 1) hs hA hb hb1 hq hqE hT hc hC₀ hK hB (by norm_num)
  filter_upwards [herror] with ξ hξ
  try dsimp only at hξ ⊢
  let ρ := Real.exp (-ξ)
  have hρ : 0 < ρ := Real.exp_pos (-ξ)
  intro N k hkN S hS harea entrance he θentry hwindow δ G hweighted
  obtain ⟨hw, hL, hM⟩ := P.rotatingNormalized_finiteSinglePlanarLabel_uniform_bounds
    hs hA hb hρ hρ N k S he (harea entrance he).1 θentry
  apply S.rotatingNormalizedRelativeParticleCurve_bound_of_material_error
    (P.finiteSinglePlanarInitialLabel s A₀ b ρ ρ N k)
    (ampScale A₀ b k) (radScale ρ ρ k) entrance (finiteAncestorAngularVelocity A₀ b k) θentry
    (ε := 1) (radScale_pos hρ hρ k) he hD (by norm_num) hwindow harea hw hL hM
  intro τ hτ z hz
  exact hξ N k hkN S hS harea entrance _ he (hwindow τ hτ) (G τ hτ) (hweighted τ hτ) θentry _ z hz

end CircularMaterialTransferProfile
end Euler2D

end
