module

public import RequestProject.Euler.ActualRotatingReferenceMomentStability
public import RequestProject.Euler.CircularActualReferenceEntryDensity
public import RequestProject.Euler.RotatingNormalizedPhysicalMoment

/-! The same original finite Euler label is compared with a concrete
Euler reference on a fixed observation window. Entry geometry yields
source closeness and true ancestor geometry yields the velocity error.
Future ancestor geometry remains an explicit construction obligation. -/

@[expose] public section

set_option maxHeartbeats 10000000
set_option maxRecDepth 6500

noncomputable section

open Complex Set Filter Topology MeasureTheory Metric
open scoped NNReal ENNReal

namespace Euler2D
namespace CircularMaterialTransferProfile

variable {γ : ℝ≥0} {hγ : 0 < γ} {hγ1 : (γ : ℝ) < 1}
    (P : CircularMaterialTransferProfile hγ hγ1)
    (Ref : CircularPlanarParticleReference hγ hγ1)

attribute [local irreducible] finiteBaseCurlL2 finiteBaseLp
  BoundedEulerParticleSystem.rotatingNormalizedRelativeParticleCurve
  BoundedEulerParticleSystem.rotatingNormalizedVelocityAt
  BoundedEulerParticleSystem.rotatingNormalizedPlanarLabelSource
  BoundedEulerParticleSystem.rotatingNormalizedRelativeHomeomorph
  planarMaterialLabelVelocity kernelK complexPhysicalPlane

theorem exists_eventually_actualFinite_rotating_reference_moment_close
    {s A₀ b q T c C₀ K D η : ℝ} [Fact (1 ≤ ENNReal.ofReal q)]
    (hs : s ≤ 0) (hA : 0 < A₀) (hb : 0 < b) (hb1 : b ≤ 1)
    (hq : 0 < q) (hqE : 2 ≤ ENNReal.ofReal q) (hT : 0 ≤ T)
    (hc : 0 < c) (hC₀ : 0 < C₀) (hK : 0 ≤ K) (hD : 0 ≤ D) (hη : 0 < η) :
    ∃ δentry > 0, ∀ᶠ ξ : ℝ in atTop,
      let ρ := Real.exp (-ξ)
      let hρ := Real.exp_pos (-ξ)
      ∀ (N k : ℕ) (hkN : k ≤ N), ∀ S : BoundedEulerParticleSystem
        (finiteBaseCurlL2 (A₀ := A₀) (b := b) (ρ := ρ) hρ hρ hq hqE
          (P.finiteBaseLp (A₀ := A₀) (b := b) (ρ := ρ) (q := q) hs hρ hρ) N) T,
      IsFourfoldBoundedEulerParticleSystem S →
      (∀ u ∈ Icc (0 : ℝ) T, MeasurePreserving (S.forward u) volume volume ∧
        MeasurePreserving (S.backward u) volume volume) →
      ∀ entrance : ℝ, ∀ he : entrance ∈ Icc (0 : ℝ) T, ∀ (θentry : ℝ) (β : Fin 2 → ℝ),
      ∀ (W : Fin 2 → LittleContourSpace γ) (Zend : Fin 2 → ContourC1Space γ),
      (∀ i, Zend i = radScale ρ ρ k • ContourC1Space.complexScale (Complex.exp ((θentry : ℂ) * I))
        (contourParameterShiftC1 (β i) (W i).val)) →
      (∀ i, S.forward entrance '' (complexTorusPoint '' contourRadialFill (ContourC1Space.lift γ
        (finiteCircularInitialContours hγ hγ1 ρ ρ (P.ancient s) N (⟨k, Nat.lt_succ_of_le hkN⟩, i)).val)) =
          complexTorusPoint '' contourRadialFill (ContourC1Space.lift γ (Zend i))) →
      ‖W - Ref.initial‖ < δentry →
      (∀ τ ∈ Icc (0 : ℝ) D,
        physicalTimeFromNormalized (ampScale A₀ b k) entrance τ ∈ Icc (0 : ℝ) T) →
      ∀ {δ : ℝ} (G : ∀ τ ∈ Icc (0 : ℝ) D, ∀ j : Fin k,
        P.FiniteOuterMaterialTube s ρ ρ N (finiteAncestorPointwiseIndex hkN j) S
          (physicalTimeFromNormalized (ampScale A₀ b k) entrance τ) c δ),
      (∀ τ hτ (j : Fin k) i,
        let l := finiteAncestorPointwiseIndex hkN j
        ‖contourParameterShiftC1 ((G τ hτ j).shifts (l, i)) ((G τ hτ j).contours (l, i)) -
          (G τ hτ j).reference (l, i)‖ ≤ radScale ρ ρ j * ((C₀ * ρ ^ 6) ^ (k - (j : ℕ)) * K)) →
      ∀ τ ∈ Icc (0 : ℝ) D,
        ‖planarFourthMoment (S.rotatingNormalizedPlanarLabelSource
            (P.finiteSinglePlanarInitialLabel s A₀ b ρ ρ N k) (ampScale A₀ b k) (radScale ρ ρ k)
            (θentry + (finiteAncestorAngularVelocity A₀ b k / ampScale A₀ b k) * τ)
            (physicalTimeFromNormalized (ampScale A₀ b k) entrance τ)) - planarFourthMoment (Ref.positive.vorticity τ)‖ < η ∧
        ‖momentN (fun z => P.finiteSinglePlanarInitialLabel s A₀ b ρ ρ N k
            (S.backward (physicalTimeFromNormalized (ampScale A₀ b k) entrance τ) (complexTorusPoint z))) 4 -
          (ampScale A₀ b k : ℂ) * (radScale ρ ρ k : ℂ) ^ 6 *
            Complex.exp (-(4 * ((θentry + (finiteAncestorAngularVelocity A₀ b k / ampScale A₀ b k) * τ : ℝ) : ℂ) * I)) *
            planarFourthMoment (Ref.positive.vorticity τ)‖ < ampScale A₀ b k * radScale ρ ρ k ^ 6 * η := by
  obtain ⟨δsource, hδsource, ε, hε, hε1, hmoment⟩ :=
    Ref.exists_actualRotating_moment_stability_of_source_error hD hη
  obtain ⟨δ₁, hδ₁, hentry⟩ := P.exists_actual_rotating_entry_L1_neighborhood_at Ref.initial_domain hδsource
  have hWnear : ∀ᶠ W in 𝓝 Ref.initial, W ∈ circularQuarterPhaseDomain hγ hγ1 :=
    (isOpen_circularQuarterPhaseDomain hγ hγ1).mem_nhds Ref.initial_domain
  obtain ⟨δ₂, hδ₂, hδ₂spec⟩ := Metric.eventually_nhds_iff.mp hWnear
  have herror := P.eventually_actualFinite_rotating_material_velocity_error_le
    (B := Ref.observationParticleRadius D) (ε := ε) hs hA hb hb1 hq hqE hT hc hC₀ hK
    (Ref.observationParticleRadius_nonneg hD) hε
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, ?_⟩
  filter_upwards [herror] with ξ hξ
  try dsimp only at hξ ⊢
  let ρ := Real.exp (-ξ)
  have hρ : 0 < ρ := Real.exp_pos (-ξ)
  intro N k hkN S hS harea entrance he θentry β W Zend hscale himages hnear hwindow δ G hweighted
  let j : Fin (N + 1) := ⟨k, Nat.lt_succ_of_le hkN⟩
  let q₀ := P.finiteSinglePlanarInitialLabel s A₀ b ρ ρ N k
  let A := ampScale A₀ b k
  let r := radScale ρ ρ k
  let Ω := finiteAncestorAngularVelocity A₀ b k
  let w := S.rotatingNormalizedPlanarLabelSource q₀ A r θentry entrance
  have hr : 0 < r := radScale_pos hρ hρ k
  have hW : W ∈ circularQuarterPhaseDomain hγ hγ1 := hδ₂spec (by
    simpa only [dist_eq_norm] using hnear.trans_le (min_le_right _ _))
  have hid : w = circularPhasePatchPlanarVorticity W := by
    funext z
    exact P.rotatingNormalized_finiteSinglePlanarLabel_eq_circularPhasePatch
      hA hb hρ hρ N j S he θentry β W Zend hscale himages z
  have hL1 : (∫ z : R2, ‖w z - circularPhasePatchPlanarVorticity Ref.initial z‖) < δsource := by
    simpa only [Real.norm_eq_abs] using
      hentry hA hb hρ hρ N j S he θentry β W Zend hscale himages (hnear.trans_le (min_le_left _ _))
  have hsupport (z : R2) (hz : w z ≠ 0) : ‖z‖ ≤ 5 / 4 := by
    rw [hid] at hz
    exact norm_le_of_circularPhasePatchPlanarVorticity_ne_zero hγ hγ1 hW hz
  obtain ⟨hw, hwL, hwM⟩ := P.rotatingNormalized_finiteSinglePlanarLabel_uniform_bounds
    hs hA hb hρ hρ N k S he (harea entrance he).1 θentry
  have hfM : ∀ᵐ x ∂μT,
      ‖(finiteBaseCurlL2 (A₀ := A₀) (b := b) (ρ := ρ) hρ hρ hq hqE
        (P.finiteBaseLp (A₀ := A₀) (b := b) (ρ := ρ) (q := q) hs hρ hρ) N) x‖ ≤
          finiteInitialDensityBound A₀ b N := by
    filter_upwards [P.finiteBaseCurlL2_ae_density (A₀ := A₀) (b := b) (ρ := ρ) hs hρ hρ hq hqE N] with x hx
    rw [hx]
    exact P.norm_finiteInitialPlanarDensity_le hs N _
  have hobs := hmoment S (finiteInitialDensityBound_nonneg A₀ b N) hfM q₀ A r entrance Ω θentry
    hr he hwindow harea hw hwL hwM hsupport hL1 (by
      intro τ hτ z hz
      exact hξ N k hkN S hS harea entrance _ he (hwindow τ hτ) (G τ hτ) (hweighted τ hτ) θentry _ z hz)
  intro τ hτ
  refine ⟨hobs τ hτ, ?_⟩
  have hAmp : 0 < A := by dsimp only [A, ampScale]; positivity
  exact S.singlePlanarMoment_close_of_rotatingNormalized_close q₀ hAmp hr
    (θentry + (Ω / A) * τ) (physicalTimeFromNormalized A entrance τ) (planarFourthMoment (Ref.positive.vorticity τ)) (hobs τ hτ)


end CircularMaterialTransferProfile
end Euler2D

end

