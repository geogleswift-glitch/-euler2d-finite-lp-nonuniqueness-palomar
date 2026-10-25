module

public import RequestProject.Euler.CircularActualAncientSectionObservation
public import RequestProject.Euler.CircularCoupledActualReferenceObservationMoment

/-! Literal transported moments of the SAME finite Euler hierarchy with
R=rho^10 and A0=cA*(1+xi), compared to the ORIGINAL reference/ancient
profile. Actual material geometry, areas and source identities are kept. -/

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 6500

noncomputable section

open Complex Set Filter Topology MeasureTheory Metric
open scoped NNReal ENNReal

namespace Euler2D
namespace CircularMaterialTransferProfile

variable {γ : ℝ≥0} {hγ : 0 < γ} {hγ1 : (γ : ℝ) < 1}
    (P : CircularMaterialTransferProfile hγ hγ1)

theorem exists_eventually_actualFinite_coupled_ancient_section_moment_close {sCanon : ℝ} (hsCanon : sCanon ≤ 0)
    {s cA b q T c C₀ K D η : ℝ} [Fact (1 ≤ ENNReal.ofReal q)]
    (hs : s ≤ 0) (hcA : 0 < cA) (hb : 0 < b) (hb1 : b ≤ 1)
    (hq : 0 < q) (hqE : 2 ≤ ENNReal.ofReal q) (hT : 0 ≤ T)
    (hc : 0 < c) (hC₀ : 0 < C₀) (hK : 0 ≤ K) (hD : 0 ≤ D) (hη : 0 < η) :
    ∃ δentry > 0, ∀ᶠ ξ : ℝ in atTop,
      let ρ := Real.exp (-ξ)
      let hρ := Real.exp_pos (-ξ)
      let R := ρ ^ 10
      let hR := pow_pos hρ 10
      let A₀ := cA * (1 + ξ)
      ∀ (N k : ℕ) (hkN : k ≤ N), ∀ S : BoundedEulerParticleSystem
        (finiteBaseCurlL2 (A₀ := A₀) (b := b) (ρ := ρ) hR hρ hq hqE
          (P.finiteBaseLp (A₀ := A₀) (b := b) (ρ := ρ) (q := q) hs hR hρ) N) T,
      IsFourfoldBoundedEulerParticleSystem S →
      (∀ u ∈ Icc (0 : ℝ) T, MeasurePreserving (S.forward u) volume volume ∧
        MeasurePreserving (S.backward u) volume volume) →
      ∀ entrance : ℝ, ∀ he : entrance ∈ Icc (0 : ℝ) T, ∀ (θentry : ℝ) (β : Fin 2 → ℝ),
      ∀ (W : Fin 2 → LittleContourSpace γ) (Zend : Fin 2 → ContourC1Space γ),
      (∀ i, Zend i = radScale R ρ k • ContourC1Space.complexScale (Complex.exp ((θentry : ℂ) * I))
        (contourParameterShiftC1 (β i) (W i).val)) →
      (∀ i, S.forward entrance '' (complexTorusPoint '' contourRadialFill (ContourC1Space.lift γ
        (finiteCircularInitialContours hγ hγ1 R ρ (P.ancient s) N (⟨k, Nat.lt_succ_of_le hkN⟩, i)).val)) =
          complexTorusPoint '' contourRadialFill (ContourC1Space.lift γ (Zend i))) →
      ‖W - (P.ancient sCanon)‖ < δentry →
      (∀ τ ∈ Icc (0 : ℝ) D,
        physicalTimeFromNormalized (ampScale A₀ b k) entrance τ ∈ Icc (0 : ℝ) T) →
      ∀ {δ : ℝ} (G : ∀ τ ∈ Icc (0 : ℝ) D, ∀ j : Fin k,
        P.FiniteOuterMaterialTube s R ρ N (finiteAncestorPointwiseIndex hkN j) S
          (physicalTimeFromNormalized (ampScale A₀ b k) entrance τ) c δ),
      (∀ τ hτ (j : Fin k) i,
        let l := finiteAncestorPointwiseIndex hkN j
        ‖contourParameterShiftC1 ((G τ hτ j).shifts (l, i)) ((G τ hτ j).contours (l, i)) -
          (G τ hτ j).reference (l, i)‖ ≤ radScale R ρ j * ((C₀ * ρ ^ 6) ^ (k - (j : ℕ)) * K)) →
      ∀ τ ∈ Icc (0 : ℝ) D,
        ‖planarFourthMoment (S.rotatingNormalizedPlanarLabelSource
            (P.finiteSinglePlanarInitialLabel s A₀ b R ρ N k) (ampScale A₀ b k) (radScale R ρ k)
            (θentry + (finiteAncestorAngularVelocity A₀ b k / ampScale A₀ b k) * τ)
            (physicalTimeFromNormalized (ampScale A₀ b k) entrance τ)) - P.moment (sCanon + τ)‖ < η ∧
        ‖momentN (fun z => P.finiteSinglePlanarInitialLabel s A₀ b R ρ N k
            (S.backward (physicalTimeFromNormalized (ampScale A₀ b k) entrance τ) (complexTorusPoint z))) 4 -
          (ampScale A₀ b k : ℂ) * (radScale R ρ k : ℂ) ^ 6 *
            Complex.exp (-(4 * ((θentry + (finiteAncestorAngularVelocity A₀ b k / ampScale A₀ b k) * τ : ℝ) : ℂ) * I)) *
            P.moment (sCanon + τ)‖ < ampScale A₀ b k * radScale R ρ k ^ 6 * η := by
  obtain ⟨Q, _hnegative, _hpositive, hmoment⟩ := P.exists_ancient_section_global_continuation hsCanon
  let Ref : CircularPlanarParticleReference hγ hγ1 :=
    ⟨P.ancient sCanon, P.ancient_domain sCanon hsCanon, Q⟩
  obtain ⟨δentry, hδentry, hξ⟩ :=
    P.exists_eventually_actualFinite_coupled_rotating_reference_moment_close Ref
      hs hcA hb hb1 hq hqE hT hc hC₀ hK hD hη
  refine ⟨δentry, hδentry, ?_⟩
  filter_upwards [hξ] with ξ hξ
  try dsimp only at hξ ⊢
  intro N k hkN S hS harea entrance he θentry β W Zend hscale himages hnear hwindow
    δ G hweighted τ hτ
  have hh := hξ N k hkN S hS harea entrance he θentry β W Zend hscale himages hnear hwindow
    G hweighted τ hτ
  simpa only [Ref, hmoment τ hτ.1] using hh

end CircularMaterialTransferProfile
end Euler2D

end
