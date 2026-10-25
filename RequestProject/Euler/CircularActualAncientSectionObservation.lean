module

public import RequestProject.Euler.CircularActualReferenceObservationMoment
public import RequestProject.Euler.CircularAncientSectionContinuation

/-! Actual finite Euler observations on a window starting at a fixed
negative ancient section are compared with the original P.moment
throughout the negative and positive parts of that window. The future
ancestor material geometry is still required from the actual cascade. -/

@[expose] public section

set_option maxHeartbeats 16000000
set_option maxRecDepth 6500

noncomputable section

open Complex Set Filter Topology MeasureTheory Metric
open scoped NNReal ENNReal

namespace Euler2D
namespace CircularMaterialTransferProfile

variable {γ : ℝ≥0} {hγ : 0 < γ} {hγ1 : (γ : ℝ) < 1}
    (P : CircularMaterialTransferProfile hγ hγ1)

theorem exists_eventually_actualFinite_ancient_section_moment_close {sCanon : ℝ} (hsCanon : sCanon ≤ 0)
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
      ‖W - (P.ancient sCanon)‖ < δentry →
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
            (physicalTimeFromNormalized (ampScale A₀ b k) entrance τ)) - P.moment (sCanon + τ)‖ < η ∧
        ‖momentN (fun z => P.finiteSinglePlanarInitialLabel s A₀ b ρ ρ N k
            (S.backward (physicalTimeFromNormalized (ampScale A₀ b k) entrance τ) (complexTorusPoint z))) 4 -
          (ampScale A₀ b k : ℂ) * (radScale ρ ρ k : ℂ) ^ 6 *
            Complex.exp (-(4 * ((θentry + (finiteAncestorAngularVelocity A₀ b k / ampScale A₀ b k) * τ : ℝ) : ℂ) * I)) *
            P.moment (sCanon + τ)‖ < ampScale A₀ b k * radScale ρ ρ k ^ 6 * η := by
  obtain ⟨Q, _hnegative, _hpositive, hmoment⟩ := P.exists_ancient_section_global_continuation hsCanon
  let Ref : CircularPlanarParticleReference hγ hγ1 :=
    ⟨P.ancient sCanon, P.ancient_domain sCanon hsCanon, Q⟩
  obtain ⟨δentry, hδentry, hξ⟩ :=
    P.exists_eventually_actualFinite_rotating_reference_moment_close Ref
      hs hA hb hb1 hq hqE hT hc hC₀ hK hD hη
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
