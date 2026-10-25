module

public import RequestProject.Euler.CircularActualEntryDensityCloseness

/-! Entry density closeness for an arbitrary fixed true circular
reference contour. The actual datum and its transported label are
the original finite Euler hierarchy. -/

@[expose] public section

set_option maxHeartbeats 8000000
set_option maxRecDepth 6500

noncomputable section

open Complex Set Filter Topology MeasureTheory
open scoped NNReal ENNReal

namespace Euler2D
namespace CircularMaterialTransferProfile

variable {γ : ℝ≥0} {hγ : 0 < γ} {hγ1 : (γ : ℝ) < 1}
    (P : CircularMaterialTransferProfile hγ hγ1)

theorem exists_actual_rotating_entry_L1_neighborhood_at
    {Zref : Fin 2 → LittleContourSpace γ}
    (hZref : Zref ∈ circularQuarterPhaseDomain hγ hγ1) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ {s A₀ b R ρ : ℝ}, (0 < A₀) → (0 < b) → (0 < R) → (0 < ρ) →
    ∀ (N : ℕ) (j : Fin (N + 1)) {f : Lp ℝ 2 μT} {T t : ℝ}
      (S : BoundedEulerParticleSystem f T), t ∈ Icc (0 : ℝ) T → ∀ (θ : ℝ) (β : Fin 2 → ℝ),
    ∀ (W : Fin 2 → LittleContourSpace γ) (Zend : Fin 2 → ContourC1Space γ),
    (∀ i, Zend i = radScale R ρ j •
      ContourC1Space.complexScale (Complex.exp ((θ : ℂ) * I)) (contourParameterShiftC1 (β i) (W i).val)) →
    (∀ i, S.forward t '' (complexTorusPoint '' contourRadialFill (ContourC1Space.lift γ
      (finiteCircularInitialContours hγ hγ1 R ρ (P.ancient s) N (j, i)).val)) =
        complexTorusPoint '' contourRadialFill (ContourC1Space.lift γ (Zend i))) →
    ‖W - Zref‖ < δ →
    (∫ z : R2, |S.rotatingNormalizedPlanarLabelSource
        (P.finiteSinglePlanarInitialLabel s A₀ b R ρ N j)
        (ampScale A₀ b j) (radScale R ρ j) θ t z -
      circularPhasePatchPlanarVorticity Zref z|) < ε := by
  obtain ⟨δ, hδ, hδspec⟩ := exists_circularPhasePatchPlanarVorticity_L1_neighborhood
    hγ hγ1 hZref hε
  refine ⟨δ, hδ, ?_⟩
  intro s A₀ b R ρ hA hb hR hρ N j f T t S ht θ β W Zend hscale himages hnear
  have he : S.rotatingNormalizedPlanarLabelSource (P.finiteSinglePlanarInitialLabel s A₀ b R ρ N j)
      (ampScale A₀ b j) (radScale R ρ j) θ t = circularPhasePatchPlanarVorticity W := by
    funext z
    exact P.rotatingNormalized_finiteSinglePlanarLabel_eq_circularPhasePatch
      hA hb hR hρ N j S ht θ β W Zend hscale himages z
  rw [he]
  exact hδspec W hnear

end CircularMaterialTransferProfile
end Euler2D

end
