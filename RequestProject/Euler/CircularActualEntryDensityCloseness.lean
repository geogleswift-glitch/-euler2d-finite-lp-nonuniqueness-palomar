module

public import RequestProject.Euler.CircularPhasePatchL1Continuity
public import RequestProject.Euler.ContourPhaseComplexScale
public import RequestProject.Euler.CircularSinglePlanarLabelTransport
public import RequestProject.Euler.RotatingNormalizedFiniteParticleTransport

/-! The actual original single planar label, in its fixed entry frame,
is exactly the density of the actual normalized entry contours. Thus
geometric closeness to the same canonical ancient patch gives true L1
source closeness without a separate assumed analytic density bound. -/

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

theorem rotatingNormalized_finiteSinglePlanarLabel_eq_circularPhasePatch
    {s A₀ b R ρ : ℝ} (hA : 0 < A₀) (hb : 0 < b) (hR : 0 < R) (hρ : 0 < ρ)
    (N : ℕ) (j : Fin (N + 1)) {f : Lp ℝ 2 μT} {T t : ℝ}
    (S : BoundedEulerParticleSystem f T) (ht : t ∈ Icc (0 : ℝ) T) (θ : ℝ) (β : Fin 2 → ℝ)
    (W : Fin 2 → LittleContourSpace γ) (Zend : Fin 2 → ContourC1Space γ)
    (hscale : ∀ i, Zend i = radScale R ρ j •
      ContourC1Space.complexScale (Complex.exp ((θ : ℂ) * I)) (contourParameterShiftC1 (β i) (W i).val))
    (himages : ∀ i, S.forward t '' (complexTorusPoint '' contourRadialFill (ContourC1Space.lift γ
      (finiteCircularInitialContours hγ hγ1 R ρ (P.ancient s) N (j, i)).val)) =
        complexTorusPoint '' contourRadialFill (ContourC1Space.lift γ (Zend i))) (z : R2) :
    S.rotatingNormalizedPlanarLabelSource (P.finiteSinglePlanarInitialLabel s A₀ b R ρ N j)
      (ampScale A₀ b j) (radScale R ρ j) θ t z = circularPhasePatchPlanarVorticity W z := by
  have hAmp : 0 < ampScale A₀ b j := by unfold ampScale; positivity
  have hr := radScale_pos hR hρ (j : ℕ)
  have hx : centeredComplexHomeomorph.symm (radScale R ρ j • planarRigidRotation θ z + torusCenter) =
      radScale R ρ j • (Complex.exp ((θ : ℂ) * I) * complexPhysicalPlane.symm z) := by
    simp only [centeredComplexHomeomorph_symm_apply, add_sub_cancel_right, map_smul,
      planarRigidRotation_apply, LinearIsometryEquiv.symm_apply_apply]
  unfold BoundedEulerParticleSystem.rotatingNormalizedPlanarLabelSource
  rw [P.normalized_finiteSinglePlanarLabel_eq_phaseContours hR hρ N j S ht Zend himages, hx]
  rw [show Zend = (fun i => radScale R ρ j •
    ContourC1Space.complexScale (Complex.exp ((θ : ℂ) * I))
      (contourParameterShiftC1 (β i) (W i).val)) from funext hscale]
  change (ampScale A₀ b j)⁻¹ * phaseFiniteContourPatchVorticity
    (fun i => ampScale A₀ b j * circularContourStrengths i)
    (fun i => radScale R ρ j • ContourC1Space.complexScale (Complex.exp ((θ : ℂ) * I))
      (contourParameterShiftC1 (β i) (W i).val))
    (radScale R ρ j • (Complex.exp ((θ : ℂ) * I) * complexPhysicalPlane.symm z)) = _
  rw [phaseFiniteContourPatchVorticity_scale _ _ _ hr.ne', inv_smul_smul₀ hr.ne',
    phaseFiniteContourPatchVorticity_complexScale (Complex.exp_ne_zero _) _ _,
    inv_mul_cancel_left₀ (Complex.exp_ne_zero _), inv_mul_cancel_left₀ hAmp.ne']
  rw [phaseFiniteContourPatchVorticity_parameterShift]
  rfl

theorem exists_actual_rotating_entry_L1_neighborhood {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ {s A₀ b R ρ : ℝ}, (0 < A₀) → (0 < b) → (0 < R) → (0 < ρ) →
    ∀ (N : ℕ) (j : Fin (N + 1)) {f : Lp ℝ 2 μT} {T t : ℝ}
      (S : BoundedEulerParticleSystem f T), t ∈ Icc (0 : ℝ) T → ∀ (θ : ℝ) (β : Fin 2 → ℝ),
    ∀ (W : Fin 2 → LittleContourSpace γ) (Zend : Fin 2 → ContourC1Space γ),
    (∀ i, Zend i = radScale R ρ j •
      ContourC1Space.complexScale (Complex.exp ((θ : ℂ) * I)) (contourParameterShiftC1 (β i) (W i).val)) →
    (∀ i, S.forward t '' (complexTorusPoint '' contourRadialFill (ContourC1Space.lift γ
      (finiteCircularInitialContours hγ hγ1 R ρ (P.ancient s) N (j, i)).val)) =
        complexTorusPoint '' contourRadialFill (ContourC1Space.lift γ (Zend i))) →
    ‖W - P.ancient 0‖ < δ →
    (∫ z : R2, |S.rotatingNormalizedPlanarLabelSource
        (P.finiteSinglePlanarInitialLabel s A₀ b R ρ N j)
        (ampScale A₀ b j) (radScale R ρ j) θ t z -
      circularPhasePatchPlanarVorticity (P.ancient 0) z|) < ε := by
  obtain ⟨δ, hδ, hδspec⟩ := exists_circularPhasePatchPlanarVorticity_L1_neighborhood
    hγ hγ1 (P.ancient_domain 0 le_rfl) hε
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
