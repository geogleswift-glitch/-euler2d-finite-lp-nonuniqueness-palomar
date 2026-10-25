module

public import RequestProject.Euler.ContourPhaseFiniteL1Continuity
public import RequestProject.Euler.CircularPhaseGlobalContinuation

/-! A genuine L1 neighborhood of any actual circular phase patch,
including the same canonical ancient entry used in the construction. -/

@[expose] public section

set_option maxHeartbeats 5000000
set_option maxRecDepth 6000

noncomputable section

open Complex Set Filter Topology MeasureTheory Metric
open scoped NNReal ENNReal

namespace Euler2D

theorem exists_circularPhasePatchVorticity_L1_neighborhood {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1)
    {W : Fin 2 → LittleContourSpace γ} (hW : W ∈ circularQuarterPhaseDomain hγ hγ1)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ Z : Fin 2 → LittleContourSpace γ, ‖Z - W‖ < δ →
      (∫ x : ℂ, |circularPhasePatchVorticity Z x - circularPhasePatchVorticity W x|) < ε := by
  obtain ⟨b, hb⟩ := hW.2
  obtain ⟨δ, hδ, hδspec⟩ := exists_phaseFiniteContourPatchVorticity_L1_neighborhood
    circularContourStrengths (fun i => (W i).val) (circularReferenceC1 hγ hγ1)
    circularContourRadii (-b) growingMoment_radius_pos (lift_circularReferenceC1 hγ hγ1)
    (fun i => hb i) hε
  refine ⟨δ, hδ, ?_⟩
  intro Z hZW
  apply hδspec (fun i => (Z i).val)
  have hnorm : ‖(fun i => (Z i).val) - (fun i => (W i).val)‖ ≤ ‖Z - W‖ := by
    apply (pi_norm_le_iff_of_nonneg (norm_nonneg (Z - W))).mpr
    intro i
    change ‖Z i - W i‖ ≤ ‖Z - W‖
    exact norm_le_pi_norm (Z - W) i
  exact hnorm.trans_lt hZW

theorem exists_circularPhasePatchPlanarVorticity_L1_neighborhood {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1)
    {W : Fin 2 → LittleContourSpace γ} (hW : W ∈ circularQuarterPhaseDomain hγ hγ1)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ Z : Fin 2 → LittleContourSpace γ, ‖Z - W‖ < δ →
      (∫ x : R2, |circularPhasePatchPlanarVorticity Z x - circularPhasePatchPlanarVorticity W x|) < ε := by
  obtain ⟨δ, hδ, hδspec⟩ := exists_circularPhasePatchVorticity_L1_neighborhood hγ hγ1 hW hε
  refine ⟨δ, hδ, ?_⟩
  intro Z hZW
  have he : (∫ x : R2, |circularPhasePatchPlanarVorticity Z x - circularPhasePatchPlanarVorticity W x|) =
      ∫ z : ℂ, |circularPhasePatchVorticity Z z - circularPhasePatchVorticity W z| := by
    have hcoord (x : R2) : complexPhysicalPlane.symm x = planeComplexEquiv x := by
      apply complexPhysicalPlane.injective
      rw [complexPhysicalPlane.apply_symm_apply, complexPhysicalPlane_eq_planeComplexEquiv_symm,
        planeComplexEquiv.symm_apply_apply]
    simpa only [circularPhasePatchPlanarVorticity, hcoord] using
      measurePreserving_planeComplexEquiv.integral_comp'
        (fun z => |circularPhasePatchVorticity Z z - circularPhasePatchVorticity W z|)
  rw [he]
  exact hδspec Z hZW

end Euler2D

end
