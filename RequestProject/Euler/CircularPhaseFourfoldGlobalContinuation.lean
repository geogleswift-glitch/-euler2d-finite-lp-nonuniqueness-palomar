module

public import RequestProject.Euler.OriginFourfoldPlanarEulerContinuation
public import RequestProject.Euler.CircularPhasePatchInvariants

/-! The actual fourfold physical circular patch has a genuine global
positive-time continuation whose forward and inverse maps retain the
same physical quarter-turn symmetry. -/

@[expose] public section

set_option maxHeartbeats 2500000

noncomputable section

open Complex Set Filter Topology MeasureTheory
open scoped NNReal

namespace Euler2D

theorem circularPhasePatchPlanarVorticity_fourfold {γ : ℝ≥0}
    (Z : Fin 2 → LittleContourSpace γ)
    (hfour : ∀ i, Z i ∈ fourfoldLittleContourSubmodule γ) (x : R2) :
    circularPhasePatchPlanarVorticity Z (perpJ x) = circularPhasePatchPlanarVorticity Z x := by
  have he : complexPhysicalPlane.symm (perpJ x) = I * complexPhysicalPlane.symm x := by
    apply complexPhysicalPlane.injective
    rw [LinearIsometryEquiv.apply_symm_apply, complexPhysicalPlane_mul_I,
      LinearIsometryEquiv.apply_symm_apply]
  simpa only [circularPhasePatchPlanarVorticity, he] using
    circularPhasePatchVorticity_fourfold Z hfour (complexPhysicalPlane.symm x)

theorem exists_circularPhasePatch_originFourfoldGlobalPlanarEuler {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1) {Z : Fin 2 → LittleContourSpace γ}
    (hZ : Z ∈ circularQuarterPhaseDomain hγ hγ1)
    (hfour : ∀ i, Z i ∈ fourfoldLittleContourSubmodule γ) :
    ∃ S : GlobalPlanarEulerParticleSystem (circularPhasePatchPlanarVorticity Z),
      IsOriginFourfoldGlobalPlanarEulerParticleSystem S := by
  have hB : 0 ≤ finiteContourPatchSupBound circularContourStrengths :=
    Finset.sum_nonneg (fun i _ => abs_nonneg (circularContourStrengths i))
  apply exists_originFourfoldGlobalPlanarEulerParticleSystem_of_shifted_box
    (integrable_circularPhasePatchPlanarVorticity hγ hγ1 hZ) hB
    (norm_circularPhasePatchPlanarVorticity_le hγ hγ1 hZ)
    (circularPhasePatchPlanarVorticity_fourfold Z hfour)
  intro x hx i
  have hb := norm_le_of_circularPhasePatchPlanarVorticity_ne_zero hγ hγ1 hZ hx
  have hi : |x i| ≤ 5 / 4 := (abs_coord_le x i).trans hb
  change 0 ≤ (x + torusCenter) i ∧ (x + torusCenter) i < 2 * Real.pi
  simp only [PiLp.add_apply, torusCenter_apply]
  constructor <;> linarith [Real.pi_gt_three, (abs_le.mp hi).1, (abs_le.mp hi).2]

end Euler2D

end
