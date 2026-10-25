module

public import RequestProject.Euler.ContourPhasePatchMoment
public import RequestProject.Euler.GlobalPlanarEulerTranslation
public import RequestProject.Euler.GlobalPlanarFourthMoment

/-! The actual material circular patch in every quarter-phase chart
has a genuine global positive-time planar continuation, with its
entire physical initial density and original fourth moment retained. -/

@[expose] public section

set_option maxHeartbeats 2500000

noncomputable section

open Complex Set Filter Topology MeasureTheory
open scoped NNReal

namespace Euler2D

def circularPhasePatchPlanarVorticity {γ : ℝ≥0} (Z : Fin 2 → LittleContourSpace γ) : R2 → ℝ :=
  fun x => circularPhasePatchVorticity Z (complexPhysicalPlane.symm x)

section Patch

variable {γ : ℝ≥0} (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1)
  {Z : Fin 2 → LittleContourSpace γ} (hZ : Z ∈ circularQuarterPhaseDomain hγ hγ1)

include hZ

theorem integrable_circularPhasePatchPlanarVorticity : Integrable (circularPhasePatchPlanarVorticity Z) :=
  complexPhysicalPlane.symm.measurePreserving.integrable_comp_of_integrable
    (integrable_circularPhasePatchVorticity hγ hγ1 hZ)

theorem norm_circularPhasePatchPlanarVorticity_le (x : R2) :
    ‖circularPhasePatchPlanarVorticity Z x‖ ≤ finiteContourPatchSupBound circularContourStrengths := by
  simpa only [circularPhasePatchPlanarVorticity, Real.norm_eq_abs] using
    abs_circularPhasePatchVorticity_le hγ hγ1 hZ (complexPhysicalPlane.symm x)

theorem norm_le_of_circularPhasePatchPlanarVorticity_ne_zero {x : R2}
    (hx : circularPhasePatchPlanarVorticity Z x ≠ 0) : ‖x‖ ≤ 5 / 4 := by
  have he := norm_le_of_circularPhasePatchVorticity_ne_zero hγ hγ1 hZ hx
  simpa only [LinearIsometryEquiv.norm_map] using he

theorem exists_circularPhasePatch_globalPlanarEuler :
    Nonempty (GlobalPlanarEulerParticleSystem (circularPhasePatchPlanarVorticity Z)) := by
  have hB : 0 ≤ finiteContourPatchSupBound circularContourStrengths :=
    Finset.sum_nonneg (fun i _ => abs_nonneg (circularContourStrengths i))
  apply exists_globalPlanarEulerParticleSystem_of_shifted_box
    (integrable_circularPhasePatchPlanarVorticity hγ hγ1 hZ) hB
    (norm_circularPhasePatchPlanarVorticity_le hγ hγ1 hZ) torusCenter
  intro x hx i
  have hb := norm_le_of_circularPhasePatchPlanarVorticity_ne_zero hγ hγ1 hZ hx
  have hi : |x i| ≤ 5 / 4 := (abs_coord_le x i).trans hb
  change 0 ≤ (x + torusCenter) i ∧ (x + torusCenter) i < 2 * Real.pi
  simp only [PiLp.add_apply, torusCenter_apply]
  constructor <;> linarith [Real.pi_gt_three, (abs_le.mp hi).1, (abs_le.mp hi).2]

theorem planarFourthMoment_circularPhasePatchPlanarVorticity :
    planarFourthMoment (circularPhasePatchPlanarVorticity Z) = circularBoundaryFourthMoment Z :=
  planarFourthMoment_circularPhasePatch hγ hγ1 hZ

end Patch

end Euler2D

end
