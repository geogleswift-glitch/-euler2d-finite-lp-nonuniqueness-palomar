module

public import RequestProject.Euler.ContourPhaseVorticity
public import RequestProject.Euler.CircularBoundaryFourthMoment
public import RequestProject.Euler.CircularFourierOperatorBounds

/-! The actual circular material patch on its entire quarter-phase
domain, with a fixed physical density independent of chart choice. -/

@[expose] public section

set_option maxHeartbeats 2500000

noncomputable section

open Complex Set Filter Topology MeasureTheory
open scoped NNReal

namespace Euler2D

local instance (priority := 2000) circularPhasePatchC1_group (γ : ℝ≥0) :
    NormedAddCommGroup (ContourC1Space γ) := Submodule.normedAddCommGroup (contourC1GraphSubmodule γ)
local instance (priority := 2000) circularPhasePatchC1_space (γ : ℝ≥0) :
    NormedSpace ℝ (ContourC1Space γ) := Submodule.normedSpace (contourC1GraphSubmodule γ)

def circularPhasePatchVorticity {γ : ℝ≥0} (Z : Fin 2 → LittleContourSpace γ) : ℂ → ℝ :=
  phaseFiniteContourPatchVorticity circularContourStrengths (fun i => (Z i).val)

theorem exists_circularQuarterPhase_shift {γ : ℝ≥0} (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1)
    {Z : Fin 2 → LittleContourSpace γ} (hZ : Z ∈ circularQuarterPhaseDomain hγ hγ1) :
    ∃ b : Fin 2 → ℝ, ∀ i, ‖contourParameterShiftC1 (b i) (Z i).val -
      circularReferenceC1 hγ hγ1 i‖ ≤ circularContourRadii i / 4 := by
  obtain ⟨b, hb⟩ := hZ.2
  exact ⟨-b, fun i => (hb i).le⟩

section Patch

variable {γ : ℝ≥0} (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1)
  {Z : Fin 2 → LittleContourSpace γ} (hZ : Z ∈ circularQuarterPhaseDomain hγ hγ1)

include hZ

theorem integrable_circularPhasePatchVorticity : Integrable (circularPhasePatchVorticity Z) := by
  obtain ⟨b, hb⟩ := exists_circularQuarterPhase_shift hγ hγ1 hZ
  exact integrable_phaseFiniteContourPatchVorticity circularContourStrengths (fun i => (Z i).val)
    (circularReferenceC1 hγ hγ1) circularContourRadii growingMoment_radius_pos
    (lift_circularReferenceC1 hγ hγ1) b hb

theorem abs_circularPhasePatchVorticity_le (x : ℂ) :
    |circularPhasePatchVorticity Z x| ≤ finiteContourPatchSupBound circularContourStrengths := by
  obtain ⟨b, hb⟩ := exists_circularQuarterPhase_shift hγ hγ1 hZ
  exact abs_phaseFiniteContourPatchVorticity_le circularContourStrengths (fun i => (Z i).val)
    (circularReferenceC1 hγ hγ1) circularContourRadii growingMoment_radius_pos
    (lift_circularReferenceC1 hγ hγ1) b hb x

theorem norm_le_of_circularPhasePatchVorticity_ne_zero {x : ℂ}
    (hx : circularPhasePatchVorticity Z x ≠ 0) : ‖x‖ ≤ 5 / 4 := by
  obtain ⟨b, hb⟩ := exists_circularQuarterPhase_shift hγ hγ1 hZ
  apply norm_le_of_phaseFiniteContourPatchVorticity_ne_zero circularContourStrengths (fun i => (Z i).val)
    (circularReferenceC1 hγ hγ1) circularContourRadii growingMoment_radius_pos
    (lift_circularReferenceC1 hγ hγ1) b hb _ hx
  intro i
  have hi := (circularContourRadii_bounds i).2.2
  linarith

theorem circularBanachField_eq_actual_phase_velocity (i : Fin 2) (θ : ℝ) :
    LittleContourSpace.lift γ (circularBanachField hγ hγ1 Z i) θ =
      velocityC (circularPhasePatchVorticity Z) (LittleContourSpace.lift γ (Z i) θ) := by
  obtain ⟨b, hb⟩ := exists_circularQuarterPhase_shift hγ hγ1 hZ
  rw [circularBanachField, lift_finiteContourPhaseFieldTotal hγ hγ1 _ _ _ _ _ Z hZ.1]
  exact contourBoundaryField_eq_phase_actual_velocity circularContourStrengths (fun i => (Z i).val)
    (circularReferenceC1 hγ hγ1) circularContourRadii growingMoment_radius_pos
    (lift_circularReferenceC1 hγ hγ1) b hb i θ

theorem circularBoundaryFourthMoment_eq_intrinsic_domains :
    circularBoundaryFourthMoment Z = ∑ i : Fin 2, (circularContourStrengths i : ℂ) *
      momentJ (contourRadialFill (LittleContourSpace.lift γ (Z i))) 4 := by
  obtain ⟨b, hb⟩ := exists_circularQuarterPhase_shift hγ hγ1 hZ
  unfold circularBoundaryFourthMoment
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  exact (momentJ_contourRadialFill_four_of_shift (Z i).val (circularReferenceC1 hγ hγ1 i)
    (growingMoment_radius_pos i) (lift_circularReferenceC1 hγ hγ1 i) (b i) (hb i)).symm

end Patch

end Euler2D

end
