module

public import RequestProject.Euler.PlanarVelocityPhysicalScaling
public import RequestProject.Euler.CircularFiniteContourDensity

/-! The physical velocity of a scaled active cell is exactly the
original isolated circular Banach field with its physical amplitude
and length factors. These are identities for the actual domains. -/

@[expose] public section

noncomputable section

open Complex Set
open scoped NNReal

namespace Euler2D

theorem velocityC_phaseFiniteContourPatchVorticity_scale
    {γ : ℝ≥0} {ι : Type*} [Fintype ι]
    (g : ι → ℝ) (Z : ι → ContourC1Space γ) (A : ℝ) {r : ℝ} (hr : 0 < r)
    (x : ℂ) :
    velocityC (phaseFiniteContourPatchVorticity (fun i => A * g i)
      (fun i => r • Z i)) (r • x) =
      (A * r) • velocityC (phaseFiniteContourPatchVorticity g Z) x := by
  have hd : phaseFiniteContourPatchVorticity (fun i => A * g i) (fun i => r • Z i) =
      scaledComplexDensity A r (phaseFiniteContourPatchVorticity g Z) :=
    funext (phaseFiniteContourPatchVorticity_scale g Z A hr.ne')
  rw [hd]
  exact velocityC_scaledComplexDensity A hr _ x

theorem circularPhysicalSelfVelocity_eq_scaled_field {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1)
    {Z : Fin 2 → LittleContourSpace γ} (hZ : Z ∈ circularQuarterPhaseDomain hγ hγ1)
    (A : ℝ) {r : ℝ} (hr : 0 < r) (i : Fin 2) (θ : ℝ) :
    velocityC (phaseFiniteContourPatchVorticity (fun j => A * circularContourStrengths j)
      (fun j => r • (Z j).val)) (r • LittleContourSpace.lift γ (Z i) θ) =
      (A * r) • LittleContourSpace.lift γ (circularBanachField hγ hγ1 Z i) θ := by
  rw [velocityC_phaseFiniteContourPatchVorticity_scale _ _ A hr]
  rw [circularBanachField_eq_actual_phase_velocity hγ hγ1 hZ]
  rfl

end Euler2D

end
