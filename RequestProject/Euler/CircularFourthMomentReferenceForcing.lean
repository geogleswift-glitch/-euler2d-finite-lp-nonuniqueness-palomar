module

public import RequestProject.Euler.CircularComplementAmplitudeBound

/-! The fourth-moment multipole field on the reference circles has
the actual growing Fourier coordinate Kstar times its moment. The
coordinate here is the bounded functional on the original contour
space, including the normal extraction and its radius factor. -/

@[expose] public section

set_option maxHeartbeats 6000000
set_option maxRecDepth 5500

noncomputable section

open Complex Set
open scoped NNReal ComplexConjugate

namespace Euler2D

local instance (priority := 2000) referenceForcingLittle_group (γ : ℝ≥0) :
    NormedAddCommGroup (LittleContourSpace γ) := Submodule.normedAddCommGroup (LittleContourSpace γ)
local instance (priority := 2000) referenceForcingLittle_space (γ : ℝ≥0) :
    NormedSpace ℝ (LittleContourSpace γ) := Submodule.normedSpace (LittleContourSpace γ)

def circularFourthMomentReferenceForcing {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : γ ≤ 1) (M : ℂ) : Fin 2 → LittleContourSpace γ :=
  fun i => littleContourFourierMode hγ hγ1 5
    (I / (2 * Real.pi) * ((circularContourRadii i : ℂ) ^ 5)⁻¹ * M)

theorem circularFourthMomentReferenceForcing_normal_coordinates {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : γ ≤ 1) (M : ℂ) :
    (circularModeAmplitudeCoefficientCLM γ 2 (circularFourthMomentReferenceForcing hγ hγ1 M)).1 =
      M • ![I / (2 * Real.pi) * (cellA : ℂ)⁻¹ ^ 6, I / (2 * Real.pi)] := by
  funext i
  change littleContourModeNormalCoefficientCLM γ (circularContourRadii i) 2
    (circularFourthMomentReferenceForcing hγ hγ1 M i) = _
  rw [littleContourModeNormalCoefficientCLM_apply]
  fin_cases i <;>
    norm_num [circularFourthMomentReferenceForcing, circularContourRadii,
      littleContourFourierCoefficient_fourierMode] <;>
    field_simp [cellA_ne] <;> ring

theorem circularFourthMomentReferenceForcing_growing_coordinate {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : γ ≤ 1) (M : ℂ) :
    circularUnstableCoordinateCLM γ (circularFourthMomentReferenceForcing hγ hγ1 M) = Kstar * M := by
  rw [circularUnstableCoordinate_eq_ellPlus_amplitude,
    circularFourthMomentReferenceForcing_normal_coordinates,
    ellPlus_complex_smul, ellPlus_forcing, mul_comm]

end Euler2D

end
