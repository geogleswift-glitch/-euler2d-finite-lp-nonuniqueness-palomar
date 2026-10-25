module

public import RequestProject.Euler.CircularActualMaterialForcedEquation
public import RequestProject.Euler.CircularCanonicalInitialState

/-! The actual parent coordinate starts at zero, and its physical
adjacent rotation has exactly the forcing frequency used by the
original retarded response. Both refer to the original canonical X. -/

@[expose] public section

set_option maxHeartbeats 9000000
set_option maxRecDepth 6500

noncomputable section

open Complex Set MeasureTheory
open scoped NNReal ENNReal

namespace Euler2D

attribute [local instance 2000] rigidGaugeLittle_group rigidGaugeLittle_space rigidGaugeFamily_tower
attribute [local instance] LittleContourSpace.complexScalarNormedSpace LittleContourSpace.complexScalarTower

theorem actualAdjacentPhase_from_parent_clock {A₀ b : ℝ}
    (hA : 0 < A₀) (hb : 0 < b) (k : ℕ) (t σ₀ τ χ : ℝ)
    (htime : physicalTimeFromNormalized (ampScale A₀ b k) 0 (σ₀ + b * τ) = t) :
    Complex.exp (4 * ((t * finiteAncestorAngularVelocity A₀ b k -
        (t * finiteAncestorAngularVelocity A₀ b (k + 1) + χ) : ℝ) : ℂ) * I) =
      Complex.exp (-((2 * σ₀ + 4 * χ : ℝ) : ℂ) * I) *
        Complex.exp (-((2 * b * τ : ℝ) : ℂ) * I) := by
  have hAmp : ampScale A₀ b k ≠ 0 := (div_pos hA (pow_pos hb k)).ne'
  have hAt : t * ampScale A₀ b k = σ₀ + b * τ := by
    exact ((div_eq_iff hAmp).mp (by simpa only [physicalTimeFromNormalized, zero_add] using htime)).symm
  have hreal : 4 * (t * finiteAncestorAngularVelocity A₀ b k -
      (t * (finiteAncestorAngularVelocity A₀ b k + ampScale A₀ b k / 2) + χ)) =
      -(2 * σ₀ + 4 * χ) - 2 * b * τ := by nlinarith only [hAt]
  rw [finiteAncestorAngularVelocity_succ, ← Complex.exp_add]
  congr 1
  have hh := congrArg (fun u : ℝ => (u : ℂ) * I) hreal
  push_cast at hh ⊢
  convert hh using 1 <;> ring

namespace CircularMaterialTransferProfile

variable {γ : ℝ≥0} {hγ : 0 < γ} {hγ1 : (γ : ℝ) < 1}
    (P : CircularMaterialTransferProfile hγ hγ1)

theorem actualCanonicalPrefix_initial_materialGrowing_zero
    {s A₀ b R ρ a Hglob D : ℝ} (hR : 0 < R) (hρ : 0 < ρ)
    {N k : ℕ} (hkN : k ≤ N) (hkchild : k + 1 ≤ N)
    {f : Lp ℝ 2 μT} {T : ℝ} (S : BoundedEulerParticleSystem f T)
    (X : ℝ → FiniteCircularIndex k → LittleContourSpace γ)
    (hX : P.ActualCanonicalPrefixTrajectory s A₀ b R ρ a Hglob hR hρ hkN S D X) :
    canonicalPrefixMaterialGrowingCoordinate hγ hγ1 A₀ b R ρ k X 0 = 0 := by
  have hi := P.actualCanonicalPrefix_initial_cell hR hρ hkN S X hX (Fin.last k)
  have hkne : k ≠ N := Nat.ne_of_lt (Nat.lt_of_succ_le hkchild)
  simp only [Fin.val_last, if_neg hkne] at hi
  unfold canonicalPrefixMaterialGrowingCoordinate canonicalPrefixMaterialCurrentCell
  simp only [mul_zero, neg_zero]
  rw [show (fun _ : Fin 2 => (0 : ℝ)) = (0 : Fin 2 → ℝ) from rfl]
  rw [contourParameterShiftFamilyCLM_zero, hi, sub_self, map_zero]

end CircularMaterialTransferProfile
end Euler2D

end
