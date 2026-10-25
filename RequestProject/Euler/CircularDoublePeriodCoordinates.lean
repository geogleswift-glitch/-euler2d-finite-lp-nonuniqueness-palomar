module

public import RequestProject.Euler.CircularFourierCoordinates
public import RequestProject.Euler.CircularAmplitudeDoublePeriodEstimate

/-! The double-period amplitude remainder is the actual coefficient
of the squared genuine return derivative on every original perturbation. -/

@[expose] public section

set_option maxHeartbeats 1000000

noncomputable section

open Set Filter Topology Metric NormedSpace
open scoped NNReal ContDiff

namespace Euler2D

local instance (priority := 2000) doubleCoordLittle_group (γ : ℝ≥0) :
    NormedAddCommGroup (LittleContourSpace γ) := Submodule.normedAddCommGroup (LittleContourSpace γ)
local instance (priority := 2000) doubleCoordLittle_space (γ : ℝ≥0) :
    NormedSpace ℝ (LittleContourSpace γ) := Submodule.normedSpace (LittleContourSpace γ)

theorem circularAmplitudeLinearFlow_period_twice (N : ℕ) (p : CircularFourierAmplitudes) :
    circularAmplitudeLinearFlow N (circularAmplitudeLinearFlow N p period) period =
      exp ((2 * period) • circularAmplitudeGenerator N) p := by
  let A := circularAmplitudeGenerator N
  have he := exp_add_of_commute_of_mem_ball (𝕂 := ℝ) (Commute.refl (period • A))
    ((expSeries_radius_eq_top ℝ (CircularFourierAmplitudes →L[ℝ] CircularFourierAmplitudes)).symm ▸
      edist_lt_top _ _)
    ((expSeries_radius_eq_top ℝ (CircularFourierAmplitudes →L[ℝ] CircularFourierAmplitudes)).symm ▸
      edist_lt_top _ _)
  have hs : period • A + period • A = (2 * period) • A := by
    module
  change (exp (period • A) * exp (period • A)) p = _
  rw [← he, hs]

theorem circularPeriod_derivative_square_mode_coordinates {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1) {ρ : ℝ} (hρ : 0 < ρ)
    {X : (Fin 2 → LittleContourSpace γ) → ℝ → Fin 2 → LittleContourSpace γ}
    (hX : IsBanachFlowOn (circularBanachField hγ hγ1) (circularBanachDomain hγ hγ1)
      (ball (littleCircularReference hγ hγ1) ρ) period X)
    (hd : DifferentiableAt ℝ (fun W => X W period) (littleCircularReference hγ hγ1))
    (N : ℕ) (H : Fin 2 → LittleContourSpace γ) :
    circularModeAmplitudeCoefficientCLM γ N
      (fderiv ℝ (fun W => X W period) (littleCircularReference hγ hγ1)
        (fderiv ℝ (fun W => X W period) (littleCircularReference hγ hγ1) H) - H) =
      (exp ((2 * period) • circularAmplitudeGenerator N) -
        ContinuousLinearMap.id ℝ CircularFourierAmplitudes) (circularModeAmplitudeCoefficientCLM γ N H) := by
  let D := fderiv ℝ (fun W => X W period) (littleCircularReference hγ hγ1)
  let C := circularModeAmplitudeCoefficientCLM γ N
  have hc (G : Fin 2 → LittleContourSpace γ) :
      C (D G) = circularAmplitudeLinearFlow N (C G) period :=
    circularPeriod_derivative_all_mode_coordinates hγ hγ1 hρ hX hd N G
  change C (D (D H) - H) = _
  rw [map_sub, hc, hc, circularAmplitudeLinearFlow_period_twice]
  rfl

theorem exists_circularPeriod_derivative_square_mode_geometric_bound {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1) {ρ : ℝ} (hρ : 0 < ρ)
    {X : (Fin 2 → LittleContourSpace γ) → ℝ → Fin 2 → LittleContourSpace γ}
    (hX : IsBanachFlowOn (circularBanachField hγ hγ1) (circularBanachDomain hγ hγ1)
      (ball (littleCircularReference hγ hγ1) ρ) period X)
    (hd : DifferentiableAt ℝ (fun W => X W period) (littleCircularReference hγ hγ1)) :
    ∃ K > 0, ∀ (N : ℕ) (H : Fin 2 → LittleContourSpace γ),
      ‖circularModeAmplitudeCoefficientCLM γ N
        (fderiv ℝ (fun W => X W period) (littleCircularReference hγ hγ1)
          (fderiv ℝ (fun W => X W period) (littleCircularReference hγ hγ1) H) - H)‖ ≤
          K * cellA ^ N * ‖circularModeAmplitudeCoefficientCLM γ N H‖ := by
  obtain ⟨K, hK, hbound⟩ := exists_norm_circularAmplitude_doublePeriod_sub_id_geometric_bound
  refine ⟨K, hK, fun N H => ?_⟩
  rw [circularPeriod_derivative_square_mode_coordinates hγ hγ1 hρ hX hd]
  exact (ContinuousLinearMap.le_opNorm _ _).trans
    (mul_le_mul_of_nonneg_right (hbound N) (norm_nonneg _))

end Euler2D

end
