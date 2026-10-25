module

public import RequestProject.Euler.CircularStableFourthGrowth
public import RequestProject.Euler.ContourFourfoldFourierSupport
public import RequestProject.Euler.CircularPeriodDerivativePowers

/-! Every genuine amplitude block on the original fourfold
unstable complement has the same polynomial growth bound. The forbidden
low modes vanish and the fourth normal block is the actual stable one. -/

@[expose] public section

set_option maxHeartbeats 1000000

noncomputable section

open Complex Set Filter Topology Metric
open scoped NNReal ContDiff

namespace Euler2D

local instance (priority := 2000) complementAmpLittle_group (γ : ℝ≥0) :
    NormedAddCommGroup (LittleContourSpace γ) := Submodule.normedAddCommGroup (LittleContourSpace γ)
local instance (priority := 2000) complementAmpLittle_space (γ : ℝ≥0) :
    NormedSpace ℝ (LittleContourSpace γ) := Submodule.normedSpace (LittleContourSpace γ)

theorem circularUnstableCoordinate_eq_ellPlus_amplitude {γ : ℝ≥0}
    (H : Fin 2 → LittleContourSpace γ) :
    circularUnstableCoordinateCLM γ H = ellPlus (circularModeAmplitudeCoefficientCLM γ 2 H).1 := by
  change circularEllPlusCLM (circularFourthNormalCoefficientCLM γ H) = _
  rw [circularEllPlusCLM_apply]
  rfl

theorem ellPlus_amplitude_zero_of_unstableProjection_zero {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : γ ≤ 1) (H : Fin 2 → LittleContourSpace γ)
    (hH : circularUnstableProjectionCLM hγ hγ1 H = 0) :
    ellPlus (circularModeAmplitudeCoefficientCLM γ 2 H).1 = 0 := by
  rw [← circularUnstableCoordinate_eq_ellPlus_amplitude]
  apply circularUnstableEmbeddingCLM_injective hγ hγ1
  exact hH.trans (circularUnstableEmbeddingCLM hγ hγ1).map_zero.symm

theorem norm_circularAmplitudeLinearFlow_fourfold_complement_le {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : γ ≤ 1) (H : Fin 2 → LittleContourSpace γ)
    (hfour : ∀ i, H i ∈ fourfoldLittleContourSubmodule γ)
    (hcomp : circularUnstableProjectionCLM hγ hγ1 H = 0)
    (N : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    ‖circularAmplitudeLinearFlow N (circularModeAmplitudeCoefficientCLM γ N H) t‖ ≤
      (4 + 8 * t) * ‖circularModeAmplitudeCoefficientCLM γ N H‖ := by
  by_cases hN2 : N = 2
  · subst N
    have h := norm_circularAmplitudeLinearFlow_fourth_complement_le
      (circularModeAmplitudeCoefficientCLM γ 2 H)
      (ellPlus_amplitude_zero_of_unstableProjection_zero hγ hγ1 H hcomp) ht
    exact h.trans (by nlinarith [norm_nonneg (circularModeAmplitudeCoefficientCLM γ 2 H)])
  · by_cases hN : N < 6
    · rw [circularModeAmplitudeCoefficient_low_fourfold_eq_zero H hfour hN hN2]
      change ‖NormedSpace.exp (t • circularAmplitudeGenerator N) 0‖ ≤ _
      rw [map_zero, norm_zero, mul_zero]
    · exact norm_circularAmplitudeLinearFlow_high_le (by omega) _ ht

theorem norm_circularPeriod_derivative_power_amplitude_complement_le {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1) {ρ : ℝ} (hρ : 0 < ρ)
    {X : (Fin 2 → LittleContourSpace γ) → ℝ → Fin 2 → LittleContourSpace γ}
    (hX : IsBanachFlowOn (circularBanachField hγ hγ1) (circularBanachDomain hγ hγ1)
      (ball (littleCircularReference hγ hγ1) ρ) period X)
    (hd : DifferentiableAt ℝ (fun W => X W period) (littleCircularReference hγ hγ1))
    (H : Fin 2 → LittleContourSpace γ)
    (hfour : ∀ i, H i ∈ fourfoldLittleContourSubmodule γ)
    (hcomp : circularUnstableProjectionCLM hγ hγ1.le H = 0) (N k : ℕ) :
    ‖circularModeAmplitudeCoefficientCLM γ N
        (((fderiv ℝ (fun W => X W period) (littleCircularReference hγ hγ1)) ^ k) H)‖ ≤
      (4 + 8 * ((k : ℝ) * period)) * (2 / cellA) * ‖H‖ := by
  rw [circularPeriod_derivative_power_mode_coordinates hγ hγ1 hρ hX hd]
  have ht : 0 ≤ (k : ℝ) * period := by unfold period; positivity
  have h := norm_circularAmplitudeLinearFlow_fourfold_complement_le hγ hγ1.le H hfour hcomp N ht
  exact h.trans (by
    have hb := mul_le_mul_of_nonneg_left (norm_circularModeAmplitudeCoefficient_le N H)
      (by positivity : (0 : ℝ) ≤ 4 + 8 * ((k : ℝ) * period))
    nlinarith)

end Euler2D

end
