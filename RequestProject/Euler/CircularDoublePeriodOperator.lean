module

public import RequestProject.Euler.CircularFourierBlockMultiplier
public import RequestProject.Euler.CircularFourierCoefficientDecomposition
public import RequestProject.Euler.CircularDoublePeriodCoordinates

/-! The genuine double-period derivative equals the identity plus
an actual bounded Fourier smoothing operator and a remainder supported
only on the three omitted contour frequencies. -/

@[expose] public section

set_option maxHeartbeats 1000000

noncomputable section

open Set Filter Topology Metric NormedSpace
open scoped NNReal ContDiff

namespace Euler2D

local instance (priority := 2000) doubleOperatorLittle_group (γ : ℝ≥0) :
    NormedAddCommGroup (LittleContourSpace γ) := Submodule.normedAddCommGroup (LittleContourSpace γ)
local instance (priority := 2000) doubleOperatorLittle_space (γ : ℝ≥0) :
    NormedSpace ℝ (LittleContourSpace γ) := Submodule.normedSpace (LittleContourSpace γ)

theorem summable_circularFourierModeWeight_norm_of_geometric_bound (γ : ℝ≥0)
    {A : ℕ → CircularFourierAmplitudes →L[ℝ] CircularFourierAmplitudes}
    {r C : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (hC : 0 ≤ C)
    (hA : ∀ N, ‖A N‖ ≤ C * r ^ N) :
    Summable (fun N => circularFourierModeWeight γ N * ‖A N‖) := by
  apply ((summable_circularFourierModeWeight_geometric γ hr0 hr1).mul_left C).of_nonneg_of_le
    (fun N => mul_nonneg (circularFourierModeWeight_nonneg γ N) (norm_nonneg _))
  intro N
  calc
    _ ≤ circularFourierModeWeight γ N * (C * r ^ N) :=
      mul_le_mul_of_nonneg_left (hA N) (circularFourierModeWeight_nonneg γ N)
    _ = _ := by ring

def circularDoublePeriodRemainderSymbol (N : ℕ) :
    CircularFourierAmplitudes →L[ℝ] CircularFourierAmplitudes :=
  exp ((2 * period) • circularAmplitudeGenerator N) -
    ContinuousLinearMap.id ℝ CircularFourierAmplitudes

theorem summable_circularDoublePeriodRemainderSymbol (γ : ℝ≥0) :
    Summable (fun N => circularFourierModeWeight γ N * ‖circularDoublePeriodRemainderSymbol N‖) := by
  obtain ⟨C, hC, hbound⟩ := exists_norm_circularAmplitude_doublePeriod_sub_id_geometric_bound
  exact summable_circularFourierModeWeight_norm_of_geometric_bound γ cellA_pos.le cellA_lt_one hC.le hbound

def circularDoublePeriodFourierRemainderCLM {γ : ℝ≥0} (hγ : 0 < γ) (hγ1 : γ ≤ 1) :
    (Fin 2 → LittleContourSpace γ) →L[ℝ] (Fin 2 → LittleContourSpace γ) :=
  circularFourierBlockMultiplierCLM hγ hγ1 circularDoublePeriodRemainderSymbol

theorem circularModeAmplitudeCoefficient_doublePeriodFourierRemainder {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : γ ≤ 1) (H : Fin 2 → LittleContourSpace γ) (N : ℕ) :
    circularModeAmplitudeCoefficientCLM γ N (circularDoublePeriodFourierRemainderCLM hγ hγ1 H) =
      circularDoublePeriodRemainderSymbol N (circularModeAmplitudeCoefficientCLM γ N H) :=
  circularModeAmplitudeCoefficient_multiplier hγ hγ1 (summable_circularDoublePeriodRemainderSymbol γ) H N

theorem circularPeriod_derivative_square_remainder_supported_low {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1) {ρ : ℝ} (hρ : 0 < ρ)
    {X : (Fin 2 → LittleContourSpace γ) → ℝ → Fin 2 → LittleContourSpace γ}
    (hX : IsBanachFlowOn (circularBanachField hγ hγ1) (circularBanachDomain hγ hγ1)
      (ball (littleCircularReference hγ hγ1) ρ) period X)
    (hd : DifferentiableAt ℝ (fun W => X W period) (littleCircularReference hγ hγ1))
    (H : Fin 2 → LittleContourSpace γ) :
    fderiv ℝ (fun W => X W period) (littleCircularReference hγ hγ1)
        (fderiv ℝ (fun W => X W period) (littleCircularReference hγ hγ1) H) - H -
          circularDoublePeriodFourierRemainderCLM hγ hγ1.le H =
      circularLowFourierProjectionCLM hγ hγ1.le
        (fderiv ℝ (fun W => X W period) (littleCircularReference hγ hγ1)
          (fderiv ℝ (fun W => X W period) (littleCircularReference hγ hγ1) H) - H -
            circularDoublePeriodFourierRemainderCLM hγ hγ1.le H) := by
  apply circularLowFourierProjection_of_zero_amplitude hγ hγ1.le
  intro N
  rw [map_sub, circularPeriod_derivative_square_mode_coordinates hγ hγ1 hρ hX hd,
    circularModeAmplitudeCoefficient_doublePeriodFourierRemainder]
  exact sub_self _

theorem circularPeriod_derivative_square_operator_decomposition {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1) {ρ : ℝ} (hρ : 0 < ρ)
    {X : (Fin 2 → LittleContourSpace γ) → ℝ → Fin 2 → LittleContourSpace γ}
    (hX : IsBanachFlowOn (circularBanachField hγ hγ1) (circularBanachDomain hγ hγ1)
      (ball (littleCircularReference hγ hγ1) ρ) period X)
    (hd : DifferentiableAt ℝ (fun W => X W period) (littleCircularReference hγ hγ1)) :
    (fderiv ℝ (fun W => X W period) (littleCircularReference hγ hγ1)) ^ 2 =
      ContinuousLinearMap.id ℝ (Fin 2 → LittleContourSpace γ) +
        circularDoublePeriodFourierRemainderCLM hγ hγ1.le +
          (circularLowFourierProjectionCLM hγ hγ1.le).comp
            ((fderiv ℝ (fun W => X W period) (littleCircularReference hγ hγ1)) ^ 2 -
              ContinuousLinearMap.id ℝ (Fin 2 → LittleContourSpace γ) -
                circularDoublePeriodFourierRemainderCLM hγ hγ1.le) := by
  apply ContinuousLinearMap.ext
  intro H
  have he := circularPeriod_derivative_square_remainder_supported_low hγ hγ1 hρ hX hd H
  simp only [pow_two, ContinuousLinearMap.mul_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply]
  rw [← he]
  abel

end Euler2D

end
