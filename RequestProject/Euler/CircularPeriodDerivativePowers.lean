module

public import RequestProject.Euler.CircularDoublePeriodCoordinates
public import RequestProject.Euler.CircularAmplitudePerturbationGrowth

/-! Every actual return-derivative power has the true amplitude
exponential as its mode coordinate. High double-period powers have
arbitrarily small exponential growth after a fixed mode cutoff. -/

@[expose] public section

set_option maxHeartbeats 1000000

noncomputable section

open Set Filter Topology Metric NormedSpace
open scoped NNReal ContDiff

namespace Euler2D

local instance (priority := 2000) powerCoordLittle_group (γ : ℝ≥0) :
    NormedAddCommGroup (LittleContourSpace γ) := Submodule.normedAddCommGroup (LittleContourSpace γ)
local instance (priority := 2000) powerCoordLittle_space (γ : ℝ≥0) :
    NormedSpace ℝ (LittleContourSpace γ) := Submodule.normedSpace (LittleContourSpace γ)

theorem circularAmplitude_exponential_nat_multiple
    (A : CircularFourierAmplitudes →L[ℝ] CircularFourierAmplitudes) (t : ℝ) (n : ℕ) :
    exp (((n : ℝ) * t) • A) = exp (t • A) ^ n := by
  induction n with
  | zero =>
    rw [Nat.cast_zero, zero_mul, show (0 : ℝ) • A = 0 from _root_.zero_smul ℝ A,
      exp_zero, pow_zero]
  | succ n ih =>
    have hc : Commute (((n : ℝ) * t) • A) (t • A) := by
      apply ContinuousLinearMap.ext
      intro p
      change ((n : ℝ) * t) • A (t • A p) = t • A (((n : ℝ) * t) • A p)
      simp only [map_smul, smul_smul]
      congr 1
      ring
    have he := exp_add_of_commute_of_mem_ball (𝕂 := ℝ)
      hc
      ((expSeries_radius_eq_top ℝ (CircularFourierAmplitudes →L[ℝ] CircularFourierAmplitudes)).symm ▸
        edist_lt_top _ _)
      ((expSeries_radius_eq_top ℝ (CircularFourierAmplitudes →L[ℝ] CircularFourierAmplitudes)).symm ▸
        edist_lt_top _ _)
    have ha : (((n + 1 : ℕ) : ℝ) * t) • A = ((n : ℝ) * t) • A + t • A := by
      push_cast
      module
    rw [ha, he, ih, pow_succ]

theorem exp_circularUncoupledAmplitudeGenerator_double_period_multiple (N k : ℕ) :
    exp (((k : ℝ) * (2 * period)) • circularUncoupledAmplitudeGenerator N) =
      ContinuousLinearMap.id ℝ CircularFourierAmplitudes := by
  rw [circularAmplitude_exponential_nat_multiple,
    exp_circularUncoupledAmplitudeGenerator_double_period]
  exact one_pow k

theorem circularPeriod_derivative_power_mode_coordinates {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1) {ρ : ℝ} (hρ : 0 < ρ)
    {X : (Fin 2 → LittleContourSpace γ) → ℝ → Fin 2 → LittleContourSpace γ}
    (hX : IsBanachFlowOn (circularBanachField hγ hγ1) (circularBanachDomain hγ hγ1)
      (ball (littleCircularReference hγ hγ1) ρ) period X)
    (hd : DifferentiableAt ℝ (fun W => X W period) (littleCircularReference hγ hγ1))
    (N k : ℕ) (H : Fin 2 → LittleContourSpace γ) :
    circularModeAmplitudeCoefficientCLM γ N
        (((fderiv ℝ (fun W => X W period) (littleCircularReference hγ hγ1)) ^ k) H) =
      exp (((k : ℝ) * period) • circularAmplitudeGenerator N)
        (circularModeAmplitudeCoefficientCLM γ N H) := by
  let D := fderiv ℝ (fun W => X W period) (littleCircularReference hγ hγ1)
  let C := circularModeAmplitudeCoefficientCLM γ N
  let E := exp (period • circularAmplitudeGenerator N)
  have hc (G : Fin 2 → LittleContourSpace γ) : C (D G) = E (C G) :=
    circularPeriod_derivative_all_mode_coordinates hγ hγ1 hρ hX hd N G
  have hp : C ((D ^ k) H) = (E ^ k) (C H) := by
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [pow_succ', ContinuousLinearMap.mul_apply, hc, ih,
        pow_succ', ContinuousLinearMap.mul_apply]
  rw [circularAmplitude_exponential_nat_multiple]
  exact hp

theorem norm_circularAmplitude_double_period_power_sub_id_le (N k : ℕ) :
    ‖exp (((k : ℝ) * (2 * period)) • circularAmplitudeGenerator N) -
      ContinuousLinearMap.id ℝ CircularFourierAmplitudes‖ ≤
        ((135 / 4 : ℝ) * ((k : ℝ) * (2 * period)) * cellA ^ N) *
          Real.exp ((45 / 4 : ℝ) * ((k : ℝ) * (2 * period)) * cellA ^ N) := by
  have ht : 0 ≤ (k : ℝ) * (2 * period) := by unfold period; positivity
  have h := norm_circularAmplitude_exp_sub_uncoupled_le N ht
  rw [exp_circularUncoupledAmplitudeGenerator_double_period_multiple] at h
  exact h

theorem eventually_circularAmplitude_double_period_power_small_growth
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ k : ℕ,
      ‖exp (((k : ℝ) * (2 * period)) • circularAmplitudeGenerator N) -
        ContinuousLinearMap.id ℝ CircularFourierAmplitudes‖ ≤
          ((135 / 2 : ℝ) * period) * (k : ℝ) * cellA ^ N * Real.exp (ε * (k : ℝ)) := by
  have hp := tendsto_pow_atTop_nhds_zero_of_lt_one cellA_pos.le cellA_lt_one
  have hl : Tendsto (fun N : ℕ => ((45 / 2 : ℝ) * period) * cellA ^ N)
      atTop (𝓝 (0 : ℝ)) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul hp
  have he := hl.eventually (eventually_lt_nhds hε)
  filter_upwards [he] with N hN
  intro k
  have harg : (45 / 4 : ℝ) * ((k : ℝ) * (2 * period)) * cellA ^ N ≤ ε * (k : ℝ) := by
    calc
      _ = (((45 / 2 : ℝ) * period) * cellA ^ N) * (k : ℝ) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hN.le (Nat.cast_nonneg k)
  have hconst : 0 ≤ (135 / 4 : ℝ) * ((k : ℝ) * (2 * period)) * cellA ^ N := by
    have ha := cellA_pos
    unfold period
    positivity
  calc
    _ ≤ _ := norm_circularAmplitude_double_period_power_sub_id_le N k
    _ ≤ ((135 / 4 : ℝ) * ((k : ℝ) * (2 * period)) * cellA ^ N) * Real.exp (ε * (k : ℝ)) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr harg) hconst
    _ = _ := by ring

end Euler2D

end
