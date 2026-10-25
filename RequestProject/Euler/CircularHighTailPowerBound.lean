module

public import RequestProject.Euler.CircularFourierOperatorTail
public import RequestProject.Euler.CircularLowProjectionCalculus

/-! The actual high-frequency kernel is invariant under the true
period derivative. Its even powers grow at an arbitrarily small
exponential rate, in the unchanged Banach norm. -/

@[expose] public section

set_option maxHeartbeats 1000000

noncomputable section

open Set Filter Topology Metric
open scoped NNReal ContDiff

namespace Euler2D

local instance (priority := 2000) highTailLittle_group (γ : ℝ≥0) :
    NormedAddCommGroup (LittleContourSpace γ) := Submodule.normedAddCommGroup (LittleContourSpace γ)
local instance (priority := 2000) highTailLittle_space (γ : ℝ≥0) :
    NormedSpace ℝ (LittleContourSpace γ) := Submodule.normedSpace (LittleContourSpace γ)

def circularHighModeSubmodule {γ : ℝ≥0} (hγ : 0 < γ) (hγ1 : γ ≤ 1) (L : ℕ) :
    Submodule ℝ (Fin 2 → LittleContourSpace γ) :=
  (circularLowFourierProjectionCLM hγ hγ1).ker ⊓
    ⨅ n : Fin L, (circularModeAmplitudeCoefficientCLM γ n.val).ker

theorem mem_circularHighModeSubmodule {γ : ℝ≥0} (hγ : 0 < γ) (hγ1 : γ ≤ 1)
    (L : ℕ) (H : Fin 2 → LittleContourSpace γ) :
    H ∈ circularHighModeSubmodule hγ hγ1 L ↔
      circularLowFourierProjectionCLM hγ hγ1 H = 0 ∧
        ∀ N < L, circularModeAmplitudeCoefficientCLM γ N H = 0 := by
  simp only [circularHighModeSubmodule, Submodule.mem_inf, Submodule.mem_iInf]
  change (circularLowFourierProjectionCLM hγ hγ1 H = 0 ∧
    ∀ n : Fin L, circularModeAmplitudeCoefficientCLM γ n.val H = 0) ↔ _
  constructor
  · intro h
    exact ⟨h.1, fun N hN => h.2 ⟨N, hN⟩⟩
  · intro h
    exact ⟨h.1, fun N => h.2 N.val N.isLt⟩

attribute [local irreducible] circularHighModeSubmodule

section ActualDerivative

variable {γ : ℝ≥0} (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1) {ρ : ℝ} (hρ : 0 < ρ)
variable {X : (Fin 2 → LittleContourSpace γ) → ℝ → Fin 2 → LittleContourSpace γ}
variable (hX : IsBanachFlowOn (circularBanachField hγ hγ1) (circularBanachDomain hγ hγ1)
  (ball (littleCircularReference hγ hγ1) ρ) period X)
variable (hd : DifferentiableAt ℝ (fun W => X W period) (littleCircularReference hγ hγ1))

include hρ hX hd

theorem circularPeriod_derivative_highMode_invariant (L : ℕ)
    {H : Fin 2 → LittleContourSpace γ} (hH : H ∈ circularHighModeSubmodule hγ hγ1.le L) :
    fderiv ℝ (fun W => X W period) (littleCircularReference hγ hγ1) H ∈
      circularHighModeSubmodule hγ hγ1.le L := by
  have hv := (mem_circularHighModeSubmodule hγ hγ1.le L H).mp hH
  apply (mem_circularHighModeSubmodule hγ hγ1.le L _).mpr
  constructor
  · have he := congrArg (fun A => A H)
      (circularPeriod_derivative_lowProjection_commute hγ hγ1 hρ hX hd)
    change fderiv ℝ (fun W => X W period) (littleCircularReference hγ hγ1)
      (circularLowFourierProjectionCLM hγ hγ1.le H) = _ at he
    rw [hv.1, map_zero] at he
    exact he.symm
  · intro N hN
    rw [circularPeriod_derivative_all_mode_coordinates hγ hγ1 hρ hX hd, hv.2 N hN]
    exact (NormedSpace.exp (period • circularAmplitudeGenerator N)).map_zero

theorem circularPeriod_derivative_pow_highMode_invariant (L k : ℕ)
    {H : Fin 2 → LittleContourSpace γ} (hH : H ∈ circularHighModeSubmodule hγ hγ1.le L) :
    ((fderiv ℝ (fun W => X W period) (littleCircularReference hγ hγ1)) ^ k) H ∈
      circularHighModeSubmodule hγ hγ1.le L := by
  induction k with
  | zero => exact hH
  | succ k ih =>
    rw [pow_succ', ContinuousLinearMap.mul_apply]
    exact circularPeriod_derivative_highMode_invariant hγ hγ1 hρ hX hd L ih

set_option maxHeartbeats 4000000 in
theorem circularPeriod_derivative_square_high_eq (L : ℕ)
    {H : Fin 2 → LittleContourSpace γ} (hH : H ∈ circularHighModeSubmodule hγ hγ1.le L) :
    fderiv ℝ (fun W => X W period) (littleCircularReference hγ hγ1)
        (fderiv ℝ (fun W => X W period) (littleCircularReference hγ hγ1) H) =
      H + circularFourierBlockTailCLM hγ hγ1.le circularDoublePeriodRemainderSymbol L H := by
  let D := fderiv ℝ (fun W => X W period) (littleCircularReference hγ hγ1)
  let T := circularDoublePeriodFourierRemainderCLM hγ hγ1.le
  let Q := circularLowFourierProjectionCLM hγ hγ1.le
  have hlow : Q H = 0 := ((mem_circularHighModeSubmodule hγ hγ1.le L H).mp hH).1
  have hD := circularPeriod_derivative_highMode_invariant hγ hγ1 hρ hX hd L hH
  have hDD := circularPeriod_derivative_highMode_invariant hγ hγ1 hρ hX hd L hD
  have hlowDD : Q (D (D H)) = 0 := ((mem_circularHighModeSubmodule hγ hγ1.le L _).mp hDD).1
  have hlowT : Q (T H) = 0 := circularLowFourierProjectionCLM_multiplier_zero hγ hγ1.le
    (summable_circularDoublePeriodRemainderSymbol γ) H
  have he : D (D H) - H - T H = Q (D (D H) - H - T H) :=
    circularPeriod_derivative_square_remainder_supported_low hγ hγ1 hρ hX hd H
  rw [map_sub, map_sub, hlowDD, hlow, hlowT, sub_self, sub_zero] at he
  have ht : circularFourierBlockTailCLM hγ hγ1.le circularDoublePeriodRemainderSymbol L H = T H :=
    circularFourierBlockTailCLM_apply_of_low_amplitudes_zero hγ hγ1.le _ H L
      ((mem_circularHighModeSubmodule hγ hγ1.le L H).mp hH).2
  change D (D H) = _
  rw [ht]
  exact (sub_eq_iff_eq_add.mp (sub_eq_zero.mp he)).trans (add_comm _ _)

theorem norm_circularPeriod_derivative_square_high_le (L : ℕ)
    {H : Fin 2 → LittleContourSpace γ} (hH : H ∈ circularHighModeSubmodule hγ hγ1.le L) :
    ‖fderiv ℝ (fun W => X W period) (littleCircularReference hγ hγ1)
      (fderiv ℝ (fun W => X W period) (littleCircularReference hγ hγ1) H)‖ ≤
      (1 + ‖circularFourierBlockTailCLM hγ hγ1.le circularDoublePeriodRemainderSymbol L‖) * ‖H‖ := by
  rw [circularPeriod_derivative_square_high_eq hγ hγ1 hρ hX hd L hH]
  exact (norm_add_le _ _).trans (by
    have h := (circularFourierBlockTailCLM hγ hγ1.le circularDoublePeriodRemainderSymbol L).le_opNorm H
    nlinarith)

theorem norm_circularPeriod_derivative_even_power_high_le (L k : ℕ)
    {H : Fin 2 → LittleContourSpace γ} (hH : H ∈ circularHighModeSubmodule hγ hγ1.le L) :
    ‖((fderiv ℝ (fun W => X W period) (littleCircularReference hγ hγ1)) ^ (2 * k)) H‖ ≤
      (1 + ‖circularFourierBlockTailCLM hγ hγ1.le circularDoublePeriodRemainderSymbol L‖) ^ k * ‖H‖ := by
  let D := fderiv ℝ (fun W => X W period) (littleCircularReference hγ hγ1)
  let c := 1 + ‖circularFourierBlockTailCLM hγ hγ1.le circularDoublePeriodRemainderSymbol L‖
  have hc : 0 ≤ c := by dsimp only [c]; positivity
  change ‖(D ^ (2 * k)) H‖ ≤ c ^ k * ‖H‖
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 + 2 * k by omega, pow_add, ContinuousLinearMap.mul_apply,
      pow_two, ContinuousLinearMap.mul_apply]
    calc
      _ ≤ c * ‖(D ^ (2 * k)) H‖ :=
        norm_circularPeriod_derivative_square_high_le hγ hγ1 hρ hX hd L
          (circularPeriod_derivative_pow_highMode_invariant hγ hγ1 hρ hX hd L (2 * k) hH)
      _ ≤ c * (c ^ k * ‖H‖) := mul_le_mul_of_nonneg_left ih hc
      _ = _ := by rw [pow_succ']; ring

theorem eventually_circularPeriod_derivative_even_power_high_small_growth
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ L : ℕ in atTop, ∀ (k : ℕ) (H : Fin 2 → LittleContourSpace γ),
      H ∈ circularHighModeSubmodule hγ hγ1.le L →
        ‖((fderiv ℝ (fun W => X W period) (littleCircularReference hγ hγ1)) ^ (2 * k)) H‖ ≤
          (1 + ε) ^ k * ‖H‖ := by
  filter_upwards [eventually_norm_circularDoublePeriodFourierTail_lt hγ hγ1.le hε] with L hL
  intro k H hH
  exact (norm_circularPeriod_derivative_even_power_high_le hγ hγ1 hρ hX hd L k hH).trans
    (by gcongr)

end ActualDerivative

end Euler2D

end
