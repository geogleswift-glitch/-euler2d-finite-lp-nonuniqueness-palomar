module

public import RequestProject.Euler.CircularHighCutoffProjection
public import RequestProject.Euler.CircularAreaFourierMean
public import RequestProject.Euler.CircularComplementAmplitudeBound

/-! A genuine full Banach-space growth bound on the original
fourfold area tangent unstable complement. Finite blocks and the actual
infinite high-frequency kernel are assembled in the unchanged norm. -/

@[expose] public section

set_option maxHeartbeats 6000000

noncomputable section

open Set Filter Topology Metric
open scoped NNReal ContDiff

namespace Euler2D

theorem continuousLinearMap_commuting_power_apply {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (D Q : E →L[ℝ] E) (h : D.comp Q = Q.comp D) (k : ℕ) (H : E) :
    (D ^ k) (Q H) = Q ((D ^ k) H) := by
  have hc : Commute D Q := h
  exact congrArg (fun A : E →L[ℝ] E => A H) (hc.pow_left k).eq

local instance (priority := 2000) complementPowerLittle_group (γ : ℝ≥0) :
    NormedAddCommGroup (LittleContourSpace γ) := Submodule.normedAddCommGroup (LittleContourSpace γ)
local instance (priority := 2000) complementPowerLittle_space (γ : ℝ≥0) :
    NormedSpace ℝ (LittleContourSpace γ) := Submodule.normedSpace (LittleContourSpace γ)

theorem exists_norm_circularPeriod_derivative_even_power_complement_le {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1) {ρ : ℝ} (hρ : 0 < ρ)
    {X : (Fin 2 → LittleContourSpace γ) → ℝ → Fin 2 → LittleContourSpace γ}
    (hX : IsBanachFlowOn (circularBanachField hγ hγ1) (circularBanachDomain hγ hγ1)
      (ball (littleCircularReference hγ hγ1) ρ) period X)
    (hd : DifferentiableAt ℝ (fun W => X W period) (littleCircularReference hγ hγ1)) :
    ∃ C > 0, ∀ (k : ℕ) (H : Fin 2 → LittleContourSpace γ),
      (∀ i, H i ∈ fourfoldLittleContourSubmodule γ) →
      (∀ i, littleContourEllCLM γ (circularContourRadii i) (H i) = 0) →
      circularUnstableProjectionCLM hγ hγ1.le H = 0 →
      ‖((fderiv ℝ (fun W => X W period) (littleCircularReference hγ hγ1)) ^ (2 * k)) H‖ ≤
        C * (2 : ℝ) ^ k * ‖H‖ := by
  let D := fderiv ℝ (fun W => X W period) (littleCircularReference hγ hγ1)
  let P := circularLowFourierProjectionCLM hγ hγ1.le
  obtain ⟨L, hL⟩ := (eventually_circularPeriod_derivative_even_power_high_small_growth
    hγ hγ1 hρ hX hd (by norm_num : (0 : ℝ) < 1)).exists
  let Q := circularHighCutoffCLM hγ hγ1.le L
  let S : ℝ := ∑ N ∈ Finset.range L, circularFourierModeWeight γ N
  let B : ℝ := (4 + 16 * period) * (2 / cellA)
  let C : ℝ := 1 + ‖P‖ + S * B + ‖Q‖
  have hS : 0 ≤ S := Finset.sum_nonneg (fun N _ => circularFourierModeWeight_nonneg γ N)
  have hperiod : 0 < period := by unfold period; positivity
  have ha : 0 ≤ (2 / cellA : ℝ) := by have h := cellA_pos; positivity
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hC : 0 < C := by dsimp only [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro k H hfour harea hcomp
  have hp : 0 ≤ (2 : ℝ) ^ k := by positivity
  have hkAux : ∀ n : ℕ, (n : ℝ) ≤ (2 : ℝ) ^ n := by
    intro n
    induction n with
    | zero => norm_num
    | succ n ih =>
      rw [Nat.cast_add, Nat.cast_one, pow_succ]
      have h1 : (1 : ℝ) ≤ 2 ^ n := one_le_pow₀ (by norm_num)
      nlinarith
  have hk : (k : ℝ) ≤ (2 : ℝ) ^ k := hkAux k
  have hpow1 : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
  have htime : 4 + 8 * (((2 * k : ℕ) : ℝ) * period) ≤ (4 + 16 * period) * (2 : ℝ) ^ k := by
    have hpk := mul_le_mul_of_nonneg_left hk hperiod.le
    norm_num only [Nat.cast_mul, Nat.cast_ofNat]
    nlinarith
  have hscale : (4 + 8 * (((2 * k : ℕ) : ℝ) * period)) * (2 / cellA) ≤ B * (2 : ℝ) ^ k := by
    calc
      _ ≤ ((4 + 16 * period) * (2 : ℝ) ^ k) * (2 / cellA) :=
        mul_le_mul_of_nonneg_right htime ha
      _ = _ := by dsimp only [B]; ring
  have hterm (N : ℕ) :
      ‖(D ^ (2 * k)) (circularAngularModeProjectionCLM hγ hγ1.le ((N + 2 : ℕ) : ℤ) H)‖ ≤
        circularFourierModeWeight γ N * B * (2 : ℝ) ^ k * ‖H‖ := by
    rw [continuousLinearMap_commuting_power_apply D _
      (circularPeriod_derivative_angularProjection_commute hγ hγ1 hρ hX hd ((N + 2 : ℕ) : ℤ)),
      circularAngularModeProjectionCLM_eq_embedding]
    calc
      _ ≤ circularFourierModeWeight γ N *
          ‖circularModeAmplitudeCoefficientCLM γ N ((D ^ (2 * k)) H)‖ :=
        norm_circularModeAmplitudeEmbedding_le hγ hγ1.le N _
      _ ≤ circularFourierModeWeight γ N *
          ((4 + 8 * (((2 * k : ℕ) : ℝ) * period)) * (2 / cellA) * ‖H‖) :=
        mul_le_mul_of_nonneg_left
          (norm_circularPeriod_derivative_power_amplitude_complement_le hγ hγ1 hρ hX hd H hfour hcomp N (2 * k))
          (circularFourierModeWeight_nonneg γ N)
      _ ≤ circularFourierModeWeight γ N * ((B * (2 : ℝ) ^ k) * ‖H‖) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hscale (norm_nonneg H))
          (circularFourierModeWeight_nonneg γ N)
      _ = _ := by ring
  have hsum :
      ‖∑ N ∈ Finset.range L,
        (D ^ (2 * k)) (circularAngularModeProjectionCLM hγ hγ1.le ((N + 2 : ℕ) : ℤ) H)‖ ≤
          S * B * (2 : ℝ) ^ k * ‖H‖ := by
    calc
      _ ≤ ∑ N ∈ Finset.range L,
          ‖(D ^ (2 * k)) (circularAngularModeProjectionCLM hγ hγ1.le ((N + 2 : ℕ) : ℤ) H)‖ :=
        norm_sum_le _ _
      _ ≤ ∑ N ∈ Finset.range L, circularFourierModeWeight γ N * B * (2 : ℝ) ^ k * ‖H‖ :=
        Finset.sum_le_sum (fun N _ => hterm N)
      _ = _ := by dsimp only [S]; simp only [Finset.sum_mul]
  have hPH : D (P H) = P H := circularPeriod_derivative_low_fourfold_area hγ hγ1 hρ hX hd H hfour harea
  have hPpow : (D ^ (2 * k)) (P H) = P H := by
    suffices ∀ n : ℕ, (D ^ n) (P H) = P H from this (2 * k)
    intro n
    induction n with
    | zero => rfl
    | succ n ih => rw [pow_succ', ContinuousLinearMap.mul_apply, ih, hPH]
  have hLow : ‖P H‖ ≤ ‖P‖ * (2 : ℝ) ^ k * ‖H‖ := by
    calc
      _ ≤ ‖P‖ * ‖H‖ := P.le_opNorm H
      _ = ‖P‖ * 1 * ‖H‖ := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hpow1 (norm_nonneg P)) (norm_nonneg H)
  have hhigh : ‖(D ^ (2 * k)) (Q H)‖ ≤ ‖Q‖ * (2 : ℝ) ^ k * ‖H‖ := by
    have h := hL k (Q H) (circularHighCutoffCLM_mem_highMode hγ hγ1.le L H)
    have h' : ‖(D ^ (2 * k)) (Q H)‖ ≤ (2 : ℝ) ^ k * ‖Q H‖ := by
      simpa only [D, show (1 + 1 : ℝ) = 2 by norm_num] using h
    calc
      _ ≤ (2 : ℝ) ^ k * ‖Q H‖ := h'
      _ ≤ (2 : ℝ) ^ k * (‖Q‖ * ‖H‖) := mul_le_mul_of_nonneg_left (Q.le_opNorm H) hp
      _ = _ := by ring
  have he : (D ^ (2 * k)) H = P H +
      (∑ N ∈ Finset.range L,
        (D ^ (2 * k)) (circularAngularModeProjectionCLM hγ hγ1.le ((N + 2 : ℕ) : ℤ) H)) +
        (D ^ (2 * k)) (Q H) := by
    have h := congrArg (fun Z => (D ^ (2 * k)) Z) (circularOriginalSpace_cutoff_decomposition hγ hγ1.le L H)
    simp only [map_add, map_sum] at h
    change (D ^ (2 * k)) H = (D ^ (2 * k)) (P H) +
      (∑ N ∈ Finset.range L,
        (D ^ (2 * k)) (circularAngularModeProjectionCLM hγ hγ1.le ((N + 2 : ℕ) : ℤ) H)) +
        (D ^ (2 * k)) (Q H) at h
    rw [hPpow] at h
    exact h
  change ‖(D ^ (2 * k)) H‖ ≤ _
  rw [he]
  calc
    _ ≤ (‖P H‖ + ‖∑ N ∈ Finset.range L,
        (D ^ (2 * k)) (circularAngularModeProjectionCLM hγ hγ1.le ((N + 2 : ℕ) : ℤ) H)‖) +
          ‖(D ^ (2 * k)) (Q H)‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ (‖P‖ * (2 : ℝ) ^ k * ‖H‖ + S * B * (2 : ℝ) ^ k * ‖H‖) +
        ‖Q‖ * (2 : ℝ) ^ k * ‖H‖ := add_le_add (add_le_add hLow hsum) hhigh
    _ = (‖P‖ + S * B + ‖Q‖) * (2 : ℝ) ^ k * ‖H‖ := by ring
    _ ≤ C * (2 : ℝ) ^ k * ‖H‖ := by
      have hc : ‖P‖ + S * B + ‖Q‖ ≤ C := by dsimp only [C]; linarith
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc hp) (norm_nonneg H)

end Euler2D

end
