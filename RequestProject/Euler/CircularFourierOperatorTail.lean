module

public import RequestProject.Euler.CircularDoublePeriodOperator

/-! Actual high Fourier block tails tend to zero in operator norm.
Their coefficient formulas and their action on a true high-mode kernel
are identities in the original little contour Banach space. -/

@[expose] public section

set_option maxHeartbeats 1000000

noncomputable section

open Set Filter Topology Metric
open scoped NNReal ContDiff

namespace Euler2D

local instance (priority := 2000) operatorTailLittle_group (γ : ℝ≥0) :
    NormedAddCommGroup (LittleContourSpace γ) := Submodule.normedAddCommGroup (LittleContourSpace γ)
local instance (priority := 2000) operatorTailLittle_space (γ : ℝ≥0) :
    NormedSpace ℝ (LittleContourSpace γ) := Submodule.normedSpace (LittleContourSpace γ)
local instance (priority := 2000) operatorTailEndo_group (γ : ℝ≥0) :
    NormedAddCommGroup ((Fin 2 → LittleContourSpace γ) →L[ℝ] (Fin 2 → LittleContourSpace γ)) :=
  ContinuousLinearMap.toNormedAddCommGroup

def circularFourierBlockTailCLM {γ : ℝ≥0} (hγ : 0 < γ) (hγ1 : γ ≤ 1)
    (A : ℕ → CircularFourierAmplitudes →L[ℝ] CircularFourierAmplitudes) (L : ℕ) :
    (Fin 2 → LittleContourSpace γ) →L[ℝ] (Fin 2 → LittleContourSpace γ) :=
  circularFourierBlockMultiplierCLM hγ hγ1 A -
    ∑ N ∈ Finset.range L, circularFourierBlockTermCLM hγ hγ1 N (A N)

theorem circularModeAmplitudeCoefficient_tail {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : γ ≤ 1)
    {A : ℕ → CircularFourierAmplitudes →L[ℝ] CircularFourierAmplitudes}
    (hA : Summable (fun N => circularFourierModeWeight γ N * ‖A N‖))
    (H : Fin 2 → LittleContourSpace γ) (L N : ℕ) :
    circularModeAmplitudeCoefficientCLM γ N (circularFourierBlockTailCLM hγ hγ1 A L H) =
      if L ≤ N then A N (circularModeAmplitudeCoefficientCLM γ N H) else 0 := by
  change circularModeAmplitudeCoefficientCLM γ N
    (circularFourierBlockMultiplierCLM hγ hγ1 A H -
      (∑ M ∈ Finset.range L, circularFourierBlockTermCLM hγ hγ1 M (A M)) H) = _
  rw [map_sub, circularModeAmplitudeCoefficient_multiplier hγ hγ1 hA]
  simp only [ContinuousLinearMap.sum_apply, map_sum, circularFourierBlockTermCLM,
    ContinuousLinearMap.comp_apply, circularModeAmplitudeCoefficient_embedding,
    Finset.sum_ite_eq, Finset.mem_range]
  by_cases hNL : N < L
  · rw [if_pos hNL, if_neg (by omega : ¬L ≤ N), sub_self]
  · rw [if_neg hNL, if_pos (by omega : L ≤ N), sub_zero]

theorem tendsto_circularFourierBlockTailCLM_zero {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : γ ≤ 1)
    {A : ℕ → CircularFourierAmplitudes →L[ℝ] CircularFourierAmplitudes}
    (hA : Summable (fun N => circularFourierModeWeight γ N * ‖A N‖)) :
    Tendsto (circularFourierBlockTailCLM hγ hγ1 A) atTop (𝓝 0) := by
  have hs := (summable_circularFourierBlockTermCLM hγ hγ1 hA).hasSum.tendsto_sum_nat
  have hn := tendsto_iff_norm_sub_tendsto_zero.mp hs
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  convert hn using 1
  funext L
  exact norm_sub_rev _ _

theorem eventually_norm_circularFourierBlockTailCLM_lt {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : γ ≤ 1)
    {A : ℕ → CircularFourierAmplitudes →L[ℝ] CircularFourierAmplitudes}
    (hA : Summable (fun N => circularFourierModeWeight γ N * ‖A N‖))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ L : ℕ in atTop, ‖circularFourierBlockTailCLM hγ hγ1 A L‖ < ε := by
  have ht := (tendsto_circularFourierBlockTailCLM_zero hγ hγ1 hA).norm
  rw [norm_zero] at ht
  exact ht.eventually (eventually_lt_nhds hε)

theorem circularFourierBlockTailCLM_apply_of_low_amplitudes_zero {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : γ ≤ 1)
    (A : ℕ → CircularFourierAmplitudes →L[ℝ] CircularFourierAmplitudes)
    (H : Fin 2 → LittleContourSpace γ) (L : ℕ)
    (hH : ∀ N < L, circularModeAmplitudeCoefficientCLM γ N H = 0) :
    circularFourierBlockTailCLM hγ hγ1 A L H = circularFourierBlockMultiplierCLM hγ hγ1 A H := by
  change circularFourierBlockMultiplierCLM hγ hγ1 A H -
    (∑ N ∈ Finset.range L, circularFourierBlockTermCLM hγ hγ1 N (A N)) H = _
  rw [ContinuousLinearMap.sum_apply]
  have hz : (∑ N ∈ Finset.range L, circularFourierBlockTermCLM hγ hγ1 N (A N) H) = 0 := by
    apply Finset.sum_eq_zero
    intro N hN
    change circularModeAmplitudeEmbeddingCLM hγ hγ1 N (A N (circularModeAmplitudeCoefficientCLM γ N H)) = 0
    rw [hH N (Finset.mem_range.mp hN), map_zero, map_zero]
  rw [hz, sub_zero]

theorem eventually_norm_circularDoublePeriodFourierTail_lt {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : γ ≤ 1) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ L : ℕ in atTop,
      ‖circularFourierBlockTailCLM hγ hγ1 circularDoublePeriodRemainderSymbol L‖ < ε :=
  eventually_norm_circularFourierBlockTailCLM_lt hγ hγ1 (summable_circularDoublePeriodRemainderSymbol γ) hε

end Euler2D

end
