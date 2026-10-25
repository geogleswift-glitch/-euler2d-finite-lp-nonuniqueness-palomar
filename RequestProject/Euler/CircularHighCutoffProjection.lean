module

public import RequestProject.Euler.CircularHighTailPowerBound

/-! A genuine bounded finite Fourier cutoff produces elements of the
actual invariant high-frequency kernel, with an exact original-space
decomposition for every perturbation. -/

@[expose] public section

set_option maxHeartbeats 1000000

noncomputable section

open Set Filter Topology Metric
open scoped NNReal ContDiff

namespace Euler2D

local instance (priority := 2000) highCutoffLittle_group (γ : ℝ≥0) :
    NormedAddCommGroup (LittleContourSpace γ) := Submodule.normedAddCommGroup (LittleContourSpace γ)
local instance (priority := 2000) highCutoffLittle_space (γ : ℝ≥0) :
    NormedSpace ℝ (LittleContourSpace γ) := Submodule.normedSpace (LittleContourSpace γ)

theorem circularAngularModeProjectionCLM_eq_embedding {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : γ ≤ 1) (N : ℕ) (H : Fin 2 → LittleContourSpace γ) :
    circularAngularModeProjectionCLM hγ hγ1 ((N + 2 : ℕ) : ℤ) H =
      circularModeAmplitudeEmbeddingCLM hγ hγ1 N (circularModeAmplitudeCoefficientCLM γ N H) := by
  rw [circularAngularModeProjectionCLM_eq_normalMode, circularModeAmplitudeEmbeddingCLM_apply]
  rfl

theorem circularLowFourierProjectionCLM_idempotent {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : γ ≤ 1) (H : Fin 2 → LittleContourSpace γ) :
    circularLowFourierProjectionCLM hγ hγ1 (circularLowFourierProjectionCLM hγ hγ1 H) =
      circularLowFourierProjectionCLM hγ hγ1 H := by
  funext i
  have hc (k : ℤ) (hk0 : 0 ≤ k) (hk2 : k ≤ 2) :
      littleContourFourierCoefficient γ k (circularLowFourierProjectionCLM hγ hγ1 H i) =
        littleContourFourierCoefficient γ k (H i) := by
    rw [littleContourFourierCoefficient_lowProjection]
    interval_cases k <;> norm_num
  calc
    _ = _ := circularLowFourierProjectionCLM_apply hγ hγ1 _ i
    _ = _ := by rw [hc 0 (by norm_num) (by norm_num), hc 1 (by norm_num) (by norm_num),
      hc 2 (by norm_num) (by norm_num)]
    _ = _ := (circularLowFourierProjectionCLM_apply hγ hγ1 H i).symm

theorem circularModeAmplitudeCoefficient_lowProjection_zero {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : γ ≤ 1) (H : Fin 2 → LittleContourSpace γ) (N : ℕ) :
    circularModeAmplitudeCoefficientCLM γ N (circularLowFourierProjectionCLM hγ hγ1 H) = 0 := by
  have hz (i : Fin 2) (k : ℤ) (hk : k < 0 ∨ 3 ≤ k) :
      littleContourFourierCoefficient γ k (circularLowFourierProjectionCLM hγ hγ1 H i) = 0 := by
    rw [littleContourFourierCoefficient_lowProjection, if_neg (by omega : (0 : ℤ) ≠ k),
      if_neg (by omega : (1 : ℤ) ≠ k), if_neg (by omega : (2 : ℤ) ≠ k), zero_add, zero_add]
  apply Prod.ext
  · funext i
    change littleContourModeNormalCoefficientCLM γ (circularContourRadii i) N
      (circularLowFourierProjectionCLM hγ hγ1 H i) = 0
    rw [littleContourModeNormalCoefficientCLM_apply, hz i _ (by omega), hz i _ (by omega)]
    simp
  · funext i
    change littleContourModeTangentCoefficientCLM γ (circularContourRadii i) N
      (circularLowFourierProjectionCLM hγ hγ1 H i) = 0
    rw [littleContourModeTangentCoefficientCLM_apply, hz i _ (by omega), hz i _ (by omega)]
    simp

def circularHighCutoffCLM {γ : ℝ≥0} (hγ : 0 < γ) (hγ1 : γ ≤ 1) (L : ℕ) :
    (Fin 2 → LittleContourSpace γ) →L[ℝ] (Fin 2 → LittleContourSpace γ) :=
  ContinuousLinearMap.id ℝ _ - circularLowFourierProjectionCLM hγ hγ1 -
    ∑ N ∈ Finset.range L, circularAngularModeProjectionCLM hγ hγ1 ((N + 2 : ℕ) : ℤ)

theorem circularHighCutoffCLM_apply {γ : ℝ≥0} (hγ : 0 < γ) (hγ1 : γ ≤ 1)
    (L : ℕ) (H : Fin 2 → LittleContourSpace γ) :
    circularHighCutoffCLM hγ hγ1 L H = H - circularLowFourierProjectionCLM hγ hγ1 H -
      ∑ N ∈ Finset.range L, circularAngularModeProjectionCLM hγ hγ1 ((N + 2 : ℕ) : ℤ) H := by
  simp only [circularHighCutoffCLM, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.id_apply, ContinuousLinearMap.sum_apply]

theorem circularHighCutoffCLM_mem_highMode {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : γ ≤ 1) (L : ℕ) (H : Fin 2 → LittleContourSpace γ) :
    circularHighCutoffCLM hγ hγ1 L H ∈ circularHighModeSubmodule hγ hγ1 L := by
  apply (mem_circularHighModeSubmodule hγ hγ1 L _).mpr
  constructor
  · rw [circularHighCutoffCLM_apply, map_sub, map_sub, circularLowFourierProjectionCLM_idempotent]
    have hz (N : ℕ) : circularLowFourierProjectionCLM hγ hγ1
        (circularAngularModeProjectionCLM hγ hγ1 ((N + 2 : ℕ) : ℤ) H) = 0 := by
      rw [circularAngularModeProjectionCLM_eq_embedding]
      exact circularLowFourierProjectionCLM_embedding_zero hγ hγ1 N _
    simp only [map_sum, hz, Finset.sum_const_zero, sub_self, sub_zero]
  · intro N hN
    rw [circularHighCutoffCLM_apply, map_sub, map_sub, circularModeAmplitudeCoefficient_lowProjection_zero]
    simp only [map_sum, circularAngularModeProjectionCLM_eq_embedding,
      circularModeAmplitudeCoefficient_embedding, Finset.sum_ite_eq, Finset.mem_range,
      if_pos hN, sub_zero, sub_self]

theorem circularOriginalSpace_cutoff_decomposition {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : γ ≤ 1) (L : ℕ) (H : Fin 2 → LittleContourSpace γ) :
    H = circularLowFourierProjectionCLM hγ hγ1 H +
      (∑ N ∈ Finset.range L, circularAngularModeProjectionCLM hγ hγ1 ((N + 2 : ℕ) : ℤ) H) +
        circularHighCutoffCLM hγ hγ1 L H := by
  rw [circularHighCutoffCLM_apply]
  abel

end Euler2D

end
