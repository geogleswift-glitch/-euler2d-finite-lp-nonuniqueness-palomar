module

public import RequestProject.Euler.CircularFourierOperatorBounds

/-! Actual amplitude coordinates and the three omitted contour
frequencies completely determine every original little contour family. -/

@[expose] public section

set_option maxHeartbeats 1000000

noncomputable section

open Complex Set
open scoped NNReal ContDiff ComplexConjugate

namespace Euler2D

local instance (priority := 2000) coefficientDecompLittle_group (γ : ℝ≥0) :
    NormedAddCommGroup (LittleContourSpace γ) := Submodule.normedAddCommGroup (LittleContourSpace γ)
local instance (priority := 2000) coefficientDecompLittle_space (γ : ℝ≥0) :
    NormedSpace ℝ (LittleContourSpace γ) := Submodule.normedSpace (LittleContourSpace γ)

theorem circularFourierCoefficient_plus_reconstruct {γ : ℝ≥0}
    (N : ℕ) (H : Fin 2 → LittleContourSpace γ) (i : Fin 2) :
    littleContourFourierCoefficient γ ((N + 3 : ℕ) : ℤ) (H i) =
      circularNormalModePlus (circularContourRadii i)
        ((circularModeAmplitudeCoefficientCLM γ N H).1 i)
        ((circularModeAmplitudeCoefficientCLM γ N H).2 i) := by
  symm
  change circularNormalModePlus (circularContourRadii i)
    (littleContourModeNormalCoefficientCLM γ (circularContourRadii i) N (H i))
    (littleContourModeTangentCoefficientCLM γ (circularContourRadii i) N (H i)) = _
  rw [littleContourModeNormalCoefficientCLM_apply, littleContourModeTangentCoefficientCLM_apply]
  exact circularFourthModePlus_reconstruct (circularContourRadii_bounds i).1.ne' _ _

theorem circularFourierCoefficient_minus_reconstruct {γ : ℝ≥0}
    (N : ℕ) (H : Fin 2 → LittleContourSpace γ) (i : Fin 2) :
    littleContourFourierCoefficient γ (-((N + 1 : ℕ) : ℤ)) (H i) =
      circularNormalModeMinus (circularContourRadii i)
        ((circularModeAmplitudeCoefficientCLM γ N H).1 i)
        ((circularModeAmplitudeCoefficientCLM γ N H).2 i) := by
  symm
  change circularNormalModeMinus (circularContourRadii i)
    (littleContourModeNormalCoefficientCLM γ (circularContourRadii i) N (H i))
    (littleContourModeTangentCoefficientCLM γ (circularContourRadii i) N (H i)) = _
  rw [littleContourModeNormalCoefficientCLM_apply, littleContourModeTangentCoefficientCLM_apply]
  exact circularFourthModeMinus_reconstruct (circularContourRadii_bounds i).1.ne' _ _

theorem circularFourierAmplitude_ext {γ : ℝ≥0}
    {H K : Fin 2 → LittleContourSpace γ}
    (hmode : ∀ N : ℕ, circularModeAmplitudeCoefficientCLM γ N H = circularModeAmplitudeCoefficientCLM γ N K)
    (hlow : ∀ (i : Fin 2) (k : ℤ), 0 ≤ k → k ≤ 2 →
      littleContourFourierCoefficient γ k (H i) = littleContourFourierCoefficient γ k (K i)) : H = K := by
  funext i
  apply littleContourFourierCoefficient_ext
  intro k
  by_cases hpos : 3 ≤ k
  · let N := (k - 3).toNat
    have hk : ((N + 3 : ℕ) : ℤ) = k := by dsimp only [N]; omega
    rw [← hk, circularFourierCoefficient_plus_reconstruct,
      circularFourierCoefficient_plus_reconstruct, hmode N]
  · by_cases hneg : k < 0
    · let N := (-k - 1).toNat
      have hk : -((N + 1 : ℕ) : ℤ) = k := by dsimp only [N]; omega
      rw [← hk, circularFourierCoefficient_minus_reconstruct,
        circularFourierCoefficient_minus_reconstruct, hmode N]
    · exact hlow i k (by omega) (by omega)

def circularLowFourierProjectionCLM {γ : ℝ≥0} (hγ : 0 < γ) (hγ1 : γ ≤ 1) :
    (Fin 2 → LittleContourSpace γ) →L[ℝ] (Fin 2 → LittleContourSpace γ) :=
  ContinuousLinearMap.pi fun i =>
    (littleContourFourierTermCLM hγ hγ1 0 1 + littleContourFourierTermCLM hγ hγ1 1 1 +
      littleContourFourierTermCLM hγ hγ1 2 1).comp (ContinuousLinearMap.proj i)

theorem littleContourFourierCoefficient_lowProjection {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : γ ≤ 1) (H : Fin 2 → LittleContourSpace γ) (i : Fin 2) (k : ℤ) :
    littleContourFourierCoefficient γ k (circularLowFourierProjectionCLM hγ hγ1 H i) =
      (if (0 : ℤ) = k then littleContourFourierCoefficient γ 0 (H i) else 0) +
        (if (1 : ℤ) = k then littleContourFourierCoefficient γ 1 (H i) else 0) +
          (if (2 : ℤ) = k then littleContourFourierCoefficient γ 2 (H i) else 0) := by
  change littleContourFourierCoefficientCLM γ k
    (littleContourFourierTermCLM hγ hγ1 0 1 (H i) +
      littleContourFourierTermCLM hγ hγ1 1 1 (H i) +
        littleContourFourierTermCLM hγ hγ1 2 1 (H i)) = _
  rw [map_add, map_add]
  simp only [littleContourFourierCoefficientCLM_apply, littleContourFourierCoefficient_term, one_mul]

theorem circularLowFourierProjection_of_zero_amplitude {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : γ ≤ 1) (H : Fin 2 → LittleContourSpace γ)
    (hmode : ∀ N : ℕ, circularModeAmplitudeCoefficientCLM γ N H = 0) :
    H = circularLowFourierProjectionCLM hγ hγ1 H := by
  funext i
  apply littleContourFourierCoefficient_ext
  intro k
  rw [littleContourFourierCoefficient_lowProjection]
  by_cases hpos : 3 ≤ k
  · have hk0 : (0 : ℤ) ≠ k := by omega
    have hk1 : (1 : ℤ) ≠ k := by omega
    have hk2 : (2 : ℤ) ≠ k := by omega
    rw [if_neg hk0, if_neg hk1, if_neg hk2, zero_add, zero_add]
    let N := (k - 3).toNat
    have hk : ((N + 3 : ℕ) : ℤ) = k := by dsimp only [N]; omega
    rw [← hk, circularFourierCoefficient_plus_reconstruct, hmode N]
    simp [circularNormalModePlus]
  · by_cases hneg : k < 0
    · have hk0 : (0 : ℤ) ≠ k := by omega
      have hk1 : (1 : ℤ) ≠ k := by omega
      have hk2 : (2 : ℤ) ≠ k := by omega
      rw [if_neg hk0, if_neg hk1, if_neg hk2, zero_add, zero_add]
      let N := (-k - 1).toNat
      have hk : -((N + 1 : ℕ) : ℤ) = k := by dsimp only [N]; omega
      rw [← hk, circularFourierCoefficient_minus_reconstruct, hmode N]
      simp [circularNormalModeMinus]
    · have hk0 : 0 ≤ k := by omega
      have hk2 : k ≤ 2 := by omega
      interval_cases k <;> norm_num

end Euler2D

end
