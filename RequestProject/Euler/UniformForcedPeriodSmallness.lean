module

public import Mathlib

@[expose] public section

noncomputable section

open Set
open scoped NNReal

namespace Euler2D

theorem exists_uniform_forced_flow_smallness {r T : ℝ} (hr : 0 < r) (hT : 0 < T)
    (K : ℝ≥0) :
    ∃ δ > 0, ∃ η > 0,
      δ * Real.exp (2 * (K : ℝ) * T) < r ∧
      ∀ (J : ℝ≥0), (J : ℝ) ≤ 1 → ∀ B ∈ Icc (0 : ℝ) η,
        (δ + B * T) * Real.exp (2 * ((K : ℝ) + J) * T) < r := by
  let E : ℝ := Real.exp (2 * ((K : ℝ) + 1) * T)
  have hE : 0 < E := Real.exp_pos _
  let δ : ℝ := r / (4 * E)
  have hδ : 0 < δ := div_pos hr (by positivity)
  let η : ℝ := δ / T
  have hη : 0 < η := div_pos hδ hT
  have hδE : δ * E = r / 4 := by dsimp only [δ]; field_simp
  have hηT : η * T = δ := div_mul_cancel₀ δ hT.ne'
  have hexp₀ : Real.exp (2 * (K : ℝ) * T) ≤ E := by
    apply Real.exp_le_exp.mpr
    nlinarith only [hT]
  refine ⟨δ, hδ, η, hη, ?_, ?_⟩
  · exact (mul_le_mul_of_nonneg_left hexp₀ hδ.le).trans_lt (by rw [hδE]; linarith)
  · intro J hJ B hB
    have hexp : Real.exp (2 * ((K : ℝ) + J) * T) ≤ E := by
      apply Real.exp_le_exp.mpr
      nlinarith only [hJ, hT]
    have hsum : δ + B * T ≤ 2 * δ := by
      have hh := mul_le_mul_of_nonneg_right hB.2 hT.le
      rw [hηT] at hh
      linarith only [hh]
    calc
      _ ≤ (2 * δ) * E := mul_le_mul hsum hexp (Real.exp_pos _).le (by positivity)
      _ = r / 2 := by nlinarith only [hδE]
      _ < r := by linarith

end Euler2D

end
