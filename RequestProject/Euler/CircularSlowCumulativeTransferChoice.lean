module

public import RequestProject.Euler.CircularSlowTransferChoice

/-! The same nonzero transfer parameter may be chosen before the
cumulative stage horizon, including its geometric 1/(1-b) factor. -/

@[expose] public section

noncomputable section

open Complex Set
open scoped NNReal

namespace Euler2D
namespace CircularMaterialTransferProfile

variable {γ : ℝ≥0} {hγ : 0 < γ} {hγ1 : (γ : ℝ) < 1}
    (P : CircularMaterialTransferProfile hγ hγ1)

theorem exists_nonzero_transfer_ratio_with_slow_cumulative_self (K : ℝ≥0) :
    ∃ b ∈ Ioo (0 : ℝ) (1 / 4),
      bilateral P.moment ((b : ℂ) * (sigma + 5 / 4 * I)) ≠ 0 ∧
      6 * (K : ℝ) * b / ((1 - b) * sigma) < 1 / 2 := by
  have hσ : 0 < sigma := P.laplace.sigma_pos
  have hB : 0 < sigma / (16 * ((K : ℝ) + 1)) := div_pos hσ (by positivity)
  obtain ⟨b, hb, hsmall, hne⟩ := P.exists_nonzero_transfer_ratio_below hB
  refine ⟨b, hb, hne, ?_⟩
  have hh := (lt_div_iff₀ (by positivity : 0 < 16 * ((K : ℝ) + 1))).mp hsmall
  have hden : (3 / 4 : ℝ) * sigma ≤ (1 - b) * sigma :=
    mul_le_mul_of_nonneg_right (by linarith [hb.2]) hσ.le
  apply (div_lt_iff₀ (mul_pos (by linarith [hb.2] : 0 < 1 - b) hσ)).mpr
  nlinarith [K.coe_nonneg, hb.1]

end CircularMaterialTransferProfile
end Euler2D

end
