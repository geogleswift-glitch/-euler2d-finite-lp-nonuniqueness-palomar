module

public import RequestProject.Euler.SmallNonzeroTransferRatio

/-! A nonzero transfer ratio of the same moment profile may satisfy
the genuine slow-ancestor restriction with the original six-over-sigma
capture clock. The self constant is fixed before choosing the ratio. -/

@[expose] public section

noncomputable section

open Complex Set
open scoped NNReal

namespace Euler2D
namespace CircularMaterialTransferProfile

variable {γ : ℝ≥0} {hγ : 0 < γ} {hγ1 : (γ : ℝ) < 1}
    (P : CircularMaterialTransferProfile hγ hγ1)

theorem exists_nonzero_transfer_ratio_with_slow_self (K : ℝ≥0) :
    ∃ b ∈ Ioo (0 : ℝ) (1 / 4),
      bilateral P.moment ((b : ℂ) * (sigma + 5 / 4 * I)) ≠ 0 ∧
      6 * (K : ℝ) * b / sigma < 1 / 2 := by
  have hσ : 0 < sigma := P.laplace.sigma_pos
  have hB : 0 < sigma / (12 * ((K : ℝ) + 1)) := div_pos hσ (by positivity)
  obtain ⟨b, hb, hsmall, hne⟩ := P.exists_nonzero_transfer_ratio_below hB
  refine ⟨b, hb, hne, ?_⟩
  have hh := (lt_div_iff₀ (by positivity : 0 < 12 * ((K : ℝ) + 1))).mp hsmall
  apply (div_lt_iff₀ hσ).mpr
  nlinarith [K.coe_nonneg, hb.1]

end CircularMaterialTransferProfile
end Euler2D

end
