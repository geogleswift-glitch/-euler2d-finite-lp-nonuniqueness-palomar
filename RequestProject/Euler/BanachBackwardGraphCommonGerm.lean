module

public import RequestProject.Euler.BanachLocalBackwardGraph

/-! Every two genuinely constructed weighted graphs for the same return
map agree on their common small coordinate ball. This transfers estimates
to an already fixed ancient graph without changing that graph or orbit. -/

@[expose] public section

set_option maxHeartbeats 1600000

noncomputable section

namespace Euler2D

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

namespace IsLocalWeightedBackwardGraph

theorem eq_of_common_coordinate {F : E → E} {P : E →L[ℝ] E} {ρ r s : ℝ}
    {x y : E → ℕ → E} (hx : IsLocalWeightedBackwardGraph F P ρ r x)
    (hy : IsLocalWeightedBackwardGraph F P ρ s y) (hρ : 0 ≤ ρ)
    {α : E} (hα : P α = α) (hαr : ‖α‖ ≤ r / 2) (hαs : ‖α‖ ≤ s / 2) :
    x α = y α := by
  apply Eq.symm
  apply hx.unique α hα hαr (y α) (hy.backward α hα hαs)
  · intro n
    have hp : 0 ≤ (ρ⁻¹) ^ n := pow_nonneg (inv_nonneg.mpr hρ) n
    calc
      ‖y α n‖ ≤ 2 * (ρ⁻¹) ^ n * ‖α‖ := hy.norm_le α hα hαs n
      _ ≤ 2 * (ρ⁻¹) ^ n * (r / 2) := mul_le_mul_of_nonneg_left hαr (by positivity)
      _ = r * (ρ⁻¹) ^ n := by ring
  · exact hy.coordinate α hα hαs

theorem quadratic_difference_of_comparisonGraph {F : E → E} {P : E →L[ℝ] E} {ρ r s H : ℝ}
    {x y : E → ℕ → E} (hx : IsLocalWeightedBackwardGraph F P ρ r x)
    (hy : IsLocalWeightedBackwardGraph F P ρ s y) (hρ : 0 ≤ ρ)
    (hquad : ∀ α, P α = α → ‖α‖ ≤ s / 2 → ∀ β, P β = β → ‖β‖ ≤ s / 2 →
      ‖(y α 0 - α) - (y β 0 - β)‖ ≤ H * (‖α‖ + ‖β‖) * ‖α - β‖)
    {α β : E} (hα : P α = α) (hαr : ‖α‖ ≤ min r s / 2)
    (hβ : P β = β) (hβr : ‖β‖ ≤ min r s / 2) :
    ‖(x α 0 - α) - (x β 0 - β)‖ ≤ H * (‖α‖ + ‖β‖) * ‖α - β‖ := by
  have har : ‖α‖ ≤ r / 2 := hαr.trans (div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num))
  have has : ‖α‖ ≤ s / 2 := hαr.trans (div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num))
  have hbr : ‖β‖ ≤ r / 2 := hβr.trans (div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num))
  have hbs : ‖β‖ ≤ s / 2 := hβr.trans (div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num))
  rw [hx.eq_of_common_coordinate hy hρ hα har has, hx.eq_of_common_coordinate hy hρ hβ hbr hbs]
  exact hquad α hα has β hβ hbs

end IsLocalWeightedBackwardGraph

end Euler2D

end
