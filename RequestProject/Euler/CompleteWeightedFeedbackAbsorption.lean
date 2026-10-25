module

public import RequestProject.Euler.CompleteWeightedInteractionRows

/-! Periodic row feedback is a true O(R^8) addition to the fixed
planar weighted rate. Thus the nonzero transfer ratio may be chosen
from fixed row constants before every rho and physical scale. -/

@[expose] public section

set_option maxHeartbeats 4000000

noncomputable section

namespace Euler2D

theorem completeWeightedFeedback_le_fixed_rows {b Cu Cd Ct C₀ ρ : ℝ}
    (hb : 0 ≤ b) (hb1 : b ≤ 1) (ht : 0 ≤ Ct)
    (hC₀ : 2 ≤ C₀) (hζ : C₀ * ρ ^ 8 ≤ 1 / 2) :
    Ct * b + weightedInteractionRowFeedback b (Cu + Ct) (Cd + Ct) C₀ ρ ≤
      weightedInteractionRowFeedback b Cu Cd C₀ ρ + 3 * Ct := by
  let ζ := C₀ * ρ ^ 8
  have hζ0 : 0 ≤ ζ := by dsimp only [ζ]; positivity
  have hden : 0 < 1 - ζ := by dsimp only [ζ]; linarith
  have hfirst : 1 / (C₀ - 1) ≤ 1 := (div_le_one (by linarith)).mpr (by linarith)
  have hsecond : ζ / (1 - ζ) ≤ 1 := (div_le_one hden).mpr (by dsimp only [ζ]; linarith)
  have hshape0 : 0 ≤ 1 + 1 / (C₀ - 1) + ζ / (1 - ζ) :=
    add_nonneg (add_nonneg zero_le_one (div_nonneg zero_le_one (by linarith))) (div_nonneg hζ0 hden.le)
  have hshape : 1 + 1 / (C₀ - 1) + ζ / (1 - ζ) ≤ 3 := by linarith
  have hprod : Ct * b * (1 + 1 / (C₀ - 1) + ζ / (1 - ζ)) ≤ 3 * Ct := by
    calc
      _ ≤ Ct * (1 + 1 / (C₀ - 1) + ζ / (1 - ζ)) :=
        mul_le_mul_of_nonneg_right (by nlinarith only [mul_le_mul_of_nonneg_left hb1 ht]) hshape0
      _ ≤ Ct * 3 := mul_le_mul_of_nonneg_left hshape ht
      _ = _ := by ring
  calc
    _ = weightedInteractionRowFeedback b Cu Cd C₀ ρ +
        Ct * b * (1 + 1 / (C₀ - 1) + ζ / (1 - ζ)) := by
      unfold weightedInteractionRowFeedback ζ
      ring
    _ ≤ _ := add_le_add le_rfl hprod

theorem completeWeighted_rhs_le_fixed_rows {b Cu Cd Ct C₀ ρ Z E D : ℝ}
    (hb : 0 ≤ b) (hb1 : b ≤ 1) (ht : 0 ≤ Ct) (ht1 : Ct ≤ 1)
    (hC₀ : 2 ≤ C₀) (hζ : C₀ * ρ ^ 8 ≤ 1 / 2) (hZ : 0 ≤ Z) (hE : 0 ≤ E) :
    (Ct * b + weightedInteractionRowFeedback b (Cu + Ct) (Cd + Ct) C₀ ρ) * Z +
        (Cu + Ct) / C₀ * E + D ≤
      (3 * Ct + weightedInteractionRowFeedback b Cu Cd C₀ ρ) * Z +
        (Cu + 1) / C₀ * E + D := by
  have hfb := mul_le_mul_of_nonneg_right
    (completeWeightedFeedback_le_fixed_rows (Cu := Cu) (Cd := Cd) hb hb1 ht hC₀ hζ) hZ
  have hcur : (Cu + Ct) / C₀ * E ≤ (Cu + 1) / C₀ * E := mul_le_mul_of_nonneg_right
    (div_le_div_of_nonneg_right (add_le_add le_rfl ht1) (by linarith : 0 ≤ C₀)) hE
  have hfb' : (Ct * b + weightedInteractionRowFeedback b (Cu + Ct) (Cd + Ct) C₀ ρ) * Z ≤
      (3 * Ct + weightedInteractionRowFeedback b Cu Cd C₀ ρ) * Z :=
    hfb.trans_eq (by ring)
  exact add_le_add (add_le_add hfb' hcur) le_rfl

end Euler2D

end
