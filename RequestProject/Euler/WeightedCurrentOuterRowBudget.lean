module

public import RequestProject.Euler.WeightedInteractionRowBudget

/-! The current target is outside the ancestor maximum. Its complete
outer row is still O(rho^8), uniformly in the prefix length. It can be
absorbed into a fixed rho^6 polynomial forcing margin by choosing rho
after the weighted bound and all row constants. -/

@[expose] public section

set_option maxHeartbeats 3500000

noncomputable section

open Set
open scoped BigOperators NNReal

namespace Euler2D

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem weighted_current_outer_row_sum_bound {b C₀ ρ : ℝ}
    (hb : 0 < b) (hb1 : b ≤ 1) (hC₀ : 0 < C₀) (hρ : 0 < ρ)
    (hζ : C₀ * ρ ^ 8 < 1) (k : ℕ) (x : ℕ → E) :
    (∑ l : Fin k, b ^ (k - (l : ℕ)) * ρ ^ (2 * (k - (l : ℕ))) * ‖x l‖) ≤
      b * weightedFamilyNorm (C₀ * ρ ^ 6) k x * ((C₀ * ρ ^ 8) / (1 - C₀ * ρ ^ 8)) := by
  let h := C₀ * ρ ^ 6
  let Z := weightedFamilyNorm h k x
  let ζ := C₀ * ρ ^ 8
  have hh : 0 < h := by dsimp [h]; positivity
  have hZ : 0 ≤ Z := norm_nonneg _
  have hζ0 : 0 ≤ ζ := by dsimp [ζ]; positivity
  have hterm (l : Fin k) :
      b ^ (k - (l : ℕ)) * ρ ^ (2 * (k - (l : ℕ))) * ‖x l‖ ≤
        (b * Z) * ζ ^ (k - (l : ℕ)) := by
    have hn := norm_le_weightedFamilyNorm hh k x l
    have hbpow : b ^ (k - (l : ℕ)) ≤ b := by
      simpa only [pow_one] using pow_le_pow_of_le_one hb.le hb1 (show 1 ≤ k - (l : ℕ) by omega)
    have hid := rho_pow_down C₀ ρ 0 (k - (l : ℕ))
    simp only [zero_add, pow_zero, one_mul] at hid
    calc
      _ ≤ (b * ρ ^ (2 * (k - (l : ℕ)))) * (h ^ (k - (l : ℕ)) * Z) :=
        mul_le_mul (mul_le_mul_of_nonneg_right hbpow (by positivity)) hn (norm_nonneg _) (by positivity)
      _ = b * Z * (ρ ^ (2 * (k - (l : ℕ))) * (C₀ * ρ ^ 6) ^ (k - (l : ℕ))) := by dsimp [h]; ring
      _ = _ := by rw [hid]
  have hgeo := sum_pow_le_of_injOn (Finset.univ : Finset (Fin k)) (fun l => k - (l : ℕ))
    (fun a _ b' _ hab => by
      change k - (a : ℕ) = k - (b' : ℕ) at hab
      exact Fin.ext (by have ha := a.isLt; have hb' := b'.isLt; omega))
    (fun l _ => by have hl := l.isLt; change 1 ≤ k - (l : ℕ); omega) hζ0 hζ
  calc
    _ ≤ ∑ l : Fin k, (b * Z) * ζ ^ (k - (l : ℕ)) :=
      Finset.sum_le_sum (fun l _ => hterm l)
    _ = (b * Z) * ∑ l : Fin k, ζ ^ (k - (l : ℕ)) := by rw [Finset.mul_sum]
    _ ≤ (b * Z) * (ζ / (1 - ζ)) := mul_le_mul_of_nonneg_left hgeo (by positivity)
    _ = _ := rfl

theorem weighted_current_outer_row_le_rhoEight {b C₀ ρ K : ℝ}
    (hb : 0 < b) (hb1 : b ≤ 1) (hC₀ : 0 < C₀) (hρ : 0 < ρ)
    (hζ : C₀ * ρ ^ 8 ≤ 1 / 2) (hK : 0 ≤ K) (k : ℕ) (x : ℕ → E)
    (hx : weightedFamilyNorm (C₀ * ρ ^ 6) k x ≤ K) :
    (∑ l : Fin k, b ^ (k - (l : ℕ)) * ρ ^ (2 * (k - (l : ℕ))) * ‖x l‖) ≤
      (2 * b * C₀ * K) * ρ ^ 8 := by
  have hζ0 : 0 ≤ C₀ * ρ ^ 8 := by positivity
  have hden : 0 < 1 - C₀ * ρ ^ 8 := by linarith
  have hfrac : (C₀ * ρ ^ 8) / (1 - C₀ * ρ ^ 8) ≤ 2 * (C₀ * ρ ^ 8) := by
    apply (div_le_iff₀ hden).mpr
    nlinarith only [mul_nonneg hζ0 (show 0 ≤ 1 - 2 * (C₀ * ρ ^ 8) by linarith)]
  calc
    _ ≤ b * weightedFamilyNorm (C₀ * ρ ^ 6) k x * ((C₀ * ρ ^ 8) / (1 - C₀ * ρ ^ 8)) :=
      weighted_current_outer_row_sum_bound hb hb1 hC₀ hρ (by linarith) k x
    _ ≤ (b * K) * (2 * (C₀ * ρ ^ 8)) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hx hb.le) hfrac
        (div_nonneg hζ0 hden.le) (mul_nonneg hb.le hK)
    _ = _ := by ring

theorem weighted_current_outer_forcing_le_rhoSix_budget {b C₀ ρ K Cdown Δ t : ℝ}
    (hb : 0 < b) (hb1 : b ≤ 1) (hC₀ : 0 < C₀) (hρ : 0 < ρ)
    (hζ : C₀ * ρ ^ 8 ≤ 1 / 2) (hK : 0 ≤ K) (hdown : 0 ≤ Cdown) (hΔ : 0 ≤ Δ)
    (k : ℕ) (x : ℕ → E) (hx : weightedFamilyNorm (C₀ * ρ ^ 6) k x ≤ K)
    (hsmall : (2 * b * C₀ * K * Cdown) * ρ ^ 2 ≤ Δ) (ht : 0 ≤ t) :
    Cdown * (∑ l : Fin k, b ^ (k - (l : ℕ)) * ρ ^ (2 * (k - (l : ℕ))) * ‖x l‖) ≤
      Δ * ρ ^ 6 * (1 + t) ^ 4 := by
  have hpoly : (1 : ℝ) ≤ (1 + t) ^ 4 := one_le_pow₀ (by linarith : (1 : ℝ) ≤ 1 + t)
  calc
    _ ≤ Cdown * ((2 * b * C₀ * K) * ρ ^ 8) :=
      mul_le_mul_of_nonneg_left (weighted_current_outer_row_le_rhoEight hb hb1 hC₀ hρ hζ hK k x hx) hdown
    _ = ((2 * b * C₀ * K * Cdown) * ρ ^ 2) * ρ ^ 6 := by ring
    _ ≤ Δ * ρ ^ 6 := mul_le_mul_of_nonneg_right hsmall (by positivity)
    _ ≤ _ := le_mul_of_one_le_right (mul_nonneg hΔ (by positivity)) hpoly

end Euler2D

end
