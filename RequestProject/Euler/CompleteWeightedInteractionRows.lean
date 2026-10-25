module

public import RequestProject.Euler.WeightedInteractionRowBudget

/-! Reducing the complete actual row shape, including its periodic
self row and current source, in the original finite weighted norm. -/

@[expose] public section

set_option maxHeartbeats 6000000
set_option maxRecDepth 4000

noncomputable section

open Set
open scoped BigOperators NNReal

namespace Euler2D

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def completeInteractionRowSum (Cu Cd Ct b ρ : ℝ) (k j : ℕ) (x : ℕ → E) : ℝ :=
  (∑ l : Fin (k + 1), if (l : ℕ) < j then
    Cd * b ^ (k - (l : ℕ)) * ρ ^ (2 * (j - (l : ℕ))) * ‖x l‖ else if j < (l : ℕ) then
    Cu * b ^ (k - (l : ℕ)) * ρ ^ (6 * ((l : ℕ) - j)) * ‖x l‖ else 0) +
  ∑ l : Fin (k + 1), if j ≤ (l : ℕ) then
    Ct * b ^ (k - (l : ℕ)) * ρ ^ (6 * ((l : ℕ) - j)) * ‖x l‖ else
    Ct * b ^ (k - (l : ℕ)) * ρ ^ (2 * (j - (l : ℕ))) * ‖x l‖

theorem completeInteractionRowSum_eq (Cu Cd Ct b ρ : ℝ) (k : ℕ) (j : Fin k) (x : ℕ → E) :
    completeInteractionRowSum Cu Cd Ct b ρ k j x =
      (Cu + Ct) * (∑ l ∈ Finset.univ.filter (fun l : Fin k => j < l),
        b ^ (k - (l : ℕ)) * ρ ^ (6 * ((l : ℕ) - j)) * ‖x l‖) +
      (Cd + Ct) * (∑ l ∈ Finset.univ.filter (fun l : Fin k => l < j),
        b ^ (k - (l : ℕ)) * ρ ^ (2 * ((j : ℕ) - l)) * ‖x l‖) +
      Ct * b ^ (k - (j : ℕ)) * ‖x j‖ + (Cu + Ct) * ρ ^ (6 * (k - (j : ℕ))) * ‖x k‖ := by
  classical
  unfold completeInteractionRowSum
  rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]
  simp only [Fin.val_castSucc, Fin.val_last]
  have hknot : ¬k < (j : ℕ) := by omega
  simp only [hknot, if_false, j.isLt, if_true, j.isLt.le, Nat.sub_self, pow_zero, mul_one]
  have hsum :
      (∑ l : Fin k, if (l : ℕ) < j then
        Cd * b ^ (k - (l : ℕ)) * ρ ^ (2 * ((j : ℕ) - l)) * ‖x l‖ else if (j : ℕ) < l then
        Cu * b ^ (k - (l : ℕ)) * ρ ^ (6 * ((l : ℕ) - j)) * ‖x l‖ else 0) +
      (∑ l : Fin k, if (j : ℕ) ≤ l then
        Ct * b ^ (k - (l : ℕ)) * ρ ^ (6 * ((l : ℕ) - j)) * ‖x l‖ else
        Ct * b ^ (k - (l : ℕ)) * ρ ^ (2 * ((j : ℕ) - l)) * ‖x l‖) =
      (Cu + Ct) * (∑ l ∈ Finset.univ.filter (fun l : Fin k => j < l),
        b ^ (k - (l : ℕ)) * ρ ^ (6 * ((l : ℕ) - j)) * ‖x l‖) +
      (Cd + Ct) * (∑ l ∈ Finset.univ.filter (fun l : Fin k => l < j),
        b ^ (k - (l : ℕ)) * ρ ^ (2 * ((j : ℕ) - l)) * ‖x l‖) +
      Ct * b ^ (k - (j : ℕ)) * ‖x j‖ := by
    rw [← Finset.sum_add_distrib]
    rw [← show (∑ l : Fin k, if l = j then Ct * b ^ (k - (j : ℕ)) * ‖x j‖ else 0) =
      Ct * b ^ (k - (j : ℕ)) * ‖x j‖ by simp]
    rw [Finset.sum_filter, Finset.sum_filter, Finset.mul_sum, Finset.mul_sum,
      ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro l hl
    rcases lt_trichotomy l j with hlj | heq | hjl
    · have hlj' : (l : ℕ) < j := hlj
      simp only [hlj', hlj, if_true, show ¬(j : ℕ) ≤ l by omega, if_false,
        show ¬j < l by omega, show l ≠ j from ne_of_lt hlj]
      ring
    · subst l
      simp
    · have hjl' : (j : ℕ) < l := hjl
      simp only [show ¬(l : ℕ) < j by omega, if_false, hjl', hjl, if_true,
        hjl'.le, show ¬l < j by omega, show l ≠ j from ne_of_gt hjl]
      ring
  calc
    _ = ((∑ l : Fin k, if (l : ℕ) < j then
        Cd * b ^ (k - (l : ℕ)) * ρ ^ (2 * ((j : ℕ) - l)) * ‖x l‖ else if (j : ℕ) < l then
        Cu * b ^ (k - (l : ℕ)) * ρ ^ (6 * ((l : ℕ) - j)) * ‖x l‖ else 0) +
      (∑ l : Fin k, if (j : ℕ) ≤ l then
        Ct * b ^ (k - (l : ℕ)) * ρ ^ (6 * ((l : ℕ) - j)) * ‖x l‖ else
        Ct * b ^ (k - (l : ℕ)) * ρ ^ (2 * ((j : ℕ) - l)) * ‖x l‖)) +
        (Cu + Ct) * ρ ^ (6 * (k - (j : ℕ))) * ‖x k‖ := by ring
    _ = _ := by rw [hsum]

theorem completeInteractionRowSum_weighted_bound {Cu Cd Ct b ρ C₀ : ℝ}
    (hu : 0 ≤ Cu) (hd : 0 ≤ Cd) (ht : 0 ≤ Ct)
    (hb : 0 < b) (hb1 : b ≤ 1) (hρ : 0 < ρ)
    (hC₀ : 1 < C₀) (hζ : C₀ * ρ ^ 8 < 1)
    (k : ℕ) (j : Fin k) (x : ℕ → E) :
    completeInteractionRowSum Cu Cd Ct b ρ k j x ≤
      (C₀ * ρ ^ 6) ^ (k - (j : ℕ)) *
        ((Ct * b + weightedInteractionRowFeedback b (Cu + Ct) (Cd + Ct) C₀ ρ) *
          weightedFamilyNorm (C₀ * ρ ^ 6) k x + (Cu + Ct) / C₀ * ‖x k‖) := by
  rw [completeInteractionRowSum_eq]
  have hup := mul_le_mul_of_nonneg_left (weighted_inner_row_sum_bound hb hb1 hC₀ hρ k x j) (add_nonneg hu ht)
  have hdown := mul_le_mul_of_nonneg_left (weighted_outer_row_sum_bound hb hb1 hC₀ hρ hζ k x j) (add_nonneg hd ht)
  have hC : 0 < C₀ := by linarith
  have hh : 0 < C₀ * ρ ^ 6 := by positivity
  have hbpow : b ^ (k - (j : ℕ)) ≤ b := by
    simpa only [pow_one] using pow_le_pow_of_le_one hb.le hb1 (show 1 ≤ k - (j : ℕ) by omega)
  have hself := mul_le_mul_of_nonneg_left
    (mul_le_mul hbpow (norm_le_weightedFamilyNorm hh k x j) (norm_nonneg _) hb.le) ht
  have hcurrent : ρ ^ (6 * (k - (j : ℕ))) ≤ (C₀ * ρ ^ 6) ^ (k - (j : ℕ)) / C₀ := by
    have hc : C₀ ≤ C₀ ^ (k - (j : ℕ)) := by
      simpa only [pow_one] using pow_le_pow_right₀ hC₀.le (show 1 ≤ k - (j : ℕ) by omega)
    rw [pow_mul]
    apply (le_div_iff₀ hC).mpr
    rw [mul_pow]
    have hm := mul_le_mul_of_nonneg_right hc (by positivity : 0 ≤ (ρ ^ 6) ^ (k - (j : ℕ)))
    nlinarith only [hm]
  have hcur := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hcurrent (norm_nonneg (x k))) (add_nonneg hu ht)
  calc
    _ ≤ (Cu + Ct) * ((C₀ * ρ ^ 6) ^ (k - (j : ℕ)) *
          (b / (C₀ - 1) * weightedFamilyNorm (C₀ * ρ ^ 6) k x)) +
        (Cd + Ct) * ((C₀ * ρ ^ 6) ^ (k - (j : ℕ)) *
          (b * (C₀ * ρ ^ 8 / (1 - C₀ * ρ ^ 8)) * weightedFamilyNorm (C₀ * ρ ^ 6) k x)) +
        Ct * (b * ((C₀ * ρ ^ 6) ^ (k - (j : ℕ)) * weightedFamilyNorm (C₀ * ρ ^ 6) k x)) +
        (Cu + Ct) * ((C₀ * ρ ^ 6) ^ (k - (j : ℕ)) / C₀ * ‖x k‖) := by
      nlinarith only [hup, hdown, hself, hcur]
    _ = _ := by unfold weightedInteractionRowFeedback; ring

end Euler2D

end
