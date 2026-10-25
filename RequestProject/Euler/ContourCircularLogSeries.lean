module

public import RequestProject.Euler.ContourCircularFourier

/-! Logarithmic Fourier coefficients strictly inside the unit disk,
proved by the actual Taylor series and dominated integration. -/

@[expose] public section

noncomputable section

open Complex MeasureTheory Set
open scoped ComplexConjugate

namespace Euler2D

theorem hasSum_contourCircular_negLog_integral {q : ℂ} (hq : ‖q‖ < 1) (k : ℤ) :
    HasSum (fun n : ℕ => (q ^ n / (n : ℂ)) *
      (if (n : ℤ) + k = 0 then (2 * Real.pi : ℂ) else 0))
      (∫ θ in (0 : ℝ)..2 * Real.pi,
        (-log (1 - q * contourCircleCharacter 1 θ)) * contourCircleCharacter k θ) := by
  let F : ℕ → ℝ → ℂ := fun n θ =>
    (q * contourCircleCharacter 1 θ) ^ n / (n : ℂ) * contourCircleCharacter k θ
  have hbound (n : ℕ) (θ : ℝ) : ‖F n θ‖ ≤ ‖q‖ ^ n := by
    dsimp only [F]
    rw [norm_mul, norm_div, norm_pow, norm_mul, norm_contourCircleCharacter,
      norm_contourCircleCharacter, mul_one, mul_one, norm_natCast]
    rcases n.eq_zero_or_pos with rfl | hn
    · simp
    · exact div_le_self (pow_nonneg (norm_nonneg q) n) (by exact_mod_cast hn)
  have hs : Summable (fun n : ℕ => ‖q‖ ^ n) :=
    summable_geometric_of_lt_one (norm_nonneg q) hq
  have hlim (θ : ℝ) : HasSum (fun n => F n θ)
      ((-log (1 - q * contourCircleCharacter 1 θ)) * contourCircleCharacter k θ) := by
    have hz : ‖q * contourCircleCharacter 1 θ‖ < 1 := by
      simpa only [norm_mul, norm_contourCircleCharacter, mul_one] using hq
    exact (hasSum_taylorSeries_neg_log hz).mul_right _
  have hi : HasSum (fun n => ∫ θ in (0 : ℝ)..2 * Real.pi, F n θ)
      (∫ θ in (0 : ℝ)..2 * Real.pi,
        (-log (1 - q * contourCircleCharacter 1 θ)) * contourCircleCharacter k θ) := by
    apply intervalIntegral.hasSum_integral_of_dominated_convergence (fun n _ => ‖q‖ ^ n)
    · intro n
      have hc : Continuous (F n) := by
        dsimp only [F]
        exact ((continuous_const.mul (continuous_contourCircleCharacter 1)).pow n).div_const _
          |>.mul (continuous_contourCircleCharacter k)
      exact hc.aestronglyMeasurable
    · intro n
      exact Filter.Eventually.of_forall (fun θ _ => hbound n θ)
    · exact Filter.Eventually.of_forall (fun _ _ => hs)
    · exact intervalIntegrable_const
    · exact Filter.Eventually.of_forall (fun θ _ => hlim θ)
  have hterm (n : ℕ) :
      (∫ θ in (0 : ℝ)..2 * Real.pi, F n θ) = (q ^ n / (n : ℂ)) *
        (if (n : ℤ) + k = 0 then (2 * Real.pi : ℂ) else 0) := by
    have he : F n = fun θ => (q ^ n / (n : ℂ)) * contourCircleCharacter ((n : ℤ) + k) θ := by
      funext θ
      dsimp only [F]
      rw [mul_pow, contourCircleCharacter_pow, ← contourCircleCharacter_mul]
      ring
    rw [he, intervalIntegral.integral_const_mul, integral_contourCircleCharacter]
  exact hi.congr_fun (fun n => (hterm n).symm)

theorem integral_contourCircular_negLog_positive {q : ℂ} (hq : ‖q‖ < 1)
    {m : ℕ} (hm : 0 < m) :
    (∫ θ in (0 : ℝ)..2 * Real.pi,
      (-log (1 - q * contourCircleCharacter 1 θ)) * contourCircleCharacter (m : ℤ) θ) = 0 := by
  have hs := hasSum_contourCircular_negLog_integral hq (m : ℤ)
  have hz : (fun n : ℕ => (q ^ n / (n : ℂ)) *
      (if (n : ℤ) + (m : ℤ) = 0 then (2 * Real.pi : ℂ) else 0)) = fun _ => 0 := by
    funext n
    have hne : (n : ℤ) + (m : ℤ) ≠ 0 := by omega
    simp only [if_neg hne, mul_zero]
  rw [hz] at hs
  exact hs.unique (hasSum_zero (β := ℕ) (α := ℂ))

theorem integral_contourCircular_negLog_negative {q : ℂ} (hq : ‖q‖ < 1)
    (m : ℕ) :
    (∫ θ in (0 : ℝ)..2 * Real.pi,
      (-log (1 - q * contourCircleCharacter 1 θ)) * contourCircleCharacter (-(m : ℤ)) θ) =
      (q ^ m / (m : ℂ)) * (2 * Real.pi : ℂ) := by
  have hs := hasSum_contourCircular_negLog_integral hq (-(m : ℤ))
  have he : (fun n : ℕ => (q ^ n / (n : ℂ)) *
      (if (n : ℤ) + -(m : ℤ) = 0 then (2 * Real.pi : ℂ) else 0)) =
      fun n => if n = m then (q ^ m / (m : ℂ)) * (2 * Real.pi : ℂ) else 0 := by
    funext n
    by_cases hnm : n = m
    · subst n
      simp
    · have hne : (n : ℤ) + -(m : ℤ) ≠ 0 := by omega
      simp only [if_neg hne, if_neg hnm, mul_zero]
  rw [he] at hs
  exact hs.unique (hasSum_ite_eq m _)

end Euler2D

end
