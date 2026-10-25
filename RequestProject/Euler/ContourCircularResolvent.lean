module

public import RequestProject.Euler.ContourCircularKernel

/-! Actual circular rational-kernel Fourier coefficients, obtained by
dominated integration of the genuine geometric series. These accompany
the logarithmic coefficients in the shape derivative calculation. -/

@[expose] public section

noncomputable section

open Complex MeasureTheory Set

namespace Euler2D

theorem hasSum_contourCircular_resolvent_integral {q : ℂ} (hq : ‖q‖ < 1) (k : ℤ) :
    HasSum (fun n : ℕ => q ^ n *
      (if (n : ℤ) + k = 0 then (2 * Real.pi : ℂ) else 0))
      (∫ θ in (0 : ℝ)..2 * Real.pi,
        (1 - q * contourCircleCharacter 1 θ)⁻¹ * contourCircleCharacter k θ) := by
  let F : ℕ → ℝ → ℂ := fun n θ =>
    (q * contourCircleCharacter 1 θ) ^ n * contourCircleCharacter k θ
  have hbound (n : ℕ) (θ : ℝ) : ‖F n θ‖ ≤ ‖q‖ ^ n := by
    dsimp only [F]
    simp only [norm_mul, norm_pow, norm_contourCircleCharacter, mul_one, le_refl]
  have hs : Summable (fun n : ℕ => ‖q‖ ^ n) :=
    summable_geometric_of_lt_one (norm_nonneg q) hq
  have hlim (θ : ℝ) : HasSum (fun n => F n θ)
      ((1 - q * contourCircleCharacter 1 θ)⁻¹ * contourCircleCharacter k θ) := by
    have hz : ‖q * contourCircleCharacter 1 θ‖ < 1 := by
      simpa only [norm_mul, norm_contourCircleCharacter, mul_one] using hq
    exact (hasSum_geometric_of_norm_lt_one hz).mul_right _
  have hi : HasSum (fun n => ∫ θ in (0 : ℝ)..2 * Real.pi, F n θ)
      (∫ θ in (0 : ℝ)..2 * Real.pi,
        (1 - q * contourCircleCharacter 1 θ)⁻¹ * contourCircleCharacter k θ) := by
    apply intervalIntegral.hasSum_integral_of_dominated_convergence (fun n _ => ‖q‖ ^ n)
    · intro n
      have hc : Continuous (F n) := by
        dsimp only [F]
        exact ((continuous_const.mul (continuous_contourCircleCharacter 1)).pow n).mul
          (continuous_contourCircleCharacter k)
      exact hc.aestronglyMeasurable
    · intro n
      exact Filter.Eventually.of_forall (fun θ _ => hbound n θ)
    · exact Filter.Eventually.of_forall (fun _ _ => hs)
    · exact intervalIntegrable_const
    · exact Filter.Eventually.of_forall (fun θ _ => hlim θ)
  have hterm (n : ℕ) :
      (∫ θ in (0 : ℝ)..2 * Real.pi, F n θ) = q ^ n *
        (if (n : ℤ) + k = 0 then (2 * Real.pi : ℂ) else 0) := by
    have he : F n = fun θ => q ^ n * contourCircleCharacter ((n : ℤ) + k) θ := by
      funext θ
      dsimp only [F]
      rw [mul_pow, contourCircleCharacter_pow, ← contourCircleCharacter_mul]
      ring
    rw [he, intervalIntegral.integral_const_mul, integral_contourCircleCharacter]
  exact hi.congr_fun (fun n => (hterm n).symm)

theorem integral_contourCircular_resolvent_positive {q : ℂ} (hq : ‖q‖ < 1)
    {m : ℕ} (hm : 0 < m) :
    (∫ θ in (0 : ℝ)..2 * Real.pi,
      (1 - q * contourCircleCharacter 1 θ)⁻¹ * contourCircleCharacter (m : ℤ) θ) = 0 := by
  have hs := hasSum_contourCircular_resolvent_integral hq (m : ℤ)
  have hz : (fun n : ℕ => q ^ n *
      (if (n : ℤ) + (m : ℤ) = 0 then (2 * Real.pi : ℂ) else 0)) = fun _ => 0 := by
    funext n
    have hne : (n : ℤ) + (m : ℤ) ≠ 0 := by omega
    simp only [if_neg hne, mul_zero]
  rw [hz] at hs
  exact hs.unique (hasSum_zero (β := ℕ) (α := ℂ))

theorem integral_contourCircular_resolvent_negative {q : ℂ} (hq : ‖q‖ < 1) (m : ℕ) :
    (∫ θ in (0 : ℝ)..2 * Real.pi,
      (1 - q * contourCircleCharacter 1 θ)⁻¹ * contourCircleCharacter (-(m : ℤ)) θ) =
      q ^ m * (2 * Real.pi : ℂ) := by
  have hs := hasSum_contourCircular_resolvent_integral hq (-(m : ℤ))
  have he : (fun n : ℕ => q ^ n *
      (if (n : ℤ) + -(m : ℤ) = 0 then (2 * Real.pi : ℂ) else 0)) =
      fun n => if n = m then q ^ m * (2 * Real.pi : ℂ) else 0 := by
    funext n
    by_cases hnm : n = m
    · subst n
      simp
    · have hne : (n : ℤ) + -(m : ℤ) ≠ 0 := by omega
      simp only [if_neg hne, if_neg hnm, mul_zero]
  rw [he] at hs
  exact hs.unique (hasSum_ite_eq m _)

theorem integral_contourCircular_resolvent_symmetric (q : ℂ) (k : ℤ) :
    (∫ θ in (-Real.pi : ℝ)..Real.pi,
      (1 - q * contourCircleCharacter 1 θ)⁻¹ * contourCircleCharacter k θ) =
      ∫ θ in (0 : ℝ)..2 * Real.pi,
        (1 - q * contourCircleCharacter 1 θ)⁻¹ * contourCircleCharacter k θ := by
  have hp : Function.Periodic (fun θ =>
      (1 - q * contourCircleCharacter 1 θ)⁻¹ * contourCircleCharacter k θ) (2 * Real.pi) := by
    intro θ
    dsimp only
    rw [periodic_contourCircleCharacter 1 θ, periodic_contourCircleCharacter k θ]
  have he := hp.intervalIntegral_add_eq (-Real.pi) 0
  convert he using 1 <;> congr 1 <;> ring

end Euler2D

end
