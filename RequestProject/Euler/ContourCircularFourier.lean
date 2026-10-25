module

public import Mathlib

/-! Actual integer characters and logarithmic Fourier integrals on
the reference circle. -/

@[expose] public section

noncomputable section

open Complex MeasureTheory
open scoped ComplexConjugate

namespace Euler2D

def contourCircleCharacter (k : ℤ) (θ : ℝ) : ℂ :=
  exp ((k : ℂ) * (θ : ℂ) * I)

@[simp] theorem contourCircleCharacter_zero (θ : ℝ) : contourCircleCharacter 0 θ = 1 := by
  simp [contourCircleCharacter]

@[simp] theorem norm_contourCircleCharacter (k : ℤ) (θ : ℝ) :
    ‖contourCircleCharacter k θ‖ = 1 := by
  rw [contourCircleCharacter, norm_exp]
  simp [mul_assoc]

theorem contourCircleCharacter_mul (k l : ℤ) (θ : ℝ) :
    contourCircleCharacter k θ * contourCircleCharacter l θ =
      contourCircleCharacter (k + l) θ := by
  simp only [contourCircleCharacter, ← exp_add, Int.cast_add]
  congr 1
  ring

theorem contourCircleCharacter_pow (n : ℕ) (θ : ℝ) :
    contourCircleCharacter 1 θ ^ n = contourCircleCharacter (n : ℤ) θ := by
  rw [contourCircleCharacter, ← exp_nat_mul, contourCircleCharacter]
  simp [mul_assoc]

@[simp] theorem conj_contourCircleCharacter (k : ℤ) (θ : ℝ) :
    conj (contourCircleCharacter k θ) = contourCircleCharacter (-k) θ := by
  rw [contourCircleCharacter, ← exp_conj, contourCircleCharacter]
  congr 1
  simp

theorem continuous_contourCircleCharacter (k : ℤ) : Continuous (contourCircleCharacter k) := by
  unfold contourCircleCharacter
  fun_prop

theorem integral_contourCircleCharacter (k : ℤ) :
    ∫ θ in (0 : ℝ)..2 * Real.pi, contourCircleCharacter k θ =
      if k = 0 then (2 * Real.pi : ℂ) else 0 := by
  by_cases hk : k = 0
  · subst k
    simp
  · rw [if_neg hk]
    have hc : (k : ℂ) * I ≠ 0 := mul_ne_zero (by exact_mod_cast hk) I_ne_zero
    have he : contourCircleCharacter k = fun θ : ℝ => exp (((k : ℂ) * I) * θ) := by
      funext θ
      unfold contourCircleCharacter
      congr 1
      ring
    rw [he, integral_exp_mul_complex hc]
    have hp : exp (((k : ℂ) * I) * ((2 * Real.pi : ℝ) : ℂ)) = 1 := by
      rw [show ((k : ℂ) * I) * ((2 * Real.pi : ℝ) : ℂ) =
        (k : ℂ) * (2 * Real.pi * I) by push_cast; ring]
      exact exp_int_mul_two_pi_mul_I k
    rw [hp]
    simp

end Euler2D

end
