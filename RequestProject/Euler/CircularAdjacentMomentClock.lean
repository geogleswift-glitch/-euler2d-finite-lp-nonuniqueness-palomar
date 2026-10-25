module

public import RequestProject.Euler.CircularFiniteAncestorRigidVelocity
public import RequestProject.Euler.CircularAncestorTimeRescaling

/-! Exact adjacent-scale factors and the actual ancestor rotation
phase. On the child's clock the parent's fourth-moment force has
coefficient rho^6 and oscillation exp(-2 i b tau). -/

@[expose] public section

set_option maxHeartbeats 6000000
set_option maxRecDepth 6000

noncomputable section

open Complex
open scoped NNReal

namespace Euler2D

theorem ampScale_succ_eq_div (A₀ b : ℝ) (k : ℕ) :
    ampScale A₀ b (k + 1) = ampScale A₀ b k / b := by
  simp only [ampScale, pow_succ, div_div]

theorem radScale_succ_eq_mul (R ρ : ℝ) (k : ℕ) :
    radScale R ρ (k + 1) = radScale R ρ k * ρ := by
  simp only [radScale, pow_succ]
  ring

theorem finiteAncestorAngularVelocity_succ (A₀ b : ℝ) (k : ℕ) :
    finiteAncestorAngularVelocity A₀ b (k + 1) =
      finiteAncestorAngularVelocity A₀ b k + ampScale A₀ b k / 2 := by
  unfold finiteAncestorAngularVelocity
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.val_castSucc, Fin.val_last]
  ring

theorem adjacent_ancestor_angular_rate_child_clock {A₀ b : ℝ}
    (hA : A₀ ≠ 0) (hb : b ≠ 0) (k : ℕ) :
    finiteAncestorAngularVelocity A₀ b (k + 1) / ampScale A₀ b (k + 1) =
      finiteAncestorAngularVelocity A₀ b k / ampScale A₀ b (k + 1) + b / 2 := by
  have hratio : ampScale A₀ b k / ampScale A₀ b (k + 1) = b := by
    simpa using ampScale_ratio_eq_pow hA hb (Nat.le_succ k)
  rw [finiteAncestorAngularVelocity_succ]
  calc
    _ = finiteAncestorAngularVelocity A₀ b k / ampScale A₀ b (k + 1) +
        (ampScale A₀ b k / ampScale A₀ b (k + 1)) / 2 := by ring
    _ = _ := by rw [hratio]

theorem adjacent_fourth_moment_phase_child_clock {A₀ b : ℝ}
    (hA : A₀ ≠ 0) (hb : b ≠ 0) (k : ℕ) (θp θc τ : ℝ) :
    Complex.exp (4 * ((θp + finiteAncestorAngularVelocity A₀ b k /
        ampScale A₀ b (k + 1) * τ : ℝ) : ℂ) * I) *
      Complex.exp (-(4 * ((θc + finiteAncestorAngularVelocity A₀ b (k + 1) /
        ampScale A₀ b (k + 1) * τ : ℝ) : ℂ) * I)) =
      Complex.exp (4 * ((θp - θc : ℝ) : ℂ) * I) *
        Complex.exp (-((2 * b * τ : ℝ) : ℂ) * I) := by
  rw [adjacent_ancestor_angular_rate_child_clock hA hb k]
  rw [← Complex.exp_add, ← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem adjacent_normalized_fourth_moment_coefficient {A₀ b R ρ : ℝ}
    (hA : A₀ ≠ 0) (hb : b ≠ 0) (hR : R ≠ 0) (hρ : ρ ≠ 0)
    (k : ℕ) (θp θc : ℝ) (M : ℂ) :
    (b : ℂ) * (((ampScale A₀ b k)⁻¹ : ℂ) * ((radScale R ρ k)⁻¹ : ℂ) ^ 6 *
      Complex.exp (4 * (θp : ℂ) * I) *
        ((ampScale A₀ b (k + 1) : ℂ) * (radScale R ρ (k + 1) : ℂ) ^ 6 *
          Complex.exp (-(4 * (θc : ℂ) * I)) * M)) =
      (ρ : ℂ) ^ 6 * Complex.exp (4 * ((θp - θc : ℝ) : ℂ) * I) * M := by
  have hphase : Complex.exp (4 * (θp : ℂ) * I) * Complex.exp (-(4 * (θc : ℂ) * I)) =
      Complex.exp (4 * ((θp - θc : ℝ) : ℂ) * I) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [ampScale_succ_eq_div, radScale_succ_eq_mul]
  push_cast
  rw [show Complex.exp (4 * (((θp : ℂ) - (θc : ℂ))) * I) =
      Complex.exp (4 * (θp : ℂ) * I) * Complex.exp (-(4 * (θc : ℂ) * I)) from
        (by simpa only [Complex.ofReal_sub] using hphase.symm)]
  have hap : ampScale A₀ b k ≠ 0 := div_ne_zero hA (pow_ne_zero k hb)
  have hrp : radScale R ρ k ≠ 0 := mul_ne_zero hR (pow_ne_zero k hρ)
  field_simp [Complex.ofReal_ne_zero.mpr hap, Complex.ofReal_ne_zero.mpr hrp,
    Complex.ofReal_ne_zero.mpr hb]
  <;> ring

end Euler2D

end
