module

public import RequestProject.Euler.BoundedVelocityMollification

/-! Positive mass-one spatial smoothing preserves the actual speed and
logarithmic spatial modulus, and approximates the field uniformly on the
entire plane and at every time. -/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal Convolution

namespace Euler2D

theorem boundedVelocityMollification_logFlowModulus_le
    {φ : R2 → ℝ} {v : ℝ → R2 → R2} {M C : ℝ}
    (hφ : Integrable φ) (hφpos : ∀ y, 0 ≤ φ y) (hφone : (∫ y, φ y) = 1)
    (hv : Continuous (Function.uncurry v)) (hM : ∀ t x, ‖v t x‖ ≤ M)
    (hlip : ∀ t x z, ‖x - z‖ ≤ 1 / 2 →
      ‖v t x - v t z‖ ≤ C * logFlowModulus ‖x - z‖)
    (t : ℝ) {x z : R2} (hxz : ‖x - z‖ ≤ 1 / 2) :
    ‖boundedVelocityMollification φ v t x - boundedVelocityMollification φ v t z‖ ≤
      C * logFlowModulus ‖x - z‖ := by
  change ‖(∫ y, φ y • v t (x - y)) - (∫ y, φ y • v t (z - y))‖ ≤ _
  rw [← integral_sub (integrable_boundedVelocityMollification_integrand hφ hv hM t x)
    (integrable_boundedVelocityMollification_integrand hφ hv hM t z)]
  have hb (y : R2) : ‖φ y • v t (x - y) - φ y • v t (z - y)‖ ≤
      φ y * (C * logFlowModulus ‖x - z‖) := by
    rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_nonneg (hφpos y)]
    apply mul_le_mul_of_nonneg_left _ (hφpos y)
    have hd : (x - y) - (z - y) = x - z := by abel
    simpa only [hd] using hlip t (x - y) (z - y) (by simpa only [hd] using hxz)
  calc
    _ ≤ ∫ y, φ y * (C * logFlowModulus ‖x - z‖) :=
      norm_integral_le_of_norm_le (hφ.mul_const _) (ae_of_all _ hb)
    _ = _ := by rw [integral_mul_const, hφone, one_mul]

theorem norm_boundedVelocityMollification_sub_le
    {φ : R2 → ℝ} {v : ℝ → R2 → R2} {M C ε : ℝ}
    (hφ : Integrable φ) (hφpos : ∀ y, 0 ≤ φ y) (hφone : (∫ y, φ y) = 1)
    (hφsupp : ∀ y, ε ≤ ‖y‖ → φ y = 0)
    (hv : Continuous (Function.uncurry v)) (hM : ∀ t x, ‖v t x‖ ≤ M)
    (hC : 0 ≤ C) (hε : 0 < ε) (hεhalf : ε ≤ 1 / 2)
    (hlip : ∀ t x z, ‖x - z‖ ≤ 1 / 2 →
      ‖v t x - v t z‖ ≤ C * logFlowModulus ‖x - z‖)
    (t : ℝ) (x : R2) :
    ‖boundedVelocityMollification φ v t x - v t x‖ ≤ C * logFlowModulus ε := by
  have he : (∫ y, φ y • v t x) = v t x := by
    rw [integral_smul_const, hφone, one_smul]
  change ‖(∫ y, φ y • v t (x - y)) - v t x‖ ≤ _
  rw [← he, ← integral_sub (integrable_boundedVelocityMollification_integrand hφ hv hM t x)
    (hφ.smul_const (v t x))]
  have hb (y : R2) : ‖φ y • v t (x - y) - φ y • v t x‖ ≤ φ y * (C * logFlowModulus ε) := by
    by_cases hnear : ‖y‖ < ε
    · rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_nonneg (hφpos y)]
      have hd : ‖x - y - x‖ = ‖y‖ := by rw [sub_right_comm, sub_self, zero_sub, norm_neg]
      have hvb := hlip t (x - y) x (by rw [hd]; exact hnear.le.trans hεhalf)
      rw [hd] at hvb
      have hmod := monotoneOn_logFlowModulus
        ⟨norm_nonneg y, by linarith⟩ ⟨hε.le, by linarith⟩ hnear.le
      exact mul_le_mul_of_nonneg_left
        (hvb.trans (mul_le_mul_of_nonneg_left hmod hC)) (hφpos y)
    · rw [hφsupp y (not_lt.mp hnear), zero_smul, zero_smul, sub_self, norm_zero, zero_mul]
  calc
    _ ≤ ∫ y, φ y * (C * logFlowModulus ε) :=
      norm_integral_le_of_norm_le (hφ.mul_const _) (ae_of_all _ hb)
    _ = _ := by rw [integral_mul_const, hφone, one_mul]

end Euler2D
