module

public import RequestProject.Euler.MultipoleFields
public import RequestProject.Euler.TorusCancellation

/-! Genuine volume moment bounds from support and actual L1 mass.
These apply directly to transported finite Euler labels, including
the activated child and the deeper rough cluster. -/

@[expose] public section

set_option maxHeartbeats 5000000
set_option maxRecDepth 5000

noncomputable section

open Complex Set MeasureTheory
open scoped ComplexConjugate

namespace Euler2D

theorem complex_absMoment_le_support_mass {w : ℂ → ℝ} {S A : ℝ}
    (hS : 0 ≤ S) (hw : Integrable w) (hsupp : ∀ z, S < ‖z‖ → w z = 0)
    (hA : (∫ z : ℂ, |w z|) ≤ A) (n : ℕ) :
    (∫ z : ℂ, ‖z‖ ^ n * |w z|) ≤ S ^ n * A := by
  calc
    _ ≤ ∫ z : ℂ, S ^ n * |w z| := by
      apply integral_mono (integrable_norm_pow_mul_of_supp hw hsupp n) (hw.abs.const_mul _)
      intro z
      by_cases hz : w z = 0
      · simp [hz]
      have hnorm : ‖z‖ ≤ S := le_of_not_gt (fun hlt => hz (hsupp z hlt))
      exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg z) hnorm n) (abs_nonneg _)
    _ = S ^ n * ∫ z : ℂ, |w z| := integral_const_mul _ _
    _ ≤ S ^ n * A := mul_le_mul_of_nonneg_left hA (pow_nonneg hS n)

theorem norm_complexMoment_le_support_mass {w : ℂ → ℝ} {S A : ℝ}
    (hS : 0 ≤ S) (hw : Integrable w) (hsupp : ∀ z, S < ‖z‖ → w z = 0)
    (hA : (∫ z : ℂ, |w z|) ≤ A) (n : ℕ) :
    ‖momentN w n‖ ≤ S ^ n * A := by
  unfold momentN
  calc
    _ ≤ ∫ z : ℂ, ‖(w z : ℂ) * conj z ^ n‖ := norm_integral_le_integral_norm _
    _ = ∫ z : ℂ, ‖z‖ ^ n * |w z| := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun z => by
        change ‖(w z : ℂ) * conj z ^ n‖ = ‖z‖ ^ n * |w z|
        rw [norm_mul, norm_pow, norm_conj, Complex.norm_real, Real.norm_eq_abs, mul_comm])
    _ ≤ _ := complex_absMoment_le_support_mass hS hw hsupp hA n

end Euler2D

end
