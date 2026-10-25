module

public import RequestProject.Euler.PolynomialForcingTail

/-! The actual parent clock u=b*s gives the same fixed child-time
entrance for the exponentially weighted polynomial tail. -/

@[expose] public section

set_option maxHeartbeats 3000000

noncomputable section

open Filter Topology Set MeasureTheory

namespace Euler2D

theorem polynomialForcingTail_mul_clock {σ b S : ℝ}
    (hσ : 0 < σ) (hb : 0 < b) (hb1 : b ≤ 1) (hS : 0 ≤ S) :
    polynomialForcingTail σ (b * S) ≤ b * polynomialForcingTail (b * σ) S := by
  let g : ℝ → ℝ := fun u => Real.exp (-σ * u) * (1 + u) ^ 4
  have hg : IntegrableOn g (Ioi (b * S)) :=
    (integrableOn_exponential_polynomial_four hσ).mono_set
      (fun u hu => (mul_nonneg hb.le hS).trans hu.le)
  have hgcomp : IntegrableOn (fun s => g (b * s)) (Ioi S) :=
    (integrableOn_Ioi_comp_mul_left_iff g S hb).mpr hg
  have ht : IntegrableOn (fun s : ℝ => Real.exp (-(b * σ) * s) * (1 + s) ^ 4) (Ioi S) :=
    (integrableOn_exponential_polynomial_four (mul_pos hb hσ)).mono_set
      (fun u hu => hS.trans hu.le)
  have hle : (∫ s in Ioi S, g (b * s)) ≤
      ∫ s in Ioi S, Real.exp (-(b * σ) * s) * (1 + s) ^ 4 := by
    apply integral_mono_ae hgcomp ht
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    have hs0 : 0 ≤ s := hS.trans hs.le
    have hbs : b * s ≤ s := by nlinarith only [mul_le_mul_of_nonneg_right hb1 hs0]
    have hp : (1 + b * s) ^ 4 ≤ (1 + s) ^ 4 :=
      pow_le_pow_left₀ (by positivity) (by linarith) 4
    dsimp only [g]
    rw [show -σ * (b * s) = -(b * σ) * s by ring]
    exact mul_le_mul_of_nonneg_left hp (Real.exp_pos _).le
  have hchange : polynomialForcingTail σ (b * S) = b * (∫ s in Ioi S, g (b * s)) := by
    rw [integral_comp_mul_left_Ioi g S hb]
    simp only [smul_eq_mul]
    rw [← mul_assoc, mul_inv_cancel₀ hb.ne', one_mul]
    exact integral_Ici_eq_integral_Ioi
  rw [hchange]
  unfold polynomialForcingTail
  rw [integral_Ici_eq_integral_Ioi]
  exact mul_le_mul_of_nonneg_left hle hb.le

end Euler2D

end

