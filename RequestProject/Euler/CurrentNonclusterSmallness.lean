module

public import RequestProject.Euler.CurrentPrefixRowSums

/-! The actual noncluster budget retains its small source factors.
Fine weighted control K=Kw*h, h=C0*rho^6, makes the ancestor part
rho^14. The periodic self and deep terms have the same bound when
R<=rho. The explicit coefficient is independent of physical scales. -/

@[expose] public section

set_option maxHeartbeats 5000000

noncomputable section

namespace Euler2D

theorem current_noncluster_budget_le_rhoFourteen
    {b C₀ Kw Kcur O V J Cb R ρ D q : ℝ}
    (hb : 0 < b) (hC₀ : 0 ≤ C₀) (hKw : 0 ≤ Kw) (hKcur : 0 ≤ Kcur)
    (hO : 0 ≤ O) (hV : 0 ≤ V) (hJ : 0 ≤ J)
    (hR : 0 ≤ R) (hRρ : R ≤ ρ) (hρ : 0 ≤ ρ) (hD : 0 ≤ D)
    (hq : q ≤ Kcur * (C₀ * ρ ^ 6)) :
    V * R ^ 8 * q +
        ((2 * b * C₀ * (Kw * (C₀ * ρ ^ 6)) * (O + V)) * ρ ^ 2) * ρ ^ 6 * (1 + D) ^ 4 +
        (2 / b) * J * Cb ^ 4 * R ^ 8 * ρ ^ 6 * (1 + D) ^ 4 ≤
      (V * Kcur * C₀ + 2 * b * C₀ ^ 2 * Kw * (O + V) + (2 / b) * J * Cb ^ 4) *
        ρ ^ 14 * (1 + D) ^ 4 := by
  have hR8 : R ^ 8 ≤ ρ ^ 8 := pow_le_pow_left₀ hR hRρ 8
  have hP : (1 : ℝ) ≤ (1 + D) ^ 4 := one_le_pow₀ (by linarith only [hD])
  have hself : V * R ^ 8 * q ≤ (V * Kcur * C₀) * ρ ^ 14 * (1 + D) ^ 4 := by
    calc
      _ ≤ V * R ^ 8 * (Kcur * (C₀ * ρ ^ 6)) :=
        mul_le_mul_of_nonneg_left hq (mul_nonneg hV (by positivity))
      _ ≤ V * ρ ^ 8 * (Kcur * (C₀ * ρ ^ 6)) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hR8 hV) (by positivity)
      _ = (V * Kcur * C₀) * ρ ^ 14 := by ring
      _ ≤ _ := by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left hP
          (show 0 ≤ (V * Kcur * C₀) * ρ ^ 14 by positivity)
  have hdeep : (2 / b) * J * Cb ^ 4 * R ^ 8 * ρ ^ 6 * (1 + D) ^ 4 ≤
      ((2 / b) * J * Cb ^ 4) * ρ ^ 14 * (1 + D) ^ 4 := by
    calc
      _ ≤ (2 / b) * J * Cb ^ 4 * ρ ^ 8 * ρ ^ 6 * (1 + D) ^ 4 :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hR8 (by positivity)) (by positivity)) (by positivity)
      _ = _ := by ring
  have houter : ((2 * b * C₀ * (Kw * (C₀ * ρ ^ 6)) * (O + V)) * ρ ^ 2) * ρ ^ 6 * (1 + D) ^ 4 =
      (2 * b * C₀ ^ 2 * Kw * (O + V)) * ρ ^ 14 * (1 + D) ^ 4 := by ring
  exact (add_le_add (add_le_add hself (le_of_eq houter)) hdeep).trans_eq (by ring)

end Euler2D

end
