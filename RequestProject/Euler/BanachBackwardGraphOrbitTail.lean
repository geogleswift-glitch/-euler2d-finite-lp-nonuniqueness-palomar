module

public import RequestProject.Euler.BanachLocalBackwardGraph

/-! Every already constructed weighted ancient orbit eventually lies
on the same unique local graph. The original orbit is retained. -/

@[expose] public section

set_option maxHeartbeats 2000000

noncomputable section

open Set Filter Topology Metric

namespace Euler2D

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

namespace IsLocalWeightedBackwardGraph

variable {F : E → E} {P : E →L[ℝ] E} {ρ r : ℝ} {x : E → ℕ → E}

theorem exists_orbit_tail_eq (h : IsLocalWeightedBackwardGraph F P ρ r x)
    (hρ : 1 < ρ) (hr : 0 < r) (hP : ∀ v, P (P v) = P v)
    (y : ℕ → E) (hback : ∀ n, F (y (n + 1)) = y n)
    {C : ℝ} (hnorm : ∀ n, ‖y n‖ ≤ C * (ρ⁻¹) ^ n) :
    ∃ N : ℕ, ∀ n ≥ N, ‖P (y n)‖ ≤ r / 2 ∧
      x (P (y n)) = (fun k => y (n + k)) := by
  have hρ0 : 0 < ρ := zero_lt_one.trans hρ
  have hC : 0 ≤ C := by
    have hh := hnorm 0
    simp only [pow_zero, mul_one] at hh
    exact (norm_nonneg _).trans hh
  have hi0 : 0 ≤ ρ⁻¹ := inv_nonneg.mpr hρ0.le
  have hi1 : ρ⁻¹ < 1 := by
    simpa only [one_div, inv_one] using (one_div_lt_one_div_of_lt zero_lt_one hρ)
  have ht : Tendsto (fun n : ℕ => ((‖P‖ + 1) * C) * (ρ⁻¹) ^ n) atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one hi0 hi1).const_mul ((‖P‖ + 1) * C)
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    (ht.eventually (eventually_lt_nhds (half_pos hr)))
  refine ⟨N, ?_⟩
  intro n hn
  have hp : 0 ≤ (ρ⁻¹) ^ n := pow_nonneg hi0 n
  have hsmall : ((‖P‖ + 1) * C) * (ρ⁻¹) ^ n < r / 2 := hN n hn
  have hbase : C * (ρ⁻¹) ^ n ≤ r := by
    have hm : C * (ρ⁻¹) ^ n ≤ ((‖P‖ + 1) * C) * (ρ⁻¹) ^ n := by
      nlinarith [norm_nonneg P, mul_nonneg hC hp]
    linarith
  have hproj : ‖P (y n)‖ ≤ r / 2 := by
    calc
      _ ≤ ‖P‖ * ‖y n‖ := P.le_opNorm _
      _ ≤ ‖P‖ * (C * (ρ⁻¹) ^ n) :=
        mul_le_mul_of_nonneg_left (hnorm n) (norm_nonneg P)
      _ ≤ r / 2 := by nlinarith [mul_nonneg hC hp]
  refine ⟨hproj, ?_⟩
  symm
  apply h.unique _ (hP _) hproj
  · intro k
    simpa only [Nat.add_assoc] using hback (n + k)
  · intro k
    calc
      _ ≤ C * (ρ⁻¹) ^ (n + k) := hnorm _
      _ = (C * (ρ⁻¹) ^ n) * (ρ⁻¹) ^ k := by rw [pow_add]; ring
      _ ≤ r * (ρ⁻¹) ^ k := mul_le_mul_of_nonneg_right hbase (pow_nonneg hi0 k)
  · simp only [add_zero]

end IsLocalWeightedBackwardGraph

end Euler2D

end
