module

public import Mathlib.Analysis.ODE.Gronwall

@[expose] public section

noncomputable section

namespace Euler2D

theorem gronwallBound_le_add_mul_exp {δ K ε t : ℝ} (hK : 0 ≤ K) (hε : 0 ≤ ε)
    (ht : 0 ≤ t) :
    gronwallBound δ K ε t ≤ (δ + ε * t) * Real.exp (K * t) := by
  by_cases hK0 : K = 0
  · simp [hK0, gronwallBound_K0]
  have hKp : 0 < K := lt_of_le_of_ne hK (Ne.symm hK0)
  have hmul := mul_le_mul_of_nonneg_right (Real.add_one_le_exp (-(K * t)))
    (Real.exp_pos (K * t)).le
  have he : Real.exp (-(K * t)) * Real.exp (K * t) = 1 := by
    rw [← Real.exp_add]
    simp
  have hh : Real.exp (K * t) - 1 ≤ K * (t * Real.exp (K * t)) := by
    rw [he] at hmul
    nlinarith only [hmul]
  rw [gronwallBound_of_K_ne_0 hK0]
  have hh' := mul_le_mul_of_nonneg_left hh (div_nonneg hε hK)
  have he' : (ε / K) * (K * (t * Real.exp (K * t))) = ε * t * Real.exp (K * t) := by
    field_simp
  rw [he'] at hh'
  nlinarith only [hh']

theorem gronwallBound_zero_initial_linear (K ε t : ℝ) :
    gronwallBound 0 K ε t = ε * gronwallBound 0 K 1 t := by
  unfold gronwallBound
  split_ifs <;> ring

end Euler2D

end
