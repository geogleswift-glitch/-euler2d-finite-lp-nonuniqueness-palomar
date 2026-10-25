module

public import RequestProject.Euler.CircularCaptureSeedClock
public import RequestProject.Euler.CircularAncestorTimeRescaling

/-! Actual finite stage durations retain the original physical clock.
Their common normalized upper bound produces the genuine geometric
1/(1-b) cumulative horizon and its slow-ancestor Gronwall factor. -/

@[expose] public section

set_option maxHeartbeats 3000000

noncomputable section

open Filter Topology

namespace Euler2D

theorem finite_circular_cumulative_stage_time_le {A₀ b D : ℝ}
    (hA : 0 < A₀) (hb : 0 < b) (hb1 : b < 1) (hD : 0 ≤ D)
    (duration : ℕ → ℝ) (k M : ℕ)
    (hduration : ∀ n < M, duration (k + n) ≤ D / ampScale A₀ b (k + n)) :
    ∑ n ∈ Finset.range M, duration (k + n) ≤ D / ((1 - b) * ampScale A₀ b k) := by
  have hAk : 0 < ampScale A₀ b k := div_pos hA (pow_pos hb k)
  have hsum : ∑ n ∈ Finset.range M, b ^ n ≤ (1 - b)⁻¹ := by
    rw [← tsum_geometric_of_lt_one hb.le hb1]
    exact (summable_geometric_of_lt_one hb.le hb1).sum_le_tsum _ (fun n _ => pow_nonneg hb.le n)
  calc
    _ ≤ ∑ n ∈ Finset.range M, D / ampScale A₀ b (k + n) :=
      Finset.sum_le_sum (fun n hn => hduration n (Finset.mem_range.mp hn))
    _ = ∑ n ∈ Finset.range M, (D / ampScale A₀ b k) * b ^ n := by
      apply Finset.sum_congr rfl
      intro n _
      unfold ampScale
      rw [pow_add]
      field_simp
      <;> ring
    _ = (D / ampScale A₀ b k) * ∑ n ∈ Finset.range M, b ^ n := by rw [Finset.mul_sum]
    _ ≤ (D / ampScale A₀ b k) * (1 - b)⁻¹ :=
      mul_le_mul_of_nonneg_left hsum (div_nonneg hD hAk.le)
    _ = _ := by
      field_simp [hAk.ne', (sub_pos.mpr hb1).ne']
      <;> ring

theorem retarded_response_factor_mono {b K t u : ℝ} (hb : 0 ≤ b) (hK : 0 ≤ K)
    (ht : 0 ≤ t) (htu : t ≤ u) :
    b * t * Real.exp (b * K * t) ≤ b * u * Real.exp (b * K * u) := by
  exact mul_le_mul (mul_le_mul_of_nonneg_left htu hb)
    (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left htu (mul_nonneg hb hK)))
    (Real.exp_pos _).le (mul_nonneg hb (ht.trans htu))

theorem cumulative_actual_response_factor_le {b K A H D : ℝ}
    (hb : 0 ≤ b) (hb1 : b < 1) (hK : 0 ≤ K) (hA : 0 < A) (hH : 0 ≤ H)
    (htime : H ≤ D / ((1 - b) * A)) :
    b * A * H * Real.exp (b * A * K * H) ≤
      b * (D / (1 - b)) * Real.exp (b * K * (D / (1 - b))) := by
  have hAu : A * H ≤ D / (1 - b) := by
    have hh := (le_div_iff₀ (mul_pos (sub_pos.mpr hb1) hA)).mp htime
    apply (le_div_iff₀ (sub_pos.mpr hb1)).mpr
    nlinarith only [hh]
  have hh := retarded_response_factor_mono hb hK (mul_nonneg hA.le hH) hAu
  convert hh using 1 <;> ring

end Euler2D

end
