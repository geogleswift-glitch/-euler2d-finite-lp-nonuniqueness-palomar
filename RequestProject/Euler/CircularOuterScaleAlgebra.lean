module

public import RequestProject.Euler.CircularFinitePlanarVelocityDecomposition

/-! The exact original amplitude/radius scales turn actual outer
feedback coefficients into the convergent ancestor geometric series. -/

@[expose] public section

set_option maxHeartbeats 1800000

noncomputable section

open MeasureTheory Set
open scoped NNReal ENNReal

namespace Euler2D

theorem outer_radial_scale_identity {A₀ b R ρ : ℝ}
    (hb : 0 < b) (hR : 0 < R) (hρ : 0 < ρ) {j k : ℕ} (hjk : j ≤ k) :
    ampScale A₀ b j / radScale R ρ j ^ 2 =
      (ampScale A₀ b k / radScale R ρ k ^ 2) * (b * ρ ^ 2) ^ (k - j) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hjk
  simp only [ampScale, radScale, Nat.add_sub_cancel_left, pow_add, mul_pow]
  have hpow : (ρ ^ 2) ^ n = (ρ ^ n) ^ 2 := by simp only [← pow_mul, Nat.mul_comm]
  rw [hpow]
  field_simp [hb.ne', hR.ne', hρ.ne']
  <;> ring

theorem outer_contour_scale_identity {A₀ b R ρ : ℝ}
    (hA : 0 < A₀) (hb : 0 < b) (hR : 0 < R) (hρ : 0 < ρ) {j k : ℕ} (hjk : j ≤ k) :
    (ampScale A₀ b j * (radScale R ρ k / radScale R ρ j) ^ 2) / ampScale A₀ b k =
      (b * ρ ^ 2) ^ (k - j) := by
  have hAj : 0 < ampScale A₀ b k := by unfold ampScale; positivity
  have hrj := radScale_pos hR hρ j
  have hrk := radScale_pos hR hρ k
  calc
    _ = (ampScale A₀ b j / radScale R ρ j ^ 2) *
        (radScale R ρ k ^ 2 / ampScale A₀ b k) := by field_simp [hrj.ne', hAj.ne'] <;> ring
    _ = _ := by
      rw [outer_radial_scale_identity hb hR hρ hjk]
      field_simp [hrk.ne', hAj.ne']

theorem sum_outer_radial_scales_le {A₀ b R ρ : ℝ}
    (hA : 0 ≤ A₀) (hb : 0 < b) (hR : 0 < R) (hρ : 0 < ρ) (hsmall : b * ρ ^ 2 < 1) (k : ℕ) :
    (∑ j ∈ Finset.range (k + 1), ampScale A₀ b j / radScale R ρ j ^ 2) ≤
      (ampScale A₀ b k / radScale R ρ k ^ 2) / (1 - b * ρ ^ 2) := by
  have hκ : 0 ≤ b * ρ ^ 2 := mul_nonneg hb.le (sq_nonneg _)
  have hsum : (∑ j ∈ Finset.range (k + 1), (b * ρ ^ 2) ^ j) ≤ (1 - b * ρ ^ 2)⁻¹ := by
    rw [← tsum_geometric_of_lt_one hκ hsmall]
    exact (summable_geometric_of_lt_one hκ hsmall).sum_le_tsum _ (fun j _ => pow_nonneg hκ j)
  have hreflect : (∑ j ∈ Finset.range (k + 1), (b * ρ ^ 2) ^ (k - j)) =
      ∑ j ∈ Finset.range (k + 1), (b * ρ ^ 2) ^ j := by
    simpa only [Nat.add_sub_cancel_right] using
      (Finset.sum_range_reflect (fun j => (b * ρ ^ 2) ^ j) (k + 1))
  calc
    _ = (∑ j ∈ Finset.range (k + 1),
        (ampScale A₀ b k / radScale R ρ k ^ 2) * (b * ρ ^ 2) ^ (k - j)) := by
      apply Finset.sum_congr rfl
      intro j hj
      exact outer_radial_scale_identity hb hR hρ (Nat.le_of_lt_succ (Finset.mem_range.mp hj))
    _ = (ampScale A₀ b k / radScale R ρ k ^ 2) *
        ∑ j ∈ Finset.range (k + 1), (b * ρ ^ 2) ^ j := by rw [← Finset.mul_sum, hreflect]
    _ ≤ (ampScale A₀ b k / radScale R ρ k ^ 2) * (1 - b * ρ ^ 2)⁻¹ :=
      mul_le_mul_of_nonneg_left hsum (by unfold ampScale; positivity)
    _ = _ := by simp only [div_eq_mul_inv]

end Euler2D

end
