module

public import Mathlib

/-! Finite, stopped recurrence estimates used by the actual return-map
capture argument. No extension of a recurrence beyond its given interval
is used in these bounds. -/

@[expose] public section

set_option maxHeartbeats 1800000

noncomputable section

open scoped BigOperators

namespace Euler2D

theorem finite_weighted_recurrence_bound {u e : ℕ → ℝ} {a : ℝ} (ha : 0 < a)
    {N : ℕ} (hstep : ∀ n < N, u (n + 1) ≤ a * u n + e n) :
    ∀ n ≤ N, u n ≤ a ^ n * (u 0 + ∑ j ∈ Finset.range n, e j / a ^ (j + 1)) := by
  intro n hn
  induction n with
  | zero => simp
  | succ n ih =>
    have hprev := ih (Nat.le_of_succ_le hn)
    have hrec := hstep n (Nat.lt_of_succ_le hn)
    calc
      u (n + 1) ≤ a * u n + e n := hrec
      _ ≤ a * (a ^ n * (u 0 + ∑ j ∈ Finset.range n, e j / a ^ (j + 1))) + e n :=
        add_le_add (mul_le_mul_of_nonneg_left hprev ha.le) le_rfl
      _ = a ^ (n + 1) * (u 0 + ∑ j ∈ Finset.range (n + 1), e j / a ^ (j + 1)) := by
        rw [Finset.sum_range_succ, pow_succ]
        field_simp
        <;> ring

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem finite_norm_recurrence_bound {w : ℕ → E} {e : ℕ → ℝ} {a : ℝ} (ha : 0 < a)
    {N : ℕ} (hstep : ∀ n < N, ‖w (n + 1)‖ ≤ a * ‖w n‖ + e n) :
    ∀ n ≤ N, ‖w n‖ ≤ a ^ n * (‖w 0‖ + ∑ j ∈ Finset.range n, e j / a ^ (j + 1)) :=
  finite_weighted_recurrence_bound ha hstep

theorem finite_amplitude_defect_bound (v : ℕ → E) {a : ℝ} (ha : 0 < a)
    (N : ℕ) :
    ‖v N - a ^ N • v 0‖ ≤ a ^ N *
      ∑ j ∈ Finset.range N, ‖v (j + 1) - a • v j‖ / a ^ (j + 1) := by
  let d : ℕ → E := fun n => v n - a ^ n • v 0
  have hstep : ∀ n < N, ‖d (n + 1)‖ ≤ a * ‖d n‖ + ‖v (n + 1) - a • v n‖ := by
    intro n _
    have he : d (n + 1) = a • d n + (v (n + 1) - a • v n) := by
      dsimp only [d]
      rw [pow_succ]
      module
    rw [he]
    exact (norm_add_le _ _).trans_eq (by rw [norm_smul, Real.norm_of_nonneg ha.le])
  have hh := finite_norm_recurrence_bound ha hstep N le_rfl
  simpa only [d, pow_zero, one_smul, sub_self, norm_zero, zero_add] using hh

theorem finite_amplitude_envelope_of_weighted_defect (v : ℕ → E) {a θ : ℝ}
    (ha : 0 < a) {N : ℕ}
    (hbudget : ∑ j ∈ Finset.range N, ‖v (j + 1) - a • v j‖ / a ^ (j + 1) ≤
      θ * ‖v 0‖) :
    (1 - θ) * ‖v 0‖ * a ^ N ≤ ‖v N‖ ∧
      ‖v N‖ ≤ (1 + θ) * ‖v 0‖ * a ^ N := by
  have hh := (finite_amplitude_defect_bound v ha N).trans
    (mul_le_mul_of_nonneg_left hbudget (pow_nonneg ha.le N))
  have hs : ‖a ^ N • v 0‖ = a ^ N * ‖v 0‖ := by
    rw [norm_smul, Real.norm_of_nonneg (pow_nonneg ha.le N)]
  have hl := norm_le_norm_sub_add (a ^ N • v 0) (v N)
  have hu := norm_le_norm_sub_add (v N) (a ^ N • v 0)
  rw [hs] at hl hu
  rw [norm_sub_rev] at hl
  constructor <;> nlinarith only [hl, hu, hh]

end Euler2D

end
