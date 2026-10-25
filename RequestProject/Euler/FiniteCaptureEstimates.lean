module

public import RequestProject.Euler.FiniteCaptureBootstrap

/-! Polynomial forcing and the sharper complementary estimate at any
already existing finite capture endpoint. Constants precede the endpoint
and forcing parameters. -/

@[expose] public section

set_option maxHeartbeats 2000000

noncomputable section

open scoped BigOperators

namespace Euler2D

theorem capture_polynomial_weight_summable {q : ℝ} (hq : 1 < q) (M : ℕ) :
    Summable (fun n : ℕ => (1 + (n : ℝ)) ^ M / q ^ (n + 1)) := by
  have hq0 : 0 < q := zero_lt_one.trans hq
  have hi : ‖q⁻¹‖ < 1 := by
    rw [Real.norm_of_nonneg (inv_nonneg.mpr hq0.le)]
    exact inv_lt_one_of_one_lt₀ hq
  have hs := summable_pow_mul_geometric_of_norm_lt_one M hi
  have hh := (summable_nat_add_iff 1).mpr hs
  convert hh using 1
  funext n
  simp only [Nat.cast_add, Nat.cast_one, inv_pow, div_eq_mul_inv, add_comm]

theorem exists_capture_polynomial_weight_budget {q : ℝ} (hq : 1 < q) (M : ℕ) :
    ∃ B > 0, ∀ n : ℕ,
      ∑ j ∈ Finset.range n, (1 + (j : ℝ)) ^ M / q ^ (j + 1) ≤ B := by
  let f : ℕ → ℝ := fun j => (1 + (j : ℝ)) ^ M / q ^ (j + 1)
  have hs : Summable f := capture_polynomial_weight_summable hq M
  have hf (j : ℕ) : 0 ≤ f j := by dsimp only [f]; positivity
  refine ⟨(∑' j, f j) + 1, by have hh : 0 ≤ ∑' j, f j := tsum_nonneg hf; positivity, ?_⟩
  intro n
  exact (hs.sum_le_tsum (Finset.range n) (fun j _ => hf j)).trans (by linarith)

theorem finite_geometric_source_convolution {q lam : ℝ} (hq : 0 < q) (hql : q < lam)
    (N : ℕ) :
    q ^ N * (∑ j ∈ Finset.range N, lam ^ j / q ^ (j + 1)) ≤ lam ^ N / (lam - q) := by
  have hd : 0 < lam - q := sub_pos.mpr hql
  induction N with
  | zero => simpa only [pow_zero, Finset.sum_range_zero, mul_zero] using
      (div_nonneg (by norm_num : (0 : ℝ) ≤ 1) hd.le)
  | succ n ih =>
    rw [Finset.sum_range_succ]
    calc
      _ = q * (q ^ n * (∑ j ∈ Finset.range n, lam ^ j / q ^ (j + 1))) + lam ^ n := by
        rw [pow_succ]
        field_simp
        <;> ring
      _ ≤ q * (lam ^ n / (lam - q)) + lam ^ n :=
        add_le_add (mul_le_mul_of_nonneg_left ih hq.le) le_rfl
      _ = lam ^ (n + 1) / (lam - q) := by
        rw [pow_succ]
        field_simp
        <;> ring

theorem exists_finite_complement_capture_budget {q lam : ℝ}
    (hq : 1 < q) (hql : q < lam) (M : ℕ) :
    ∃ B > 0, ∀ (N : ℕ) (u : ℕ → ℝ) (ε K κ a : ℝ),
      0 ≤ ε → 0 ≤ K → 0 ≤ κ → 0 ≤ a →
      (∀ n < N, u (n + 1) ≤ q * u n + ε * K * (1 + (n : ℝ)) ^ M + κ * a * lam ^ n) →
      u N ≤ q ^ N * (u 0 + ε * K * B) + κ * a * lam ^ N / (lam - q) := by
  obtain ⟨B, hB, hpoly⟩ := exists_capture_polynomial_weight_budget hq M
  refine ⟨B, hB, ?_⟩
  intro N u ε K κ a hε hK hκ ha hstep
  have hq0 : 0 < q := zero_lt_one.trans hq
  have hstep' : ∀ n < N, u (n + 1) ≤ q * u n +
      (ε * K * (1 + (n : ℝ)) ^ M + κ * a * lam ^ n) := by
    intro n hn
    simpa only [add_assoc] using hstep n hn
  have hh := finite_weighted_recurrence_bound (u := u)
    (e := fun j => ε * K * (1 + (j : ℝ)) ^ M + κ * a * lam ^ j) hq0 hstep' N le_rfl
  have hsplit : (∑ j ∈ Finset.range N,
      (ε * K * (1 + (j : ℝ)) ^ M + κ * a * lam ^ j) / q ^ (j + 1)) =
      ε * K * (∑ j ∈ Finset.range N, (1 + (j : ℝ)) ^ M / q ^ (j + 1)) +
      κ * a * (∑ j ∈ Finset.range N, lam ^ j / q ^ (j + 1)) := by
    simp only [add_div, mul_div_assoc, Finset.sum_add_distrib, Finset.mul_sum]
  rw [hsplit] at hh
  calc
    _ ≤ q ^ N * (u 0 + ε * K * (∑ j ∈ Finset.range N, (1 + (j : ℝ)) ^ M / q ^ (j + 1)) +
      κ * a * (∑ j ∈ Finset.range N, lam ^ j / q ^ (j + 1))) := by
        simpa only [add_assoc] using hh
    _ = q ^ N * (u 0 + ε * K * (∑ j ∈ Finset.range N, (1 + (j : ℝ)) ^ M / q ^ (j + 1))) +
        κ * a * (q ^ N * ∑ j ∈ Finset.range N, lam ^ j / q ^ (j + 1)) := by ring
    _ ≤ q ^ N * (u 0 + ε * K * B) + κ * a * (lam ^ N / (lam - q)) := by
      apply add_le_add
      · exact mul_le_mul_of_nonneg_left
          (add_le_add le_rfl (mul_le_mul_of_nonneg_left (hpoly N) (mul_nonneg hε hK)))
          (pow_nonneg hq0.le N)
      · exact mul_le_mul_of_nonneg_left (finite_geometric_source_convolution hq0 hql N)
          (mul_nonneg hκ ha)
    _ = _ := by ring

theorem exists_first_amplitude_section {E : Type*} [NormedAddCommGroup E]
    (v : ℕ → E) {δ : ℝ} {N : ℕ} (hN : δ ≤ ‖v N‖) :
    ∃ n ≤ N, δ ≤ ‖v n‖ ∧ ∀ j < n, ‖v j‖ < δ := by
  have hex : ∃ n : ℕ, δ ≤ ‖v n‖ := ⟨N, hN⟩
  refine ⟨Nat.find hex, Nat.find_min' hex hN, Nat.find_spec hex, ?_⟩
  intro j hj
  exact lt_of_not_ge (Nat.find_min hex hj)

end Euler2D

end
