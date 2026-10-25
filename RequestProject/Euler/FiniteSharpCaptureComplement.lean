module

public import RequestProject.Euler.FiniteCaptureEstimates

/-! The complementary error uses its own strictly slower growth rate,
instead of replacing that rate by the growing multiplier. All bounds
are on the given finite recurrence and retain the original seed. -/

@[expose] public section

set_option maxHeartbeats 2400000

noncomputable section

open scoped BigOperators

namespace Euler2D

theorem finite_complement_recurrence_sharp_bound
    {F : Type*} [NormedAddCommGroup F] (w : ℕ → F) (f : ℕ → ℝ)
    {qbar lam κ a : ℝ} (hqbar : 0 < qbar) (hgap : qbar < lam)
    (hκ : 0 ≤ κ) (ha : 0 ≤ a) {N : ℕ}
    (hstep : ∀ j < N, ‖w (j + 1)‖ ≤ qbar * ‖w j‖ + f j + κ * a * lam ^ j) :
    ‖w N‖ ≤ qbar ^ N * (‖w 0‖ + ∑ j ∈ Finset.range N, f j / qbar ^ (j + 1)) +
      κ * a * lam ^ N / (lam - qbar) := by
  have hh := finite_weighted_recurrence_bound (u := fun j => ‖w j‖)
    (e := fun j => f j + κ * a * lam ^ j) hqbar
    (fun j hj => by simpa only [add_assoc] using hstep j hj) N le_rfl
  have hsplit : (∑ j ∈ Finset.range N, (f j + κ * a * lam ^ j) / qbar ^ (j + 1)) =
      (∑ j ∈ Finset.range N, f j / qbar ^ (j + 1)) +
        κ * a * (∑ j ∈ Finset.range N, lam ^ j / qbar ^ (j + 1)) := by
    simp only [add_div, mul_div_assoc, Finset.sum_add_distrib, Finset.mul_sum]
  rw [hsplit] at hh
  calc
    ‖w N‖ ≤ qbar ^ N * (‖w 0‖ + ∑ j ∈ Finset.range N, f j / qbar ^ (j + 1)) +
        κ * a * (qbar ^ N * ∑ j ∈ Finset.range N, lam ^ j / qbar ^ (j + 1)) := by
      exact hh.trans_eq (by ring)
    _ ≤ qbar ^ N * (‖w 0‖ + ∑ j ∈ Finset.range N, f j / qbar ^ (j + 1)) +
        κ * a * (lam ^ N / (lam - qbar)) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left (finite_geometric_source_convolution hqbar hgap N)
        (mul_nonneg hκ ha))
    _ = _ := by ring

theorem finite_capture_sharp_complement_of_envelope
    {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
    (v : ℕ → E) (w : ℕ → F) (f : ℕ → ℝ)
    {lam q qbar C κ D : ℝ} (hlam : 1 < lam) (hqbar : 0 < qbar) (hgap : qbar < lam)
    (hC : 0 ≤ C) (hκ : 0 ≤ κ) {N : ℕ}
    (hterminal : ‖v 0‖ * lam ^ N ≤ D) (hcomp : q + 3 * C * D ≤ qbar)
    (henv : ∀ n ≤ N, ‖v n‖ ≤ (5 / 4 : ℝ) * ‖v 0‖ * lam ^ n ∧
      ‖w n‖ ≤ (1 / 8 : ℝ) * ‖v 0‖ * lam ^ n)
    (hstep : ∀ n < N, ‖v n‖ + ‖w n‖ ≤ 3 * D →
      ‖w (n + 1)‖ ≤ q * ‖w n‖ + C * (‖v n‖ + ‖w n‖) * ‖w n‖ +
        f n + κ * (‖v n‖ + ‖w n‖)) :
    ∀ n ≤ N,
      ‖w n‖ ≤ qbar ^ n * (‖w 0‖ + ∑ j ∈ Finset.range n, f j / qbar ^ (j + 1)) +
        κ * (3 * ‖v 0‖) * lam ^ n / (lam - qbar) := by
  have hl0 : 0 < lam := zero_lt_one.trans hlam
  have hrec (j : ℕ) (hj : j < N) :
      ‖w (j + 1)‖ ≤ qbar * ‖w j‖ + f j + κ * (3 * ‖v 0‖) * lam ^ j := by
    have hscale : 0 ≤ ‖v 0‖ * lam ^ j := mul_nonneg (norm_nonneg _) (pow_nonneg hl0.le j)
    have hs : ‖v j‖ + ‖w j‖ ≤ 3 * (‖v 0‖ * lam ^ j) := by
      obtain ⟨hv, hw⟩ := henv j hj.le
      nlinarith only [hv, hw, hscale]
    have hterm : ‖v 0‖ * lam ^ j ≤ D :=
      (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hlam.le hj.le) (norm_nonneg _)).trans hterminal
    have hsD : ‖v j‖ + ‖w j‖ ≤ 3 * D := hs.trans (by linarith only [hterm])
    have hc : q + C * (‖v j‖ + ‖w j‖) ≤ qbar := by
      have hh := mul_le_mul_of_nonneg_left hsD hC
      nlinarith only [hh, hcomp]
    have hh := hstep j hj hsD
    have hcw := mul_le_mul_of_nonneg_right hc (norm_nonneg (w j))
    have hκs := mul_le_mul_of_nonneg_left hs hκ
    nlinarith only [hh, hcw, hκs]
  intro n hn
  exact finite_complement_recurrence_sharp_bound w f hqbar hgap hκ (by positivity)
    (fun j hj => hrec j (hj.trans_le hn))

end Euler2D

end
