module

public import RequestProject.Euler.BanachGeometricTail

/-! The stable part of an actual decaying backward recurrence is
its genuine future convolution. A quadratic forcing gains the full
quadratic decay rate, with a true operator-power estimate. -/

@[expose] public section

set_option maxHeartbeats 1500000

noncomputable section

open Set Filter Topology
open scoped BigOperators

namespace Euler2D

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem backwardRecurrence_finite_formula (A : E →L[ℝ] E) (x y : ℕ → E)
    (hrec : ∀ n, x n = A (x (n + 1)) + y (n + 1)) (n m : ℕ) :
    x n = (A ^ m) (x (n + m)) + ∑ k ∈ Finset.range m, (A ^ k) (y (n + (k + 1))) := by
  induction m with
  | zero => simp only [pow_zero, ContinuousLinearMap.one_apply, add_zero, Finset.range_zero, Finset.sum_empty]
  | succ m ih =>
    rw [Finset.sum_range_succ]
    rw [hrec (n + m), (A ^ m).map_add] at ih
    have hi : n + m + 1 = n + (m + 1) := by omega
    rw [hi] at ih
    rw [pow_succ, ContinuousLinearMap.mul_apply]
    rw [ih]
    abel

theorem tendsto_backwardRecurrence_boundary_zero
    (A : E →L[ℝ] E) {M β C b : ℝ} (hM : 0 ≤ M) (hβ : 0 ≤ β) (hb : 0 ≤ b)
    (hβb : β * b < 1) (hA : ∀ k : ℕ, ‖A ^ k‖ ≤ M * β ^ k)
    (x : ℕ → E) (hx : ∀ n, ‖x n‖ ≤ C * b ^ n) (n : ℕ) :
    Tendsto (fun k : ℕ => (A ^ k) (x (n + k))) atTop (𝓝 (0 : E)) := by
  have hq0 : 0 ≤ β * b := mul_nonneg hβ hb
  have hbound (k : ℕ) : ‖(A ^ k) (x (n + k))‖ ≤ (M * C * b ^ n) * (β * b) ^ k := by
    calc
      _ ≤ ‖A ^ k‖ * ‖x (n + k)‖ := (A ^ k).le_opNorm _
      _ ≤ (M * β ^ k) * (C * b ^ (n + k)) := mul_le_mul (hA k) (hx _)
        (norm_nonneg _) (mul_nonneg hM (pow_nonneg hβ k))
      _ = _ := by rw [pow_add, mul_pow]; ring
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero (g := fun k : ℕ => (M * C * b ^ n) * (β * b) ^ k) (fun _ => norm_nonneg _) hbound
  simpa only [mul_zero] using
    (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hβb).const_mul (M * C * b ^ n)

theorem backwardRecurrence_future_formula
    (A : E →L[ℝ] E) {M β C b D d : ℝ} (hM : 0 ≤ M) (hβ : 0 ≤ β) (hb : 0 ≤ b) (hd : 0 ≤ d)
    (hβb : β * b < 1) (hβd : β * d < 1) (hA : ∀ k : ℕ, ‖A ^ k‖ ≤ M * β ^ k)
    (x y : ℕ → E) (hx : ∀ n, ‖x n‖ ≤ C * b ^ n) (hy : ∀ n, ‖y n‖ ≤ D * d ^ n)
    (hrec : ∀ n, x n = A (x (n + 1)) + y (n + 1)) (n : ℕ) :
    x n = ∑' k : ℕ, (A ^ k) (y (n + (k + 1))) ∧
      ‖x n‖ ≤ (M * D * d ^ (n + 1)) / (1 - β * d) := by
  have hq0 : 0 ≤ β * d := mul_nonneg hβ hd
  have hbound (k : ℕ) : ‖(A ^ k) (y (n + (k + 1)))‖ ≤
      (M * D * d ^ (n + 1)) * (β * d) ^ k := by
    calc
      _ ≤ ‖A ^ k‖ * ‖y (n + (k + 1))‖ := (A ^ k).le_opNorm _
      _ ≤ (M * β ^ k) * (D * d ^ (n + (k + 1))) := mul_le_mul (hA k) (hy _)
        (norm_nonneg _) (mul_nonneg hM (pow_nonneg hβ k))
      _ = _ := by
        rw [show n + (k + 1) = (n + 1) + k by omega, pow_add, mul_pow]
        ring
  have hs := summable_of_norm_le_geometric hq0 hβd hbound
  have hzero := tendsto_backwardRecurrence_boundary_zero A hM hβ hb hβb hA x hx n
  have hlim : Tendsto
      (fun m : ℕ => (A ^ m) (x (n + m)) +
        ∑ k ∈ Finset.range m, (A ^ k) (y (n + (k + 1)))) atTop
      (𝓝 (∑' k : ℕ, (A ^ k) (y (n + (k + 1))))) := by
    simpa only [zero_add] using hzero.add hs.hasSum.tendsto_sum_nat
  have hconst : Tendsto (fun _ : ℕ => x n) atTop
      (𝓝 (∑' k : ℕ, (A ^ k) (y (n + (k + 1))))) :=
    hlim.congr' (Filter.Eventually.of_forall (fun m => (backwardRecurrence_finite_formula A x y hrec n m).symm))
  have he : x n = ∑' k : ℕ, (A ^ k) (y (n + (k + 1))) :=
    tendsto_nhds_unique tendsto_const_nhds hconst
  refine ⟨he, ?_⟩
  rw [he]
  exact norm_tsum_le_geometric hq0 hβd hbound

end Euler2D

end
