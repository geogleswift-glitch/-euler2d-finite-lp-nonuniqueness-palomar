module

public import Mathlib

/-! Finite capture block bounds give a bound at every actual time,
with the original exponent. The discrete source budget supplies each
block source; no continuous envelope is assumed. -/

@[expose] public section

set_option maxHeartbeats 5000000

noncomputable section

open Set
open scoped BigOperators

namespace Euler2D

theorem exists_finite_capture_block_coordinates {T t : ℝ} (hT : 0 < T) {N : ℕ} (hN : 0 < N)
    (ht : t ∈ Icc (0 : ℝ) ((N : ℝ) * T)) :
    ∃ n < N, ∃ u ∈ Icc (0 : ℝ) T, t = (n : ℝ) * T + u := by
  by_cases heq : t = (N : ℝ) * T
  · have hc : ((N - 1 : ℕ) : ℝ) + 1 = (N : ℝ) := by
      exact_mod_cast Nat.sub_add_cancel (show 1 ≤ N by omega)
    refine ⟨N - 1, by omega, T, ⟨hT.le, le_rfl⟩, ?_⟩
    rw [heq, ← hc]
    ring
  have hlt : t < (N : ℝ) * T := lt_of_le_of_ne ht.2 heq
  have hqt : 0 ≤ t / T := div_nonneg ht.1 hT.le
  let n := ⌊t / T⌋₊
  have hn : n < N := (Nat.floor_lt hqt).mpr ((div_lt_iff₀ hT).mpr hlt)
  have hlo : (n : ℝ) * T ≤ t := (le_div_iff₀ hT).mp (Nat.floor_le hqt)
  have hhi : t < ((n : ℝ) + 1) * T := (div_lt_iff₀ hT).mp (Nat.lt_floor_add_one (t / T))
  refine ⟨n, hn, t - (n : ℝ) * T, ⟨by linarith only [hlo], by linarith only [hhi]⟩, ?_⟩
  ring

theorem capture_block_source_le_seed_envelope {lam a Csrc : ℝ}
    (hlam : 0 < lam) (hCsrc : 0 < Csrc) {N : ℕ} (B : ℕ → ℝ)
    (hB : ∀ n < N, 0 ≤ B n)
    (hf : ∀ n ≤ N, ∑ j ∈ Finset.range n, (Csrc * B j) / lam ^ (j + 1) ≤ a / 32)
    {n : ℕ} (hn : n < N) : B n ≤ (lam / (32 * Csrc)) * a * lam ^ n := by
  have hs : (Csrc * B n) / lam ^ (n + 1) ≤
      ∑ j ∈ Finset.range (n + 1), (Csrc * B j) / lam ^ (j + 1) := by
    apply Finset.single_le_sum (f := fun j : ℕ => (Csrc * B j) / lam ^ (j + 1))
      (s := Finset.range (n + 1)) (a := n)
    · intro j hj
      exact div_nonneg (mul_nonneg hCsrc.le
        (hB j ((Finset.mem_range.mp hj).trans_le (Nat.succ_le_of_lt hn))))
        (pow_nonneg hlam.le _)
    · exact Finset.mem_range.mpr (Nat.lt_succ_self n)
  have hh := (div_le_iff₀ (pow_pos hlam (n + 1))).mp
    (hs.trans (hf (n + 1) (Nat.succ_le_of_lt hn)))
  have hbound : B n ≤ ((a / 32) * lam ^ (n + 1)) / Csrc :=
    (le_div_iff₀ hCsrc).mpr (by nlinarith only [hh])
  exact hbound.trans_eq (by rw [pow_succ]; ring)

theorem finite_capture_continuous_exponential_envelope
    {E : Type*} [NormedAddCommGroup E] (z : ℝ → E)
    {σ T lam H a Csrc : ℝ} (hσ : 0 ≤ σ) (hT : 0 < T)
    (hlam : lam = Real.exp (σ * T)) (hH : 0 ≤ H) (ha : 0 ≤ a) (hCsrc : 0 < Csrc)
    {N : ℕ} (hN : 0 < N) (B : ℕ → ℝ) (hB : ∀ n < N, 0 ≤ B n)
    (hf : ∀ n ≤ N, ∑ j ∈ Finset.range n, (Csrc * B j) / lam ^ (j + 1) ≤ a / 32)
    (hblock : ∀ n < N, ∀ u ∈ Icc (0 : ℝ) T,
      ‖z ((n : ℝ) * T + u)‖ ≤ H * ((11 / 8 : ℝ) * a * lam ^ n + B n)) :
    ∀ t ∈ Icc (0 : ℝ) ((N : ℝ) * T),
      ‖z t‖ ≤ (H * (11 / 8 + lam / (32 * Csrc))) * a * Real.exp (σ * t) := by
  have hl0 : 0 < lam := hlam.symm ▸ Real.exp_pos _
  have hcoef : 0 ≤ H * (11 / 8 + lam / (32 * Csrc)) * a := by positivity
  intro t ht
  obtain ⟨n, hn, u, hu, heq⟩ := exists_finite_capture_block_coordinates hT hN ht
  have hsource := capture_block_source_le_seed_envelope hl0 hCsrc B hB hf hn
  have hbound : ‖z t‖ ≤ (H * (11 / 8 + lam / (32 * Csrc))) * a * lam ^ n := by
    rw [heq]
    exact (hblock n hn u hu).trans
      ((mul_le_mul_of_nonneg_left (add_le_add le_rfl hsource) hH).trans_eq (by ring))
  have he : lam ^ n ≤ Real.exp (σ * t) := by
    rw [hlam, ← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    have hnt : (n : ℝ) * T ≤ t := by rw [heq]; linarith only [hu.1]
    have hh := mul_le_mul_of_nonneg_left hnt hσ
    nlinarith only [hh]
  exact hbound.trans (mul_le_mul_of_nonneg_left he hcoef)

theorem finite_capture_stopped_continuous_exponential_envelope
    {E : Type*} [NormedAddCommGroup E] (z : ℝ → E)
    {σ T lam H a Csrc D : ℝ} (hσ : 0 ≤ σ) (hT : 0 < T)
    (hlam : lam = Real.exp (σ * T)) (hH : 0 ≤ H) (ha : 0 ≤ a) (hCsrc : 0 < Csrc)
    {N : ℕ} (hN : 0 < N) (hD : D ≤ (N : ℝ) * T)
    (B : ℕ → ℝ) (hB : ∀ n < N, 0 ≤ B n)
    (hf : ∀ n ≤ N, ∑ j ∈ Finset.range n, (Csrc * B j) / lam ^ (j + 1) ≤ a / 32)
    (hblock : ∀ n < N, ∀ u ∈ Icc (0 : ℝ) T, (n : ℝ) * T + u ≤ D →
      ‖z ((n : ℝ) * T + u)‖ ≤ H * ((11 / 8 : ℝ) * a * lam ^ n + B n)) :
    ∀ t ∈ Icc (0 : ℝ) D,
      ‖z t‖ ≤ (H * (11 / 8 + lam / (32 * Csrc))) * a * Real.exp (σ * t) := by
  have hl0 : 0 < lam := hlam.symm ▸ Real.exp_pos _
  have hcoef : 0 ≤ H * (11 / 8 + lam / (32 * Csrc)) * a := by positivity
  intro t ht
  obtain ⟨n, hn, u, hu, heq⟩ := exists_finite_capture_block_coordinates hT hN ⟨ht.1, ht.2.trans hD⟩
  have hsource := capture_block_source_le_seed_envelope hl0 hCsrc B hB hf hn
  have hbound : ‖z t‖ ≤ (H * (11 / 8 + lam / (32 * Csrc))) * a * lam ^ n := by
    have hvalid : (n : ℝ) * T + u ≤ D := by rw [← heq]; exact ht.2
    rw [heq]
    exact (hblock n hn u hu hvalid).trans
      ((mul_le_mul_of_nonneg_left (add_le_add le_rfl hsource) hH).trans_eq (by ring))
  have he : lam ^ n ≤ Real.exp (σ * t) := by
    rw [hlam, ← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    have hnt : (n : ℝ) * T ≤ t := by rw [heq]; linarith only [hu.1]
    have hh := mul_le_mul_of_nonneg_left hnt hσ
    nlinarith only [hh]
  exact hbound.trans (mul_le_mul_of_nonneg_left he hcoef)

end Euler2D

end
