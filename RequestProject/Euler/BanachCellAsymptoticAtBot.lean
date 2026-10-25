module

public import Mathlib

/-! Uniform geometric error bounds on actual time cells imply
the required exponential asymptotic at negative infinity. -/

@[expose] public section

noncomputable section

open Set Filter Topology Asymptotics

namespace Euler2D

theorem exists_negative_time_cell {T : ℝ} (hT : 0 < T) {t : ℝ} (ht : t ≤ 0) (N : ℕ)
    (hNt : t ≤ -(N : ℝ) * T) :
    ∃ n : ℕ, N ≤ n ∧ ∃ s ∈ Icc (0 : ℝ) T, t = -((n + 1 : ℕ) : ℝ) * T + s := by
  let n := Nat.floor (-t / T)
  have hn0 : (n : ℝ) ≤ -t / T := Nat.floor_le (div_nonneg (neg_nonneg.mpr ht) hT.le)
  have hn1 : -t / T < (n : ℝ) + 1 := Nat.lt_floor_add_one (-t / T)
  have hN : N ≤ n := Nat.le_floor ((le_div_iff₀ hT).mpr (by linarith))
  have he0 := (le_div_iff₀ hT).mp hn0
  have he1 := (div_lt_iff₀ hT).mp hn1
  refine ⟨n, hN, t + ((n + 1 : ℕ) : ℝ) * T, ?_, ?_⟩
  · push_cast
    constructor <;> nlinarith
  · ring

theorem isBigO_atBot_of_uniform_time_cells
    {f : ℝ → ℂ} {T α q C : ℝ} (hT : 0 < T) (hα : 0 ≤ α) (hC : 0 ≤ C)
    (hq : q = Real.exp (-α * T)) (N : ℕ)
    (hcell : ∀ n ≥ N, ∀ s ∈ Icc (0 : ℝ) T,
      ‖f (-((n + 1 : ℕ) : ℝ) * T + s)‖ ≤ C * q ^ n) :
    f =O[atBot] (fun t : ℝ => Real.exp (α * t)) := by
  apply IsBigO.of_bound (C * Real.exp (α * T))
  filter_upwards [eventually_le_atBot (-(N : ℝ) * T)] with t ht
  have ht0 : t ≤ 0 := ht.trans (by have hn : (0 : ℝ) ≤ N := Nat.cast_nonneg N; nlinarith)
  obtain ⟨n, hn, s, hs, he⟩ := exists_negative_time_cell hT ht0 N ht
  have herror := hcell n hn s hs
  rw [← he] at herror
  have hpow : q ^ n = Real.exp (-α * T * (n : ℝ)) := by
    rw [hq, ← Real.exp_nat_mul]
    congr 1
    ring
  have htime : -α * T * (n : ℝ) ≤ α * T + α * t := by
    rw [he]
    push_cast
    nlinarith [mul_nonneg hα hs.1]
  simp only [Real.norm_eq_abs, Real.abs_exp]
  calc
    _ ≤ C * q ^ n := herror
    _ ≤ C * Real.exp (α * T + α * t) :=
      mul_le_mul_of_nonneg_left (by rw [hpow]; exact Real.exp_le_exp.mpr htime) hC
    _ = _ := by rw [Real.exp_add]; ring

end Euler2D

end
