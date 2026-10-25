module

public import Mathlib

/-! Actual uniqueness for uniformly bounded families of labelled
particle trajectories. Repeated integration gives the factorial
estimate directly; no supremum over a noncompact label space is assumed. -/

@[expose] public section

set_option maxHeartbeats 2200000

noncomputable section

open MeasureTheory Set Filter Topology

namespace Euler2D

theorem integral_factorial_comparison_step (B K t : ℝ) (n : ℕ) :
    (∫ s in (0 : ℝ)..t, K * (B * (K * s) ^ n / (n.factorial : ℝ))) =
      B * (K * t) ^ (n + 1) / ((n + 1).factorial : ℝ) := by
  have he : (fun s : ℝ => K * (B * (K * s) ^ n / (n.factorial : ℝ))) =
      (fun s => (K * B * K ^ n / (n.factorial : ℝ)) * s ^ n) := by
    funext s
    rw [mul_pow]
    ring
  rw [he, intervalIntegral.integral_const_mul, integral_pow]
  simp only [zero_pow (Nat.succ_ne_zero n), sub_zero, Nat.factorial_succ,
    Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  have hf : (n.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  have hn : (n : ℝ) + 1 ≠ 0 := by positivity
  field_simp [hf, hn]
  simp only [mul_pow, pow_succ]
  <;> ring

theorem uniform_label_particle_uniqueness
    {ι E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {T B K : ℝ} (hB : 0 ≤ B) (hK : 0 ≤ K)
    (X Y vx vy : ℝ → ι → E)
    (hvc : ∀ a, Continuous (fun t => vx t a)) (hwc : ∀ a, Continuous (fun t => vy t a))
    (hXd : ∀ t ∈ Icc (0 : ℝ) T, ∀ a, HasDerivAt (fun s => X s a) (vx t a) t)
    (hYd : ∀ t ∈ Icc (0 : ℝ) T, ∀ a, HasDerivAt (fun s => Y s a) (vy t a) t)
    (hinit : ∀ a, X 0 a = Y 0 a)
    (hbound : ∀ t ∈ Icc (0 : ℝ) T, ∀ a, ‖X t a - Y t a‖ ≤ B)
    (hcompare : ∀ t ∈ Icc (0 : ℝ) T, ∀ D : ℝ, 0 ≤ D →
      (∀ a, ‖X t a - Y t a‖ ≤ D) → ∀ a, ‖vx t a - vy t a‖ ≤ K * D) :
    ∀ t ∈ Icc (0 : ℝ) T, ∀ a, X t a = Y t a := by
  have hInt (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) (a : ι) :
      X t a - Y t a = ∫ s in (0 : ℝ)..t, vx s a - vy s a := by
    have hg : IntervalIntegrable (fun s => vx s a - vy s a) volume 0 t :=
      ((hvc a).sub (hwc a)).intervalIntegrable 0 t
    have he := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun s hs => (hXd s (by
        have hs' : s ∈ Icc (0 : ℝ) t := by simpa only [uIcc_of_le ht.1] using hs
        exact ⟨hs'.1, hs'.2.trans ht.2⟩) a).sub (hYd s (by
        have hs' : s ∈ Icc (0 : ℝ) t := by simpa only [uIcc_of_le ht.1] using hs
        exact ⟨hs'.1, hs'.2.trans ht.2⟩) a)) hg
    dsimp only [Pi.sub_apply] at he
    rw [hinit a, sub_self, sub_zero] at he
    exact he.symm
  have hpower (n : ℕ) : ∀ t ∈ Icc (0 : ℝ) T, ∀ a,
      ‖X t a - Y t a‖ ≤ B * (K * t) ^ n / (n.factorial : ℝ) := by
    induction n with
    | zero => simpa only [pow_zero, Nat.factorial_zero, Nat.cast_one, mul_one, div_one] using hbound
    | succ n ih =>
      intro t ht a
      rw [hInt t ht a]
      calc
        _ ≤ ∫ s in (0 : ℝ)..t, K * (B * (K * s) ^ n / (n.factorial : ℝ)) := by
          apply intervalIntegral.norm_integral_le_of_norm_le ht.1 (Eventually.of_forall ?_)
            (by apply Continuous.intervalIntegrable; fun_prop)
          intro s hs
          have hsT : s ∈ Icc (0 : ℝ) T := ⟨hs.1.le, hs.2.trans ht.2⟩
          have hs0 : 0 ≤ s := hsT.1
          exact hcompare s hsT _ (by positivity) (ih s hsT) a
        _ = _ := integral_factorial_comparison_step B K t n
  intro t ht a
  have hz : Tendsto (fun n : ℕ => B * (K * t) ^ n / (n.factorial : ℝ)) atTop (𝓝 (0 : ℝ)) := by
    simpa only [mul_zero, mul_div_assoc] using
      (FloorSemiring.tendsto_pow_div_factorial_atTop (K * t)).const_mul B
  have hnorm : ‖X t a - Y t a‖ ≤ 0 := ge_of_tendsto hz (Eventually.of_forall (fun n => hpower n t ht a))
  exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm hnorm (norm_nonneg _)))

end Euler2D

end
