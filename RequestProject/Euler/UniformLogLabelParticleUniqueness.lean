module

public import RequestProject.Euler.UniformLabelParticleUniqueness
public import RequestProject.Euler.Osgood

/-! Uniform uniqueness for a family of actual particle trajectories
with an epsilon-affine logarithmic comparison. Factorial integration
avoids differentiating a supremum over the noncompact label space. -/

@[expose] public section

set_option maxHeartbeats 6000000

noncomputable section

open MeasureTheory Set Filter Topology

namespace Euler2D

theorem uniform_label_particle_affine_bound
    {ι E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {T B K H : ℝ} (hB : 0 ≤ B) (hK : 0 ≤ K) (hH : 0 ≤ H)
    (X Y vx vy : ℝ → ι → E)
    (hvc : ∀ a, Continuous (fun t => vx t a)) (hwc : ∀ a, Continuous (fun t => vy t a))
    (hXd : ∀ t ∈ Icc (0 : ℝ) T, ∀ a, HasDerivAt (fun s => X s a) (vx t a) t)
    (hYd : ∀ t ∈ Icc (0 : ℝ) T, ∀ a, HasDerivAt (fun s => Y s a) (vy t a) t)
    (hinit : ∀ a, X 0 a = Y 0 a)
    (hbound : ∀ t ∈ Icc (0 : ℝ) T, ∀ a, ‖X t a - Y t a‖ ≤ B)
    (hcompare : ∀ t ∈ Icc (0 : ℝ) T, ∀ D : ℝ, 0 ≤ D →
      (∀ a, ‖X t a - Y t a‖ ≤ D) → ∀ a, ‖vx t a - vy t a‖ ≤ K * D + H) :
    ∀ t ∈ Icc (0 : ℝ) T, ∀ a, ‖X t a - Y t a‖ ≤ gronwallBound 0 K H t := by
  let g : ℝ → ℝ := gronwallBound 0 K H
  have hgc : Continuous g := continuous_iff_continuousAt.mpr
    (fun s => (hasDerivAt_gronwallBound 0 K H s).continuousAt)
  have hgpos {t : ℝ} (ht : 0 ≤ t) : 0 ≤ g t := by
    have he := gronwallBound_mono (δ := 0) (by norm_num) hH hK ht
    simpa only [gronwallBound_x0] using he
  have hInt (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) (a : ι) :
      X t a - Y t a = ∫ s in (0 : ℝ)..t, vx s a - vy s a := by
    have he := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun s hs => (hXd s (by
        have hs' : s ∈ Icc (0 : ℝ) t := by simpa only [uIcc_of_le ht.1] using hs
        exact ⟨hs'.1, hs'.2.trans ht.2⟩) a).sub (hYd s (by
        have hs' : s ∈ Icc (0 : ℝ) t := by simpa only [uIcc_of_le ht.1] using hs
        exact ⟨hs'.1, hs'.2.trans ht.2⟩) a)) (((hvc a).sub (hwc a)).intervalIntegrable 0 t)
    dsimp only [Pi.sub_apply] at he
    rw [hinit a, sub_self, sub_zero] at he
    exact he.symm
  have hgInt (t : ℝ) : (∫ s in (0 : ℝ)..t, K * g s + H) = g t := by
    have he := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun s _ => hasDerivAt_gronwallBound 0 K H s)
      (((continuous_const.mul hgc).add continuous_const).intervalIntegrable 0 t)
    simpa only [gronwallBound_x0, sub_zero] using he
  have hpower (n : ℕ) : ∀ t ∈ Icc (0 : ℝ) T, ∀ a,
      ‖X t a - Y t a‖ ≤ g t + B * (K * t) ^ n / (n.factorial : ℝ) := by
    induction n with
    | zero =>
      intro t ht a
      simpa only [pow_zero, Nat.factorial_zero, Nat.cast_one, mul_one, div_one] using
        (hbound t ht a).trans (le_add_of_nonneg_left (hgpos ht.1))
    | succ n ih =>
      intro t ht a
      rw [hInt t ht a]
      calc
        _ ≤ ∫ s in (0 : ℝ)..t, K * (g s + B * (K * s) ^ n / (n.factorial : ℝ)) + H := by
          apply intervalIntegral.norm_integral_le_of_norm_le ht.1 (Eventually.of_forall ?_)
            (by apply Continuous.intervalIntegrable; fun_prop)
          intro s hs
          have hsT : s ∈ Icc (0 : ℝ) T := ⟨hs.1.le, hs.2.trans ht.2⟩
          have hs0 : 0 ≤ s := hsT.1
          exact hcompare s hsT _ (add_nonneg (hgpos hs0) (by positivity)) (ih s hsT) a
        _ = g t + B * (K * t) ^ (n + 1) / ((n + 1).factorial : ℝ) := by
          have he : (fun s : ℝ => K * (g s + B * (K * s) ^ n / (n.factorial : ℝ)) + H) =
              (fun s => (K * g s + H) + K * (B * (K * s) ^ n / (n.factorial : ℝ))) := by
            funext s; ring
          have hi1 : IntervalIntegrable (fun s => K * g s + H) volume 0 t :=
            (((continuous_const.mul hgc).add continuous_const).intervalIntegrable 0 t)
          have hi2 : IntervalIntegrable (fun s : ℝ => K * (B * (K * s) ^ n / (n.factorial : ℝ))) volume 0 t := by
            apply Continuous.intervalIntegrable; fun_prop
          rw [he, intervalIntegral.integral_add
            hi1 hi2, hgInt,
            integral_factorial_comparison_step]
  intro t ht a
  have hz : Tendsto (fun n : ℕ => g t + B * (K * t) ^ n / (n.factorial : ℝ)) atTop (𝓝 (g t)) := by
    simpa only [mul_zero, mul_div_assoc, add_zero] using
      ((FloorSemiring.tendsto_pow_div_factorial_atTop (K * t)).const_mul B).const_add (g t)
  exact ge_of_tendsto hz (Eventually.of_forall (fun n => hpower n t ht a))

theorem uniform_log_label_particle_uniqueness_short
    {ι E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {T B C : ℝ} (hB : 0 ≤ B) (hC : 0 ≤ C) (hCT : C * T < 1)
    (X Y vx vy : ℝ → ι → E)
    (hvc : ∀ a, Continuous (fun t => vx t a)) (hwc : ∀ a, Continuous (fun t => vy t a))
    (hXd : ∀ t ∈ Icc (0 : ℝ) T, ∀ a, HasDerivAt (fun s => X s a) (vx t a) t)
    (hYd : ∀ t ∈ Icc (0 : ℝ) T, ∀ a, HasDerivAt (fun s => Y s a) (vy t a) t)
    (hinit : ∀ a, X 0 a = Y 0 a)
    (hbound : ∀ t ∈ Icc (0 : ℝ) T, ∀ a, ‖X t a - Y t a‖ ≤ B)
    (hcompare : ∀ t ∈ Icc (0 : ℝ) T, ∀ D : ℝ, 0 ≤ D →
      (∀ a, ‖X t a - Y t a‖ ≤ D) → ∀ a, ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
        ‖vx t a - vy t a‖ ≤ C * ((1 - Real.log ε) * D + ε)) :
    ∀ t ∈ Icc (0 : ℝ) T, ∀ a, X t a = Y t a := by
  rcases hC.eq_or_lt with hC0 | hCpos
  · apply uniform_label_particle_uniqueness hB (K := 0) le_rfl X Y vx vy hvc hwc hXd hYd hinit hbound
    intro t ht D hD hd a
    simpa only [← hC0, zero_mul] using hcompare t ht D hD hd a 1 (by norm_num) le_rfl
  · intro t ht a
    have hrate : 0 < 1 - C * t := by nlinarith [mul_le_mul_of_nonneg_left ht.2 hC]
    have hboundn (n : ℕ) : ‖X t a - Y t a‖ ≤
        Real.exp (C * t) * Real.exp (-((n : ℝ) * (1 - C * t))) := by
      let ε : ℝ := Real.exp (-(n : ℝ))
      let K : ℝ := C * (1 + (n : ℝ))
      have hε : 0 < ε := Real.exp_pos _
      have hε1 : ε ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr (Nat.cast_nonneg n))
      have hK : 0 < K := by dsimp only [K]; positivity
      have hKn : C ≤ K := by dsimp only [K]; nlinarith [show 0 ≤ (n : ℝ) by positivity]
      have hcmp : ∀ s ∈ Icc (0 : ℝ) T, ∀ D : ℝ, 0 ≤ D →
          (∀ b, ‖X s b - Y s b‖ ≤ D) → ∀ b, ‖vx s b - vy s b‖ ≤ K * D + C * ε := by
        intro s hs D hD hd b
        have he := hcompare s hs D hD hd b ε hε hε1
        dsimp only [ε] at he
        rw [Real.log_exp] at he
        convert he using 1 <;> dsimp only [K, ε] <;> ring
      have hb := uniform_label_particle_affine_bound hB hK.le (mul_nonneg hC hε.le)
        X Y vx vy hvc hwc hXd hYd hinit hbound hcmp t ht a
      rw [gronwallBound_of_K_ne_0 hK.ne'] at hb
      dsimp only at hb
      rw [zero_mul, zero_add] at hb
      have hdiv : C * ε / K ≤ ε := (div_le_iff₀ hK).mpr (by nlinarith)
      have hExp : 0 ≤ Real.exp (K * t) - 1 := sub_nonneg.mpr
        (Real.one_le_exp (mul_nonneg hK.le ht.1))
      refine hb.trans ((mul_le_mul_of_nonneg_right hdiv hExp).trans ?_)
      calc
        ε * (Real.exp (K * t) - 1) ≤ ε * Real.exp (K * t) := by nlinarith
        _ = _ := by
          dsimp only [ε, K]
          rw [← Real.exp_add, ← Real.exp_add]
          congr 1
          ring
    have hlim : Tendsto (fun n : ℕ => Real.exp (C * t) *
        Real.exp (-((n : ℝ) * (1 - C * t)))) atTop (𝓝 (0 : ℝ)) := by
      have hnat : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
      simpa only [Function.comp_apply, mul_zero] using
        (Real.tendsto_exp_neg_atTop_nhds_zero.comp (hnat.atTop_mul_const hrate)).const_mul (Real.exp (C * t))
    exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm
      (ge_of_tendsto hlim (Eventually.of_forall hboundn)) (norm_nonneg _)))

theorem uniform_log_label_particle_uniqueness
    {ι E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {T B C : ℝ} (hB : 0 ≤ B) (hC : 0 ≤ C)
    (X Y vx vy : ℝ → ι → E)
    (hvc : ∀ a, Continuous (fun t => vx t a)) (hwc : ∀ a, Continuous (fun t => vy t a))
    (hXd : ∀ t ∈ Icc (0 : ℝ) T, ∀ a, HasDerivAt (fun s => X s a) (vx t a) t)
    (hYd : ∀ t ∈ Icc (0 : ℝ) T, ∀ a, HasDerivAt (fun s => Y s a) (vy t a) t)
    (hinit : ∀ a, X 0 a = Y 0 a)
    (hbound : ∀ t ∈ Icc (0 : ℝ) T, ∀ a, ‖X t a - Y t a‖ ≤ B)
    (hcompare : ∀ t ∈ Icc (0 : ℝ) T, ∀ D : ℝ, 0 ≤ D →
      (∀ a, ‖X t a - Y t a‖ ≤ D) → ∀ a, ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
        ‖vx t a - vy t a‖ ≤ C * ((1 - Real.log ε) * D + ε)) :
    ∀ t ∈ Icc (0 : ℝ) T, ∀ a, X t a = Y t a := by
  intro t ht a
  obtain ⟨N, hN⟩ := exists_nat_gt (C * t)
  let m : ℕ := N + 1
  have hm0 : (0 : ℝ) < (m : ℝ) := by dsimp only [m]; positivity
  let δ : ℝ := t / (m : ℝ)
  have hδ : 0 ≤ δ := div_nonneg ht.1 hm0.le
  have hmul : (m : ℝ) * δ = t := by dsimp only [δ]; field_simp
  have hCδ : C * δ < 1 := by
    dsimp only [δ]
    rw [← mul_div_assoc, div_lt_iff₀ hm0]
    dsimp only [m]
    push_cast
    linarith
  have hiter : ∀ k : ℕ, k ≤ m → ∀ b, X ((k : ℝ) * δ) b = Y ((k : ℝ) * δ) b := by
    intro k
    induction k with
    | zero => intro _ b; simpa only [Nat.cast_zero, zero_mul] using hinit b
    | succ k ih =>
      intro hk b
      have hkm : k ≤ m := (Nat.le_succ k).trans hk
      have hkc : (k : ℝ) + 1 ≤ (m : ℝ) := by exact_mod_cast hk
      have htimes {s : ℝ} (hs : s ∈ Icc (0 : ℝ) δ) : s + (k : ℝ) * δ ∈ Icc (0 : ℝ) T := by
        have hk0 : 0 ≤ (k : ℝ) := by positivity
        have hs0 : 0 ≤ s := hs.1
        have hprod := mul_le_mul_of_nonneg_right hkc hδ
        constructor
        · positivity
        · nlinarith [hs.2, ht.2]
      have hx (s : ℝ) (hs : s ∈ Icc (0 : ℝ) δ) (c : ι) :
          HasDerivAt (fun u => X (u + (k : ℝ) * δ) c) (vx (s + (k : ℝ) * δ) c) s :=
        (hXd _ (htimes hs) c).comp_add_const s _
      have hy (s : ℝ) (hs : s ∈ Icc (0 : ℝ) δ) (c : ι) :
          HasDerivAt (fun u => Y (u + (k : ℝ) * δ) c) (vy (s + (k : ℝ) * δ) c) s :=
        (hYd _ (htimes hs) c).comp_add_const s _
      have he := uniform_log_label_particle_uniqueness_short hB hC hCδ
        (fun s c => X (s + (k : ℝ) * δ) c) (fun s c => Y (s + (k : ℝ) * δ) c)
        (fun s c => vx (s + (k : ℝ) * δ) c) (fun s c => vy (s + (k : ℝ) * δ) c)
        (fun c => (hvc c).comp (continuous_id.add continuous_const))
        (fun c => (hwc c).comp (continuous_id.add continuous_const)) hx hy
        (fun c => by simpa only [zero_add] using ih hkm c)
        (fun s hs c => hbound _ (htimes hs) c)
        (fun s hs D hD hd c ε hε hε1 => hcompare _ (htimes hs) D hD hd c ε hε hε1)
        δ ⟨hδ, le_rfl⟩ b
      have heq : δ + (k : ℝ) * δ = ((k + 1 : ℕ) : ℝ) * δ := by push_cast; ring
      simpa only [heq] using he
  simpa only [hmul] using hiter m le_rfl a

end Euler2D

end
