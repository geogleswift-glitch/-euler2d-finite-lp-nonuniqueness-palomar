module

public import RequestProject.Euler.UniformLogLabelParticleUniqueness

/-! Uniform stability for singular material comparisons. The small
initial discrepancy and additive velocity error are chosen before
the family of actual trajectories, including noncompact label sets. -/

@[expose] public section

set_option maxHeartbeats 12000000
set_option maxRecDepth 6500

noncomputable section

open MeasureTheory Set Filter Topology

namespace Euler2D

theorem uniform_label_particle_affine_initial_bound
    {ι E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {T B A K H : ℝ} (hB : 0 ≤ B) (hA : 0 ≤ A) (hK : 0 ≤ K) (hH : 0 ≤ H)
    (X Y vx vy : ℝ → ι → E)
    (hvc : ∀ a, Continuous (fun t => vx t a)) (hwc : ∀ a, Continuous (fun t => vy t a))
    (hXd : ∀ t ∈ Icc (0 : ℝ) T, ∀ a, HasDerivAt (fun s => X s a) (vx t a) t)
    (hYd : ∀ t ∈ Icc (0 : ℝ) T, ∀ a, HasDerivAt (fun s => Y s a) (vy t a) t)
    (hinit : ∀ a, ‖X 0 a - Y 0 a‖ ≤ A)
    (hbound : ∀ t ∈ Icc (0 : ℝ) T, ∀ a, ‖X t a - Y t a‖ ≤ B)
    (hcompare : ∀ t ∈ Icc (0 : ℝ) T, ∀ D : ℝ, 0 ≤ D →
      (∀ a, ‖X t a - Y t a‖ ≤ D) → ∀ a, ‖vx t a - vy t a‖ ≤ K * D + H) :
    ∀ t ∈ Icc (0 : ℝ) T, ∀ a, ‖X t a - Y t a‖ ≤ gronwallBound A K H t := by
  let Z : ℝ → ι → E := fun t a => X t a - (X 0 a - Y 0 a)
  have hrestore (t : ℝ) (a : ι) : X t a - Y t a = (Z t a - Y t a) + (X 0 a - Y 0 a) := by
    dsimp only [Z]
    abel
  have hZinit (a : ι) : Z 0 a = Y 0 a := by dsimp only [Z]; abel
  have hZbound (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) (a : ι) : ‖Z t a - Y t a‖ ≤ B + A := by
    have he : Z t a - Y t a = (X t a - Y t a) - (X 0 a - Y 0 a) := by dsimp only [Z]; abel
    rw [he]
    exact (norm_sub_le _ _).trans (add_le_add (hbound t ht a) (hinit a))
  have hb := uniform_label_particle_affine_bound (add_nonneg hB hA) hK
    (add_nonneg (mul_nonneg hK hA) hH) Z Y vx vy hvc hwc
    (fun t ht a => (hXd t ht a).sub_const _) hYd hZinit hZbound
    (by
      intro t ht D hD hd a
      have hreal (a : ι) : ‖X t a - Y t a‖ ≤ D + A := by
        rw [hrestore]
        exact (norm_add_le _ _).trans (add_le_add (hd a) (hinit a))
      have he := hcompare t ht (D + A) (add_nonneg hD hA) hreal a
      convert he using 1 <;> ring)
  intro t ht a
  have he : gronwallBound 0 K (K * A + H) t + A = gronwallBound A K H t := by
    by_cases hK0 : K = 0
    · simp only [hK0, gronwallBound_K0, zero_mul, zero_add]
      ring
    · rw [gronwallBound_of_K_ne_0 hK0, gronwallBound_of_K_ne_0 hK0]
      dsimp only
      field_simp [hK0]
      <;> ring
  rw [hrestore]
  exact (norm_add_le _ _).trans ((add_le_add (hb t ht a) (hinit a)).trans_eq he)

theorem uniform_log_label_particle_stability_short
    {ι E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {T B C ε : ℝ} (hT : 0 ≤ T) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hCT : C * T < 1) (hε : 0 < ε) :
    ∃ δ > 0, ∀ (X Y vx vy : ℝ → ι → E),
    (∀ a, Continuous (fun t => vx t a)) → (∀ a, Continuous (fun t => vy t a)) →
    (∀ t ∈ Icc (0 : ℝ) T, ∀ a, HasDerivAt (fun s => X s a) (vx t a) t) →
    (∀ t ∈ Icc (0 : ℝ) T, ∀ a, HasDerivAt (fun s => Y s a) (vy t a) t) →
    (∀ a, ‖X 0 a - Y 0 a‖ ≤ δ) →
    (∀ t ∈ Icc (0 : ℝ) T, ∀ a, ‖X t a - Y t a‖ ≤ B) →
    (∀ t ∈ Icc (0 : ℝ) T, ∀ D : ℝ, 0 ≤ D →
      (∀ a, ‖X t a - Y t a‖ ≤ D) → ∀ a, ∀ η : ℝ, 0 < η → η ≤ 1 →
        ‖vx t a - vy t a‖ ≤ C * ((1 - Real.log η) * D + η) + δ) →
    ∀ t ∈ Icc (0 : ℝ) T, ∀ a, ‖X t a - Y t a‖ < ε := by
  have hrate : 0 < 1 - C * T := sub_pos.mpr hCT
  have hlim : Tendsto (fun n : ℕ => Real.exp ((C + 1) * T) *
      Real.exp (-((n : ℝ) * (1 - C * T)))) atTop (𝓝 (0 : ℝ)) := by
    have hnat : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
    simpa only [Function.comp_apply, mul_zero] using
      (Real.tendsto_exp_neg_atTop_nhds_zero.comp (hnat.atTop_mul_const hrate)).const_mul _
  obtain ⟨n, hn⟩ := (hlim.eventually (eventually_lt_nhds (half_pos hε))).exists
  let η := Real.exp (-(n : ℝ))
  let K := C * (1 + (n : ℝ)) + 1
  let Eexp := Real.exp (K * T)
  have hη : 0 < η := Real.exp_pos _
  have hη1 : η ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr (Nat.cast_nonneg n))
  have hK : 0 < K := by dsimp only [K]; positivity
  have hCK : C ≤ K := by dsimp only [K]; nlinarith [Nat.cast_nonneg (α := ℝ) n]
  have hExp : 0 < Eexp := Real.exp_pos _
  have hExp1 : 1 ≤ Eexp := Real.one_le_exp (mul_nonneg hK.le hT)
  have htail : η * Eexp < ε / 2 := by
    have he : η * Eexp = Real.exp ((C + 1) * T) * Real.exp (-((n : ℝ) * (1 - C * T))) := by
      dsimp only [η, Eexp, K]
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    exact he ▸ hn
  let δ := min ((ε / 4) / Eexp) (((ε / 4) * K) / Eexp)
  have hδ : 0 < δ := lt_min (div_pos (by positivity) hExp) (div_pos (by positivity) hExp)
  refine ⟨δ, hδ, ?_⟩
  intro X Y vx vy hvc hwc hXd hYd hinit hbound hcompare t ht a
  have hcmp (s : ℝ) (hs : s ∈ Icc (0 : ℝ) T) (D : ℝ) (hD : 0 ≤ D)
      (hd : ∀ b, ‖X s b - Y s b‖ ≤ D) (b : ι) :
      ‖vx s b - vy s b‖ ≤ K * D + (C * η + δ) := by
    have he := hcompare s hs D hD hd b η hη hη1
    have hlog : Real.log η = -(n : ℝ) := Real.log_exp _
    rw [hlog] at he
    dsimp only [K]
    nlinarith only [he, hD]
  have hb := uniform_label_particle_affine_initial_bound hB hδ.le hK.le
    (add_nonneg (mul_nonneg hC hη.le) hδ.le) X Y vx vy hvc hwc hXd hYd hinit hbound hcmp t ht a
  have hmono := gronwallBound_mono hδ.le (add_nonneg (mul_nonneg hC hη.le) hδ.le) hK.le ht.2
  have hδE : δ * Eexp ≤ ε / 4 := (le_div_iff₀ hExp).mp (min_le_left _ _)
  have hδKE : δ * Eexp ≤ ε / 4 * K := (le_div_iff₀ hExp).mp (min_le_right _ _)
  have hδdE : (δ / K) * Eexp ≤ ε / 4 := by
    rw [div_mul_eq_mul_div]
    exact (div_le_iff₀ hK).mpr hδKE
  have hηK : (C * η) / K ≤ η := (div_le_iff₀ hK).mpr (by nlinarith only [hCK, hη.le])
  have hsrc : 0 ≤ (C * η + δ) / K := div_nonneg (by positivity) hK.le
  have hfinal : gronwallBound δ K (C * η + δ) T < ε := by
    rw [gronwallBound_of_K_ne_0 hK.ne']
    change δ * Eexp + (C * η + δ) / K * (Eexp - 1) < ε
    have hrem : (C * η + δ) / K * (Eexp - 1) ≤ (C * η + δ) / K * Eexp :=
      mul_le_mul_of_nonneg_left (by linarith) hsrc
    have hηE := mul_le_mul_of_nonneg_right hηK hExp.le
    calc
      _ ≤ δ * Eexp + (C * η + δ) / K * Eexp := add_le_add le_rfl hrem
      _ = δ * Eexp + ((C * η) / K) * Eexp + (δ / K) * Eexp := by rw [add_div]; ring
      _ ≤ ε / 4 + η * Eexp + ε / 4 := add_le_add (add_le_add hδE hηE) hδdE
      _ < ε := by linarith only [htail]
  exact (hb.trans hmono).trans_lt hfinal

theorem uniform_log_label_particle_stability_steps
    {ι E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {step B C : ℝ} (hstep : 0 ≤ step) (hB : 0 ≤ B) (hC : 0 ≤ C) (hCstep : C * step < 1) :
    ∀ n : ℕ, ∀ ε > 0, ∃ δ > 0, ∀ (X Y vx vy : ℝ → ι → E),
    (∀ a, Continuous (fun t => vx t a)) → (∀ a, Continuous (fun t => vy t a)) →
    (∀ t ∈ Icc (0 : ℝ) ((n : ℝ) * step), ∀ a, HasDerivAt (fun s => X s a) (vx t a) t) →
    (∀ t ∈ Icc (0 : ℝ) ((n : ℝ) * step), ∀ a, HasDerivAt (fun s => Y s a) (vy t a) t) →
    (∀ a, ‖X 0 a - Y 0 a‖ ≤ δ) →
    (∀ t ∈ Icc (0 : ℝ) ((n : ℝ) * step), ∀ a, ‖X t a - Y t a‖ ≤ B) →
    (∀ t ∈ Icc (0 : ℝ) ((n : ℝ) * step), ∀ D : ℝ, 0 ≤ D →
      (∀ a, ‖X t a - Y t a‖ ≤ D) → ∀ a, ∀ η : ℝ, 0 < η → η ≤ 1 →
        ‖vx t a - vy t a‖ ≤ C * ((1 - Real.log η) * D + η) + δ) →
    ∀ t ∈ Icc (0 : ℝ) ((n : ℝ) * step), ∀ a, ‖X t a - Y t a‖ < ε := by
  intro n
  induction n with
  | zero =>
    intro ε hε
    refine ⟨ε / 2, half_pos hε, ?_⟩
    intro X Y vx vy hvc hwc hXd hYd hinit hbound hcompare t ht a
    have ht' : t ∈ Icc (0 : ℝ) 0 := by simpa only [Nat.cast_zero, zero_mul] using ht
    have ht0 : t = 0 := le_antisymm ht'.2 ht'.1
    subst t
    exact (hinit a).trans_lt (half_lt_self hε)
  | succ n ih =>
    intro ε hε
    obtain ⟨δlast, hδlast, hlast⟩ := uniform_log_label_particle_stability_short
      (ι := ι) (E := E) hstep hB hC hCstep hε
    obtain ⟨δfirst, hδfirst, hfirst⟩ := ih (min ε δlast) (lt_min hε hδlast)
    let δ := min δfirst δlast
    refine ⟨δ, lt_min hδfirst hδlast, ?_⟩
    intro X Y vx vy hvc hwc hXd hYd hinit hbound hcompare
    have hlen : (n : ℝ) * step ≤ ((n + 1 : ℕ) : ℝ) * step := by
      push_cast
      nlinarith only [hstep]
    have hinclude {t : ℝ} (ht : t ∈ Icc (0 : ℝ) ((n : ℝ) * step)) :
        t ∈ Icc (0 : ℝ) (((n + 1 : ℕ) : ℝ) * step) := ⟨ht.1, ht.2.trans hlen⟩
    have hfirstBound := hfirst X Y vx vy hvc hwc
      (fun t ht a => hXd t (hinclude ht) a) (fun t ht a => hYd t (hinclude ht) a)
      (fun a => (hinit a).trans (min_le_left _ _))
      (fun t ht a => hbound t (hinclude ht) a)
      (by
        intro t ht D hD hd a η hη hη1
        exact (hcompare t (hinclude ht) D hD hd a η hη hη1).trans
          (add_le_add le_rfl (min_le_left _ _)))
    have hshiftTime {t : ℝ} (ht : t ∈ Icc (0 : ℝ) step) :
        t + (n : ℝ) * step ∈ Icc (0 : ℝ) (((n + 1 : ℕ) : ℝ) * step) := by
      constructor
      · exact add_nonneg ht.1 (mul_nonneg (Nat.cast_nonneg n) hstep)
      · push_cast
        nlinarith only [ht.2]
    have hlastBound := hlast
      (fun t a => X (t + (n : ℝ) * step) a) (fun t a => Y (t + (n : ℝ) * step) a)
      (fun t a => vx (t + (n : ℝ) * step) a) (fun t a => vy (t + (n : ℝ) * step) a)
      (fun a => (hvc a).comp (continuous_id.add continuous_const))
      (fun a => (hwc a).comp (continuous_id.add continuous_const))
      (fun t ht a => (hXd _ (hshiftTime ht) a).comp_add_const t _)
      (fun t ht a => (hYd _ (hshiftTime ht) a).comp_add_const t _)
      (by
        intro a
        simpa only [zero_add] using
          (hfirstBound _ ⟨by positivity, le_rfl⟩ a).le.trans (min_le_right _ _))
      (fun t ht a => hbound _ (hshiftTime ht) a)
      (by
        intro t ht D hD hd a η hη hη1
        exact (hcompare _ (hshiftTime ht) D hD hd a η hη hη1).trans
          (add_le_add le_rfl (min_le_right _ _)))
    intro t ht a
    by_cases htfirst : t ≤ (n : ℝ) * step
    · exact (hfirstBound t ⟨ht.1, htfirst⟩ a).trans_le (min_le_left _ _)
    · have htlast : t - (n : ℝ) * step ∈ Icc (0 : ℝ) step := by
        constructor
        · linarith only [htfirst]
        · have he := ht.2
          push_cast at he
          nlinarith only [he]
      simpa only [sub_add_cancel] using hlastBound _ htlast a

theorem uniform_log_label_particle_stability
    {ι E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {T B C ε : ℝ} (hT : 0 ≤ T) (hB : 0 ≤ B) (hC : 0 ≤ C) (hε : 0 < ε) :
    ∃ δ > 0, ∀ (X Y vx vy : ℝ → ι → E),
    (∀ a, Continuous (fun t => vx t a)) → (∀ a, Continuous (fun t => vy t a)) →
    (∀ t ∈ Icc (0 : ℝ) T, ∀ a, HasDerivAt (fun s => X s a) (vx t a) t) →
    (∀ t ∈ Icc (0 : ℝ) T, ∀ a, HasDerivAt (fun s => Y s a) (vy t a) t) →
    (∀ a, ‖X 0 a - Y 0 a‖ ≤ δ) →
    (∀ t ∈ Icc (0 : ℝ) T, ∀ a, ‖X t a - Y t a‖ ≤ B) →
    (∀ t ∈ Icc (0 : ℝ) T, ∀ D : ℝ, 0 ≤ D →
      (∀ a, ‖X t a - Y t a‖ ≤ D) → ∀ a, ∀ η : ℝ, 0 < η → η ≤ 1 →
        ‖vx t a - vy t a‖ ≤ C * ((1 - Real.log η) * D + η) + δ) →
    ∀ t ∈ Icc (0 : ℝ) T, ∀ a, ‖X t a - Y t a‖ < ε := by
  obtain ⟨N, hN⟩ := exists_nat_gt (C * T)
  let m : ℕ := N + 1
  have hm : (0 : ℝ) < (m : ℝ) := by dsimp only [m]; positivity
  let step := T / (m : ℝ)
  have hstep : 0 ≤ step := div_nonneg hT hm.le
  have hmul : (m : ℝ) * step = T := by dsimp only [step]; field_simp
  have hCstep : C * step < 1 := by
    dsimp only [step]
    rw [← mul_div_assoc, div_lt_iff₀ hm]
    dsimp only [m]
    push_cast
    linarith
  simpa only [hmul] using
    uniform_log_label_particle_stability_steps (ι := ι) (E := E) hstep hB hC hCstep m ε hε

end Euler2D

end
