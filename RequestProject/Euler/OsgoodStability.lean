module

public import RequestProject.Euler.Osgood

/-! Quantitative logarithmic comparison for nonzero initial distances. -/

@[expose] public section

noncomputable section

open Set Filter Topology Real

namespace Euler2D

theorem logFlow_stability_epsilon_bound {T C ε : ℝ} {f f' : ℝ → ℝ}
    (hT : 0 ≤ T) (hC : 0 ≤ C) (hε : 0 < ε) (hεhalf : ε ≤ 1 / 2)
    (hf : ∀ t ∈ Icc 0 T, HasDerivAt f (f' t) t)
    (hsmall : ∀ t ∈ Icc 0 T, f t ∈ Icc 0 (1 / 2))
    (hbound : ∀ t ∈ Ioo 0 T, f' t ≤ C * logFlowModulus (f t)) :
    ∀ t ∈ Icc 0 T, f t ≤ Real.exp 1 * (f 0 + ε) ^ Real.exp (-(C * t)) := by
  let B := fun t => (1 - Real.log (f t + ε)) * Real.exp (C * t)
  have hpos (t : ℝ) (ht : t ∈ Icc 0 T) : 0 < f t + ε := by
    linarith [(hsmall t ht).1]
  have hB (t : ℝ) (ht : t ∈ Icc 0 T) : HasDerivAt B
      (Real.exp (C * t) * (C * (1 - Real.log (f t + ε)) - f' t / (f t + ε))) t := by
    have he := ((hasDerivAt_id t).const_mul C).exp
    have hl := ((hf t ht).add_const ε).log (hpos t ht).ne'
    convert ((hasDerivAt_const t (1 : ℝ)).sub hl).mul he using 1 <;>
      (try funext s) <;>
      (try dsimp only [B, Pi.sub_def, Pi.mul_def, id_eq]) <;> ring
  have hmono : MonotoneOn B (Icc 0 T) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 T)
      (fun t ht => (hB t ht).continuousAt.continuousWithinAt)
    · intro t ht
      exact (hB t (interior_subset ht)).hasDerivWithinAt
    · intro t ht
      have hti : t ∈ Ioo 0 T := by simpa only [interior_Icc] using ht
      have htc : t ∈ Icc 0 T := ⟨hti.1.le, hti.2.le⟩
      have hmod : logFlowModulus (f t) ≤ logFlowModulus (f t + ε) :=
        monotoneOn_logFlowModulus ⟨(hsmall t htc).1, by linarith [(hsmall t htc).2]⟩
          ⟨(hpos t htc).le, by linarith [(hsmall t htc).2]⟩ (by linarith)
      have hd : f' t ≤ C * ((f t + ε) * (1 - Real.log (f t + ε))) := by
        have hb := (hbound t hti).trans (mul_le_mul_of_nonneg_left hmod hC)
        convert hb using 1
        simp only [logFlowModulus]
        ring
      have hdiv : f' t / (f t + ε) ≤ C * (1 - Real.log (f t + ε)) := by
        apply (div_le_iff₀ (hpos t htc)).mpr
        nlinarith [hd]
      exact mul_nonneg (Real.exp_pos _).le (sub_nonneg.mpr hdiv)
  intro t ht
  have hb := hmono ⟨le_rfl, hT⟩ ht ht.1
  change (1 - Real.log (f 0 + ε)) * Real.exp (C * 0) ≤
    (1 - Real.log (f t + ε)) * Real.exp (C * t) at hb
  simp only [mul_zero, Real.exp_zero, mul_one] at hb
  have hb' := mul_le_mul_of_nonneg_right hb (Real.exp_pos (-(C * t))).le
  rw [mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one] at hb'
  have hl : Real.log (f t + ε) ≤ 1 + Real.log (f 0 + ε) * Real.exp (-(C * t)) := by
    nlinarith [Real.exp_pos (-(C * t))]
  have he := Real.exp_le_exp.mpr hl
  rw [Real.exp_log (hpos t ht), Real.exp_add,
    ← Real.rpow_def_of_pos (hpos 0 ⟨le_rfl, hT⟩)] at he
  exact (le_add_of_nonneg_right hε.le).trans he

theorem logFlow_stability_bound {T C : ℝ} {f f' : ℝ → ℝ}
    (hT : 0 ≤ T) (hC : 0 ≤ C)
    (hf : ∀ t ∈ Icc 0 T, HasDerivAt f (f' t) t)
    (hsmall : ∀ t ∈ Icc 0 T, f t ∈ Icc 0 (1 / 2))
    (hbound : ∀ t ∈ Ioo 0 T, f' t ≤ C * logFlowModulus (f t)) :
    ∀ t ∈ Icc 0 T, f t ≤ Real.exp 1 * (f 0) ^ Real.exp (-(C * t)) := by
  intro t ht
  have hα : 0 < Real.exp (-(C * t)) := Real.exp_pos _
  have hlim : Tendsto (fun ε : ℝ => Real.exp 1 * (f 0 + ε) ^ Real.exp (-(C * t)))
      (𝓝[>] (0 : ℝ)) (𝓝 (Real.exp 1 * (f 0) ^ Real.exp (-(C * t)))) := by
    have hc : ContinuousAt (fun ε : ℝ => Real.exp 1 * (f 0 + ε) ^ Real.exp (-(C * t))) 0 :=
      continuousAt_const.mul ((continuousAt_const.add continuousAt_id).rpow_const
        (Or.inr hα.le))
    simpa only [add_zero] using hc.tendsto.mono_left nhdsWithin_le_nhds
  have hs : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ), ε < 1 / 2 :=
    (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 2)).filter_mono nhdsWithin_le_nhds
  apply ge_of_tendsto hlim
  filter_upwards [self_mem_nhdsWithin, hs] with ε hε he
  exact logFlow_stability_epsilon_bound hT hC hε he.le hf hsmall hbound t ht

/-- Uniform smallness from a small initial value. The differential bound
is required only while the distance is below one half; a genuine first
hitting time removes any prior closeness assumption. -/
theorem logFlow_small_initial {T C η : ℝ} (hT : 0 ≤ T) (hC : 0 ≤ C)
    (hη : 0 < η) (hηhalf : η ≤ 1 / 2) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ f f' : ℝ → ℝ, Continuous f →
      (∀ t ∈ Icc 0 T, HasDerivAt f (f' t) t) →
      (∀ t ∈ Icc 0 T, 0 ≤ f t) → f 0 ≤ δ →
      (∀ t ∈ Ioo 0 T, f t ≤ η → f' t ≤ C * logFlowModulus (f t)) →
      ∀ t ∈ Icc 0 T, f t < η := by
  let α := Real.exp (-(C * T))
  have hα : 0 < α := Real.exp_pos _
  have hlim : Tendsto (fun r : ℝ => Real.exp 1 * r ^ α) (𝓝 0) (𝓝 0) := by
    have hc : ContinuousAt (fun r : ℝ => Real.exp 1 * r ^ α) 0 :=
      continuousAt_const.mul (Real.continuousAt_rpow_const (0 : ℝ) α (Or.inr hα.le))
    simpa only [Real.zero_rpow hα.ne', mul_zero] using hc.tendsto
  have hevt : ∀ᶠ r : ℝ in 𝓝 0, Real.exp 1 * r ^ α < η :=
    hlim.eventually (eventually_lt_nhds hη)
  obtain ⟨r, hr, hrbound⟩ := Metric.eventually_nhds_iff.mp hevt
  let δ := min (1 / 2 : ℝ) (r / 2)
  have hδ : 0 < δ := lt_min (by norm_num) (by positivity)
  have hδ1 : δ ≤ 1 := (min_le_left _ _).trans (by norm_num)
  have hδr : δ < r := (min_le_right _ _).trans_lt (by linarith)
  have hδbound : Real.exp 1 * δ ^ α < η := hrbound (y := δ) (by
    simpa only [dist_zero_right, Real.norm_eq_abs, abs_of_pos hδ] using hδr)
  have hδinit : δ < η := by
    have hα1 : α ≤ 1 := by
      dsimp only [α]
      rw [Real.exp_le_one_iff]
      exact neg_nonpos.mpr (mul_nonneg hC hT)
    have hpow : δ ≤ δ ^ α := by
      simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_ge hδ hδ1 hα1
    have he1 : (1 : ℝ) ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
    exact (hpow.trans (le_mul_of_one_le_left (Real.rpow_nonneg hδ.le α) he1)).trans_lt hδbound
  refine ⟨δ, hδ, fun f f' hfc hf hnonneg hinit hbound t ht => ?_⟩
  by_contra hbad
  let A := Icc (0 : ℝ) t ∩ f ⁻¹' Ici η
  have hAc : IsCompact A := isCompact_Icc.inter_right (isClosed_Ici.preimage hfc)
  have hAne : A.Nonempty := ⟨t, ⟨⟨ht.1, le_rfl⟩, le_of_not_gt hbad⟩⟩
  obtain ⟨τ, hτ⟩ := hAc.exists_isLeast hAne
  have hτ0 : 0 ≤ τ := hτ.1.1.1
  have hτt : τ ≤ t := hτ.1.1.2
  have hτT : τ ≤ T := hτt.trans ht.2
  have hτlower : η ≤ f τ := hτ.1.2
  obtain ⟨a, ha, hfa⟩ := intermediate_value_Icc hτ0 hfc.continuousOn
    ⟨(hinit.trans_lt hδinit).le, hτlower⟩
  have haA : a ∈ A := by
    refine ⟨⟨ha.1, ha.2.trans hτt⟩, ?_⟩
    change η ≤ f a
    exact hfa.ge
  have hat : a = τ := le_antisymm ha.2 (hτ.2 haA)
  have hτeq : f τ = η := by simpa only [hat] using hfa
  have hbelow (s : ℝ) (hs : s ∈ Icc 0 τ) : f s ≤ η := by
    by_contra hn
    have hsA : s ∈ A := ⟨⟨hs.1, hs.2.trans hτt⟩, (lt_of_not_ge hn).le⟩
    have hse : s = τ := le_antisymm hs.2 (hτ.2 hsA)
    exact hn (hse ▸ hτeq.le)
  have hsmall (s : ℝ) (hs : s ∈ Icc 0 τ) : f s ∈ Icc 0 (1 / 2) :=
    ⟨hnonneg s ⟨hs.1, hs.2.trans hτT⟩, (hbelow s hs).trans hηhalf⟩
  have hest := logFlow_stability_bound hτ0 hC
    (fun s hs => hf s ⟨hs.1, hs.2.trans hτT⟩) hsmall
    (fun s hs => hbound s ⟨hs.1, hs.2.trans_le hτT⟩
      (hbelow s ⟨hs.1.le, hs.2.le⟩)) τ ⟨hτ0, le_rfl⟩
  have hexp : α ≤ Real.exp (-(C * τ)) := by
    apply Real.exp_le_exp.mpr
    exact neg_le_neg (mul_le_mul_of_nonneg_left hτT hC)
  have hpow1 : (f 0) ^ Real.exp (-(C * τ)) ≤ δ ^ Real.exp (-(C * τ)) :=
    Real.rpow_le_rpow (hnonneg 0 ⟨le_rfl, hT⟩) hinit (Real.exp_pos _).le
  have hpow2 : δ ^ Real.exp (-(C * τ)) ≤ δ ^ α :=
    Real.rpow_le_rpow_of_exponent_ge hδ hδ1 hexp
  have hlast := hest.trans (mul_le_mul_of_nonneg_left (hpow1.trans hpow2) (Real.exp_pos 1).le)
  exact (not_lt_of_ge (hτeq ▸ hlast)) hδbound

end Euler2D

end
