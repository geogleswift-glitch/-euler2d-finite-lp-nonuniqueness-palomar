module

public import RequestProject.Euler.BanachCompactLocalFlow
public import RequestProject.Euler.BanachFlowConcatenation

/-! Genuine finite-time smooth continuation near a known reference
orbit. A finite cover provides a uniform step, and actual flows are
concatenated while the initial neighborhood is reduced finitely often. -/

@[expose] public section

noncomputable section

open Set Filter Topology Metric
open scoped NNReal ContDiff

namespace Euler2D

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem exists_smooth_banachFlow_along_reference (n : ℕ)
    {f : E → E} {U : Set E} (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U)
    {c : ℝ → E} (hc : Continuous c) (hcU : ∀ t, c t ∈ U)
    (hcd : ∀ t, HasDerivAt c (f (c t)) t) {T : ℝ} (hT : 0 < T) :
    ∃ ρ > 0, ∃ X : E → ℝ → E,
      IsBanachFlowOn f U (ball (c 0) ρ) T X ∧
      (∀ t ∈ Icc (0 : ℝ) T, ContDiffOn ℝ n (fun b => X b t) (ball (c 0) ρ)) ∧
      EqOn (X (c 0)) c (Icc (0 : ℝ) T) := by
  classical
  obtain ⟨δ, hδ, hlocal⟩ :=
    exists_uniform_local_banachFlow_along_reference n hU hf hc hcU hcd hT.le
  obtain ⟨N, hN⟩ := exists_nat_gt (T / δ)
  have hNR : 0 < (N : ℝ) := (div_pos hT hδ).trans hN
  let h : ℝ := T / (N : ℝ)
  have hh : 0 < h := div_pos hT hNR
  have hhδ : h ≤ δ := by
    apply (div_le_iff₀ hNR).mpr
    have hb := (div_lt_iff₀ hδ).mp hN
    nlinarith
  have hperiod : (N : ℝ) * h = T := by
    dsimp only [h]
    field_simp
  have hex : ∀ k : ℕ, k ≤ N → ∃ ρ > 0, ∃ X : E → ℝ → E,
      IsBanachFlowOn f U (ball (c 0) ρ) ((k : ℝ) * h) X ∧
      (∀ t ∈ Icc (0 : ℝ) ((k : ℝ) * h),
        ContDiffOn ℝ n (fun b => X b t) (ball (c 0) ρ)) ∧
      X (c 0) ((k : ℝ) * h) = c ((k : ℝ) * h) := by
    intro k
    induction k with
    | zero =>
      intro _
      obtain ⟨ρ, hρ, X, hX, hs, _⟩ := hlocal 0 ⟨le_rfl, hT.le⟩
      refine ⟨ρ, hρ, X, ?_, ?_, ?_⟩
      · simpa only [Nat.cast_zero, zero_mul] using hX.mono_time hδ.le
      · intro t ht
        simp only [Nat.cast_zero, zero_mul, mem_Icc] at ht
        have ht0 : t = 0 := le_antisymm ht.2 ht.1
        subst t
        exact hs 0 ⟨le_rfl, hδ.le⟩
      · simpa only [Nat.cast_zero, zero_mul] using hX.initial (c 0) (mem_ball_self hρ)
    | succ k ih =>
      intro hkN
      have hkN' : k ≤ N := (Nat.le_succ k).trans hkN
      obtain ⟨ρ₀, hρ₀, X, hX, hsX, heX⟩ := ih hkN'
      have hk0 : 0 ≤ (k : ℝ) * h := mul_nonneg (Nat.cast_nonneg k) hh.le
      have hkT : (k : ℝ) * h ≤ T :=
        (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hkN') hh.le).trans_eq hperiod
      obtain ⟨r, hr, Y, hY, hsY, heY⟩ := hlocal ((k : ℝ) * h) ⟨hk0, hkT⟩
      have hXc : ContinuousAt (fun b => X b ((k : ℝ) * h)) (c 0) :=
        (hsX ((k : ℝ) * h) ⟨hk0, le_rfl⟩).continuousOn.continuousAt
          (isOpen_ball.mem_nhds (mem_ball_self hρ₀))
      have hnear : {b | X b ((k : ℝ) * h) ∈ ball (c ((k : ℝ) * h)) r} ∈ 𝓝 (c 0) :=
        hXc (by
          change ball (c ((k : ℝ) * h)) r ∈ 𝓝 (X (c 0) ((k : ℝ) * h))
          rw [heX]
          exact ball_mem_nhds _ hr)
      obtain ⟨ρ, hρ, hρsub⟩ := Metric.mem_nhds_iff.mp
        (inter_mem (ball_mem_nhds (c 0) hρ₀) hnear)
      have hsub : ball (c 0) ρ ⊆ ball (c 0) ρ₀ := hρsub.trans inter_subset_left
      have hmap : MapsTo (fun b => X b ((k : ℝ) * h))
          (ball (c 0) ρ) (ball (c ((k : ℝ) * h)) r) :=
        fun b hb => (hρsub hb).2
      have hYr := hY.mono_time hhδ
      have hsYr : ∀ s ∈ Icc (0 : ℝ) h,
          ContDiffOn ℝ n (fun b => Y b s) (ball (c ((k : ℝ) * h)) r) :=
        fun s hs => hsY s ⟨hs.1, hs.2.trans hhδ⟩
      have hnext : ((k + 1 : ℕ) : ℝ) * h = (k : ℝ) * h + h := by
        push_cast
        ring
      refine ⟨ρ, hρ, concatenateBanachFlows X Y ((k : ℝ) * h), ?_, ?_, ?_⟩
      · rw [hnext]
        exact (hX.mono_initial hsub).concatenate hYr hk0 hh.le hmap
      · rw [hnext]
        intro t ht
        exact contDiffOn_concatenateBanachFlows hk0 hh.le
          (fun s hs => (hsX s hs).mono hsub) hsYr hmap ht
      · rw [hnext]
        have hgt : ¬(k : ℝ) * h + h ≤ (k : ℝ) * h := by linarith
        simp only [concatenateBanachFlows, if_neg hgt, add_sub_cancel_left, heX]
        exact heY ⟨hh.le, hhδ⟩
  obtain ⟨ρ, hρ, X, hX, hs, _⟩ := hex N le_rfl
  rw [hperiod] at hX hs
  refine ⟨ρ, hρ, X, hX, hs, ?_⟩
  exact eqOn_of_banachODE_open hU (hf.of_le (by simp))
    (hX.continuous (c 0) (mem_ball_self hρ)) hc.continuousOn
    (hX.mem (c 0) (mem_ball_self hρ)) (fun t _ => hcU t)
    (fun t ht => hX.hasDerivAt (c 0) (mem_ball_self hρ) t ⟨ht.1, ht.2.le⟩)
    (fun t _ => hcd t) (hX.initial (c 0) (mem_ball_self hρ))

end Euler2D

end
