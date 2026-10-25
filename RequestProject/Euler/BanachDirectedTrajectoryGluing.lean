module

public import RequestProject.Euler.NonautonomousBanachOpenUniqueness

/-! A compatible family of actual trajectories constructs one genuine
trajectory before the supremum of its time intervals. The derivative
at the initial time is retained from one fixed local trajectory. -/

@[expose] public section

set_option maxHeartbeats 2500000

noncomputable section

open Set Filter Topology

namespace Euler2D

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem exists_glued_trajectory_before_sup {ι : Type*} [Nonempty ι]
    {f : ℝ → E → E} {z : E} {D : ℝ} (hD : 0 < D)
    (T : ι → ℝ) (hT : ∀ i, 0 < T i) (X : ι → ℝ → E)
    (hcover : ∀ t < D, ∃ i, t < T i)
    (hinit : ∀ i, X i 0 = z)
    (hd : ∀ i, ∀ t ∈ Icc (0 : ℝ) (T i), HasDerivAt (X i) (f t (X i t)) t)
    (hcompat : ∀ i j, ∀ t ∈ Icc (0 : ℝ) (min (T i) (T j)), X i t = X j t) :
    ∃ α : ℝ → E, α 0 = z ∧
      (∀ t ∈ Ico (0 : ℝ) D, HasDerivAt α (f t (α t)) t) ∧
      (∀ i, ∀ t ∈ Ico (0 : ℝ) D, t ≤ T i → α t = X i t) ∧
      ∀ t ∈ Ico (0 : ℝ) D, ∃ i, t < T i ∧ α t = X i t := by
  classical
  let i₀ : ι := Classical.choice inferInstance
  let α : ℝ → E := fun t =>
    if ht : 0 ≤ t ∧ t < D then X (hcover t ht.2).choose t else X i₀ t
  have heq (i : ι) (t : ℝ) (ht : t ∈ Ico (0 : ℝ) D) (hti : t ≤ T i) : α t = X i t := by
    dsimp only [α]
    rw [dif_pos (show 0 ≤ t ∧ t < D from ht)]
    exact hcompat _ i t ⟨ht.1, le_min (hcover t ht.2).choose_spec.le hti⟩
  have hzero : α 0 = X i₀ 0 := heq i₀ 0 ⟨le_rfl, hD⟩ (hT i₀).le
  refine ⟨α, hzero.trans (hinit i₀), ?_, heq, ?_⟩
  · intro t ht
    rcases eq_or_lt_of_le ht.1 with he | hpos
    · have ht0 : t = 0 := he.symm
      subst t
      have hevent : α =ᶠ[𝓝 (0 : ℝ)] X i₀ := by
        filter_upwards [eventually_lt_nhds hD, eventually_lt_nhds (hT i₀)] with s hsD hsT
        by_cases hs : 0 ≤ s
        · exact heq i₀ s ⟨hs, hsD⟩ hsT.le
        · dsimp only [α]
          rw [dif_neg (fun h => hs h.1)]
      rw [hzero]
      exact (hd i₀ 0 ⟨le_rfl, (hT i₀).le⟩).congr_of_eventuallyEq hevent
    · obtain ⟨i, hti⟩ := hcover t ht.2
      have hevent : α =ᶠ[𝓝 t] X i := by
        filter_upwards [eventually_gt_nhds hpos, eventually_lt_nhds ht.2,
          eventually_lt_nhds hti] with s hs0 hsD hsT
        exact heq i s ⟨hs0.le, hsD⟩ hsT.le
      rw [heq i t ht hti.le]
      exact (hd i t ⟨ht.1, hti.le⟩).congr_of_eventuallyEq hevent
  · intro t ht
    obtain ⟨i, hti⟩ := hcover t ht.2
    exact ⟨i, hti, heq i t ht hti.le⟩

end Euler2D

end
