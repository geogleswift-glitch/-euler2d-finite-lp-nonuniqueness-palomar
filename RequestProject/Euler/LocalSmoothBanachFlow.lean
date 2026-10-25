module

public import RequestProject.Euler.BanachFlowRegularity

/-! A genuine common local flow with any requested finite order of
initial-data regularity, at every point of an open smooth field domain. -/

@[expose] public section

noncomputable section

open Set Filter Topology Metric
open scoped NNReal ContDiff

namespace Euler2D

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem exists_local_smooth_banachFlow (n : ℕ) {f : E → E} {U : Set E}
    (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U) {a : E} (ha : a ∈ U) :
    ∃ ρ > 0, ∃ τ > 0, ∃ X : E → ℝ → E,
      IsBanachFlowOn f U (ball a ρ) τ X ∧
      ∀ t ∈ Icc (0 : ℝ) τ, ContDiffOn ℝ n (fun b => X b t) (ball a ρ) := by
  have hfa : ContDiffAt ℝ 1 f a :=
    ((hf a ha).contDiffAt (hU.mem_nhds ha)).of_le (by simp)
  obtain ⟨K, V, hV, hLip⟩ := hfa.exists_lipschitzOnWith
  obtain ⟨r, hr, hb, T, hT, X, hX⟩ :=
    exists_local_banachFlow_of_lipschitzOn_nhds f a
      (inter_mem hV (hU.mem_nhds ha)) (hLip.mono inter_subset_left)
  have hbU : ball a r ⊆ U := hb.trans inter_subset_right
  have hbV : ball a r ⊆ V := hb.trans inter_subset_left
  obtain ⟨ρ, hρ, hρV, τ, hτ, hτT, hs⟩ :=
    banachFlow_contDiffOn_initial_locally n isOpen_ball (hf.mono hbU) (hLip.mono hbV)
      (ball_mem_nhds a (by positivity : 0 < r / 4)) hT hX
  refine ⟨ρ, hρ, τ, hτ, X, ?_, hs⟩
  have hXs := (hX.mono_initial hρV).mono_time hτT
  exact ⟨hXs.initial, hXs.continuous, hXs.hasDerivAt,
    fun b hb t ht => hbU (hXs.mem b hb t ht)⟩

end Euler2D

end
