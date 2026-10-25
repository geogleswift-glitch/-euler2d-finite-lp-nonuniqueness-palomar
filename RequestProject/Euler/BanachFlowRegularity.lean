module

public import RequestProject.Euler.BanachFlowProlongation
public import RequestProject.Euler.LocalBanachFlowExistence

/-! Genuine finite-order initial-data regularity of actual Banach ODE
flows. Each induction step constructs a real prolonged flow by Picard,
identifies its first component by ODE uniqueness, and uses its second
component as the proved initial-point derivative. -/

@[expose] public section

noncomputable section

open Set Filter Topology Metric
open scoped NNReal ContDiff

namespace Euler2D

namespace IsBanachFlowOn

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {f : E → E} {U V : Set E} {T : ℝ} {X : E → ℝ → E}

theorem mono_initial (hX : IsBanachFlowOn f U V T X) {V₀ : Set E} (hV : V₀ ⊆ V) :
    IsBanachFlowOn f U V₀ T X :=
  ⟨fun b hb => hX.initial b (hV hb), fun b hb => hX.continuous b (hV hb),
    fun b hb => hX.hasDerivAt b (hV hb), fun b hb => hX.mem b (hV hb)⟩

theorem mono_time (hX : IsBanachFlowOn f U V T X) {τ : ℝ} (hτ : τ ≤ T) :
    IsBanachFlowOn f U V τ X :=
  ⟨hX.initial, fun b hb => (hX.continuous b hb).mono (fun _ ht => ⟨ht.1, ht.2.trans hτ⟩),
    fun b hb t ht => hX.hasDerivAt b hb t ⟨ht.1, ht.2.trans hτ⟩,
    fun b hb t ht => hX.mem b hb t ⟨ht.1, ht.2.trans hτ⟩⟩

theorem lipschitzOn_initial (hX : IsBanachFlowOn f U V T X)
    {K : ℝ≥0} (hLip : LipschitzOnWith K f U) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    LipschitzOnWith ⟨Real.exp ((K : ℝ) * t), (Real.exp_pos _).le⟩ (fun b => X b t) V := by
  apply LipschitzOnWith.of_dist_le_mul
  intro b hb c hc
  exact (hX.dist_le hLip hb hc ht).trans_eq (mul_comm _ _)

end IsBanachFlowOn

universe u

/-- For every requested finite order there is a genuine common time
window and an open set of initial data on which the actual flow has that
order of Fréchet smoothness. No regularity of a selected flow is assumed. -/
theorem banachFlow_contDiffOn_initial_locally (n : ℕ)
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {f : E → E} {U V : Set E} (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U)
    {K : ℝ≥0} (hLip : LipschitzOnWith K f U) {a : E} (hV : V ∈ 𝓝 a)
    {T : ℝ} (hT : 0 < T) {X : E → ℝ → E} (hX : IsBanachFlowOn f U V T X) :
    ∃ ρ > 0, ball a ρ ⊆ V ∧ ∃ τ > 0, τ ≤ T ∧
      ∀ t ∈ Icc (0 : ℝ) τ, ContDiffOn ℝ n (fun b => X b t) (ball a ρ) := by
  induction n generalizing E K T with
  | zero =>
    obtain ⟨ρ, hρ, hρV⟩ := Metric.mem_nhds_iff.mp hV
    refine ⟨ρ, hρ, hρV, T, hT, le_rfl, ?_⟩
    intro t ht
    rw [Nat.cast_zero, contDiffOn_zero]
    exact (hX.lipschitzOn_initial hLip ht).continuousOn.mono hρV
  | succ n ih =>
    obtain ⟨ρ₀, hρ₀, hρ₀V⟩ := Metric.mem_nhds_iff.mp hV
    have haV : a ∈ V := mem_of_mem_nhds hV
    have haU : a ∈ U := by
      have h := hX.mem a haV 0 ⟨le_rfl, hT.le⟩
      rwa [hX.initial a haV] at h
    let p₀ : E × (E →L[ℝ] E) := (a, ContinuousLinearMap.id ℝ E)
    let M : Set (E × (E →L[ℝ] E)) := U ×ˢ univ
    have hM : IsOpen M := hU.prod isOpen_univ
    have hp₀ : p₀ ∈ M := ⟨haU, mem_univ _⟩
    have hF : ContDiffOn ℝ ∞ (banachFlowProlongation f) M := contDiffOn_banachFlowProlongation hU hf
    have hF₁ : ContDiffAt ℝ 1 (banachFlowProlongation f) p₀ :=
      ((hF p₀ hp₀).contDiffAt (hM.mem_nhds hp₀)).of_le (by simp)
    obtain ⟨K₁, S, hS, hLipS⟩ := hF₁.exists_lipschitzOnWith
    obtain ⟨r, hr, hball, T₁, hT₁, Y, hY⟩ :=
      exists_local_banachFlow_of_lipschitzOn_nhds (banachFlowProlongation f) p₀
        (U := S ∩ M) (inter_mem hS (hM.mem_nhds hp₀)) (hLipS.mono inter_subset_left)
    have hW (p : E × (E →L[ℝ] E)) (hp : p ∈ ball p₀ r) : p.1 ∈ U := (hball hp).2.1
    have hFW : ContDiffOn ℝ ∞ (banachFlowProlongation f) (ball p₀ r) :=
      hF.mono (fun _ hp => (hball hp).2)
    have hLipW : LipschitzOnWith K₁ (banachFlowProlongation f) (ball p₀ r) :=
      hLipS.mono (fun _ hp => (hball hp).1)
    obtain ⟨ρ₁, hρ₁, hρ₁V, τ₁, hτ₁, hτ₁T, hYn⟩ :=
      ih isOpen_ball hFW hLipW (ball_mem_nhds p₀ (by positivity : 0 < r / 4)) hT₁ hY
    let ρ := min ρ₀ ρ₁
    let τ := min T τ₁
    have hρ : 0 < ρ := lt_min hρ₀ hρ₁
    have hτ : 0 < τ := lt_min hT hτ₁
    have hOV : ball a ρ ⊆ V := (ball_subset_ball (min_le_left _ _)).trans hρ₀V
    have hOY (b : E) (hb : b ∈ ball a ρ) :
        (b, ContinuousLinearMap.id ℝ E) ∈ ball p₀ ρ₁ := by
      rw [mem_ball, Prod.dist_eq, dist_self, max_eq_left dist_nonneg]
      exact (mem_ball.mp hb).trans_le (min_le_right _ _)
    have hXτ := hX.mono_time (min_le_left T τ₁)
    have hYτ := (hY.mono_initial hρ₁V).mono_time ((min_le_right T τ₁).trans hτ₁T)
    refine ⟨ρ, hρ, hOV, τ, hτ, min_le_left _ _, ?_⟩
    intro t ht
    exact contDiffOn_succ_banachFlow_from_prolongation hU (hf.of_le (by simp)) hLip hτ.le
      hXτ hYτ hW isOpen_ball hOV hOY n ht
      (hYn t ⟨ht.1, ht.2.trans (min_le_right _ _)⟩)

end Euler2D

end
