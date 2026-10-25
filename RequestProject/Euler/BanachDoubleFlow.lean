module

public import RequestProject.Euler.BanachFlowConcatenation

/-! A true two-period material flow on exactly the initial points
whose intermediate return remains in the genuine original flow domain. -/

@[expose] public section

noncomputable section

open Set Filter Topology Metric

namespace Euler2D

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def banachDoubleFlowDomain (X : E → ℝ → E) (V : Set E) (T : ℝ) : Set E :=
  V ∩ {b | X b T ∈ V}

def banachDoubleFlow (X : E → ℝ → E) (T : ℝ) : E → ℝ → E :=
  concatenateBanachFlows X X T

theorem isBanachFlowOn_banachDoubleFlow {f : E → E} {U V : Set E} {T : ℝ} {X : E → ℝ → E}
    (hT : 0 ≤ T) (hX : IsBanachFlowOn f U V T X) :
    IsBanachFlowOn f U (banachDoubleFlowDomain X V T) (T + T) (banachDoubleFlow X T) := by
  have hsub : banachDoubleFlowDomain X V T ⊆ V := fun _ hb => hb.1
  exact (hX.mono_initial hsub).concatenate hX hT hT (fun _ hb => hb.2)

theorem banachDoubleFlow_endpoint {T : ℝ} (hT : 0 < T) (X : E → ℝ → E) (b : E) :
    banachDoubleFlow X T b (T + T) = X (X b T) T := by
  change (if T + T ≤ T then X b (T + T) else X (X b T) (T + T - T)) = _
  rw [if_neg (by linarith), add_sub_cancel_left]

theorem banachDoubleFlow_invariant {X : E → ℝ → E} {V : Set E} {T : ℝ} (hT : 0 ≤ T)
    (Q : E → Prop)
    (hQ : ∀ b ∈ V, Q b → ∀ s ∈ Icc (0 : ℝ) T, Q (X b s))
    {b : E} (hb : b ∈ banachDoubleFlowDomain X V T) (hbQ : Q b)
    {s : ℝ} (hs : s ∈ Icc (0 : ℝ) (T + T)) : Q (banachDoubleFlow X T b s) := by
  change Q (if s ≤ T then X b s else X (X b T) (s - T))
  by_cases hst : s ≤ T
  · rw [if_pos hst]
    exact hQ b hb.1 hbQ s ⟨hs.1, hst⟩
  · rw [if_neg hst]
    exact hQ (X b T) hb.2 (hQ b hb.1 hbQ T ⟨hT, le_rfl⟩) (s - T)
      ⟨by linarith, by linarith [hs.2]⟩

end Euler2D

end
