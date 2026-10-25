module

public import RequestProject.Euler.LocalSmoothBanachFlow
public import Mathlib.Topology.Algebra.MetricSpace.Lipschitz

/-! Genuine uniqueness on an entire compact time interval in an open
C¹ Banach field domain, without assuming a global Lipschitz constant. -/

@[expose] public section

noncomputable section

open Set Filter Topology Metric
open scoped NNReal ContDiff

namespace Euler2D

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem eqOn_of_banachODE_open {f : E → E} {U : Set E}
    (hU : IsOpen U) (hf : ContDiffOn ℝ 1 f U) {a b : ℝ} {α β : ℝ → E}
    (hαc : ContinuousOn α (Icc a b)) (hβc : ContinuousOn β (Icc a b))
    (hαU : ∀ t ∈ Icc a b, α t ∈ U) (hβU : ∀ t ∈ Icc a b, β t ∈ U)
    (hαd : ∀ t ∈ Ico a b, HasDerivAt α (f (α t)) t)
    (hβd : ∀ t ∈ Ico a b, HasDerivAt β (f (β t)) t)
    (h0 : α a = β a) : EqOn α β (Icc a b) := by
  let K : Set E := α '' Icc a b ∪ β '' Icc a b
  have hK : IsCompact K :=
    (isCompact_Icc.image_of_continuousOn hαc).union
      (isCompact_Icc.image_of_continuousOn hβc)
  have hKU : K ⊆ U := by
    rintro x (⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩)
    · exact hαU t ht
    · exact hβU t ht
  have hl : LocallyLipschitzOn K f := by
    intro x hx
    obtain ⟨L, V, hV, hLip⟩ :=
      ((hf x (hKU hx)).contDiffAt (hU.mem_nhds (hKU hx))).exists_lipschitzOnWith
    exact ⟨L, V, nhdsWithin_le_nhds hV, hLip⟩
  obtain ⟨L, hL⟩ := hl.exists_lipschitzOnWith_of_compact hK
  exact ODE_solution_unique_of_mem_Icc_right (v := fun _ : ℝ => f) (s := fun _ => K)
    (fun _ _ => hL) hαc (fun t ht => (hαd t ht).hasDerivWithinAt)
    (fun t ht => Or.inl (mem_image_of_mem α ⟨ht.1, ht.2.le⟩))
    hβc (fun t ht => (hβd t ht).hasDerivWithinAt)
    (fun t ht => Or.inr (mem_image_of_mem β ⟨ht.1, ht.2.le⟩)) h0

end Euler2D

end
