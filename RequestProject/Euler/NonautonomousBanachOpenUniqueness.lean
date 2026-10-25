module

public import RequestProject.Euler.BanachOpenODEUniqueness

/-! Genuine uniqueness for a smooth autonomous field plus the same
time-dependent state-Lipschitz forcing on an open Banach domain. -/

@[expose] public section

noncomputable section

open Set Filter Topology Metric
open scoped NNReal ContDiff

namespace Euler2D

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem eqOn_of_forced_banachODE_open {f : E → E} {U : Set E}
    (hU : IsOpen U) (hf : ContDiffOn ℝ 1 f U)
    {q : ℝ → E → E} {K : ℝ≥0} (hq : ∀ t, LipschitzOnWith K (q t) U)
    {a b : ℝ} {α β : ℝ → E}
    (hαc : ContinuousOn α (Icc a b)) (hβc : ContinuousOn β (Icc a b))
    (hαU : ∀ t ∈ Icc a b, α t ∈ U) (hβU : ∀ t ∈ Icc a b, β t ∈ U)
    (hαd : ∀ t ∈ Ico a b, HasDerivAt α (f (α t) + q t (α t)) t)
    (hβd : ∀ t ∈ Ico a b, HasDerivAt β (f (β t) + q t (β t)) t)
    (h0 : α a = β a) : EqOn α β (Icc a b) := by
  let C : Set E := α '' Icc a b ∪ β '' Icc a b
  have hC : IsCompact C :=
    (isCompact_Icc.image_of_continuousOn hαc).union
      (isCompact_Icc.image_of_continuousOn hβc)
  have hCU : C ⊆ U := by
    rintro x (⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩)
    · exact hαU t ht
    · exact hβU t ht
  have hl : LocallyLipschitzOn C f := by
    intro x hx
    obtain ⟨L, V, hV, hLip⟩ :=
      ((hf x (hCU hx)).contDiffAt (hU.mem_nhds (hCU hx))).exists_lipschitzOnWith
    exact ⟨L, V, nhdsWithin_le_nhds hV, hLip⟩
  obtain ⟨L, hL⟩ := hl.exists_lipschitzOnWith_of_compact hC
  have htotal (t : ℝ) : LipschitzOnWith (L + K) (fun x => f x + q t x) C :=
    hL.add ((hq t).mono hCU)
  exact ODE_solution_unique_of_mem_Icc_right
    (v := fun t x => f x + q t x) (s := fun _ => C) (fun t _ => htotal t)
    hαc (fun t ht => (hαd t ht).hasDerivWithinAt)
    (fun t ht => Or.inl (mem_image_of_mem α ⟨ht.1, ht.2.le⟩))
    hβc (fun t ht => (hβd t ht).hasDerivWithinAt)
    (fun t ht => Or.inr (mem_image_of_mem β ⟨ht.1, ht.2.le⟩)) h0

end Euler2D

end
