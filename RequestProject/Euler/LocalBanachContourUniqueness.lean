module

public import RequestProject.Euler.LocalBanachContourODE
public import Mathlib.Analysis.ODE.Gronwall

/-! Actual local uniqueness for the same open-subset Banach ODE. -/

@[expose] public section

noncomputable section

open Set Filter Topology
open scoped NNReal

namespace Euler2D

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem locally_unique_curve_on_open_subtype {U : Set E} (hU : IsOpen U)
    (F : U → E) (hF : LocallyLipschitz F) (x : U)
    {α β : ℝ → E} {t₀ : ℝ} (hα0 : α t₀ = x.val) (hβ0 : β t₀ = x.val)
    (hα : ∀ᶠ t in 𝓝 t₀, ∃ ht : α t ∈ U, HasDerivAt α (F ⟨α t, ht⟩) t)
    (hβ : ∀ᶠ t in 𝓝 t₀, ∃ ht : β t ∈ U, HasDerivAt β (F ⟨β t, ht⟩) t) :
    α =ᶠ[𝓝 t₀] β := by
  classical
  obtain ⟨K, V, hV, hLip⟩ := hF x
  have himage : (Subtype.val '' V : Set E) ∈ 𝓝 x.val := by
    rw [← map_nhds_subtype_coe_eq_nhds x.property (hU.mem_nhds x.property)]
    exact image_mem_map hV
  let G := openSubtypeFieldExtension U F
  have hG : LipschitzOnWith K G (Subtype.val '' V) := by
    rintro y ⟨v, hv, rfl⟩ z ⟨w, hw, rfl⟩
    simpa only [G, openSubtypeFieldExtension_of_mem, Subtype.edist_eq] using hLip hv hw
  obtain ⟨hαU, hαd⟩ := mem_of_mem_nhds hα
  obtain ⟨hβU, hβd⟩ := mem_of_mem_nhds hβ
  have hαV : ∀ᶠ t in 𝓝 t₀, α t ∈ Subtype.val '' V :=
    hαd.continuousAt (hα0 ▸ himage)
  have hβV : ∀ᶠ t in 𝓝 t₀, β t ∈ Subtype.val '' V :=
    hβd.continuousAt (hβ0 ▸ himage)
  have hαG : ∀ᶠ t in 𝓝 t₀, HasDerivAt α (G (α t)) t ∧ α t ∈ Subtype.val '' V := by
    filter_upwards [hα, hαV] with t ht hVt
    obtain ⟨htU, hdt⟩ := ht
    exact ⟨by simpa only [G, openSubtypeFieldExtension, dif_pos htU] using hdt, hVt⟩
  have hβG : ∀ᶠ t in 𝓝 t₀, HasDerivAt β (G (β t)) t ∧ β t ∈ Subtype.val '' V := by
    filter_upwards [hβ, hβV] with t ht hVt
    obtain ⟨htU, hdt⟩ := ht
    exact ⟨by simpa only [G, openSubtypeFieldExtension, dif_pos htU] using hdt, hVt⟩
  exact ODE_solution_unique_of_eventually (Eventually.of_forall (fun _ => hG))
    hαG hβG (hα0.trans hβ0.symm)

end Euler2D

end
