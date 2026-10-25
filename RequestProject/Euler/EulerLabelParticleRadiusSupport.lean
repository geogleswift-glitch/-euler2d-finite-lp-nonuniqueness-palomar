module

public import RequestProject.Euler.EulerLabelSupportEndpointWindow

/-! A genuine particle radius estimate on a provisional half-open
interval closes at its endpoint by continuity. It also gives the
literal raw label support, so endpoint source validity does not need
to be assumed independently of the particle fence. -/

@[expose] public section

set_option maxHeartbeats 3000000

noncomputable section

open MeasureTheory Set Filter Topology Metric
open scoped NNReal ENNReal

namespace Euler2D
namespace BoundedEulerParticleSystem

variable {f : Lp ℝ 2 μT} {T : ℝ} (S : BoundedEulerParticleSystem f T)

theorem particle_radius_closed_of_prebound {A : Set R2} {D a : ℝ}
    (hD : 0 < D)
    (hpre : ∀ t ∈ Ico (0 : ℝ) D, ∀ y ∈ A, ‖S.forward t y - torusCenter‖ ≤ a) :
    ∀ t ∈ Icc (0 : ℝ) D, ∀ y ∈ A, ‖S.forward t y - torusCenter‖ ≤ a := by
  have hend (y : R2) (hy : y ∈ A) : ‖S.forward D y - torusCenter‖ ≤ a := by
    have hc : Continuous (fun t : ℝ => ‖S.forward t y - torusCenter‖) :=
      ((S.forward_continuous.comp (continuous_id.prodMk continuous_const)).sub continuous_const).norm
    have hclosed : IsClosed {t : ℝ | ‖S.forward t y - torusCenter‖ ≤ a} :=
      isClosed_le hc continuous_const
    have hmem : D ∈ closure (Ico (0 : ℝ) D) := by
      rw [closure_Ico (ne_of_lt hD)]
      exact ⟨hD.le, le_rfl⟩
    exact (closure_minimal (fun t ht => hpre t ht y hy) hclosed) hmem
  intro t ht y hy
  rcases lt_or_eq_of_le ht.2 with hlt | rfl
  · exact hpre t ⟨ht.1, hlt⟩ y hy
  · exact hend y hy

theorem transportedScalar_support_of_particle_radius
    {w : R2 → ℝ} {A : Set R2} {t a : ℝ}
    (ht : t ∈ Icc (0 : ℝ) T) (ha1 : a < 1)
    (hAbox : A ⊆ torusBox) (hw : ∀ x ∈ torusBox, x ∉ A → w x = 0)
    (hparticles : ∀ y ∈ A, ‖S.forward t y - torusCenter‖ ≤ a) :
    ∀ x ∈ torusBox, a < ‖x - torusCenter‖ → S.transportedScalar w t x = 0 := by
  have himage : S.forward t '' A ⊆ torusBox := by
    rintro x ⟨y, hy, rfl⟩
    exact norm_sub_center_lt_one_mem_box ((hparticles y hy).trans_lt ha1)
  intro x hx hxa
  by_contra hne
  have hpre : torusWrap (S.backward t x) ∈ A := by
    by_contra hn
    exact hne (hw _ (torusRep_mem _) hn)
  have hximage : x ∈ S.forward t '' A := by
    rw [← S.preimage_patch_inter_box t ht hAbox himage]
    exact ⟨hpre, hx⟩
  obtain ⟨y, hy, he⟩ := hximage
  have hh := hparticles y hy
  rw [he] at hh
  exact (not_lt_of_ge hh) hxa

theorem exists_extended_support_of_particle_prebound
    {w : R2 → ℝ} {A : Set R2} {D B a₀ a : ℝ}
    (hD : 0 < D) (hDT : D < T)
    (hB0 : 0 ≤ B) (hB : ∀ᵐ x ∂μT, ‖f x‖ ≤ B)
    (ha₀ : 0 ≤ a₀) (haa : a₀ < a) (ha1 : a < 1)
    (hAbox : A ⊆ torusBox) (hw : ∀ x ∈ torusBox, x ∉ A → w x = 0)
    (hpre : ∀ t ∈ Ico (0 : ℝ) D, ∀ y ∈ A, ‖S.forward t y - torusCenter‖ ≤ a₀) :
    ∃ δ > 0, D + δ ≤ T ∧ ∀ t ∈ Icc (0 : ℝ) (D + δ), ∀ x ∈ torusBox,
      a < ‖x - torusCenter‖ → S.transportedScalar w t x = 0 := by
  have hparticles := S.particle_radius_closed_of_prebound hD hpre
  have hpast : ∀ t ∈ Icc (0 : ℝ) D, ∀ x ∈ torusBox,
      a₀ < ‖x - torusCenter‖ → S.transportedScalar w t x = 0 := by
    intro t ht
    exact S.transportedScalar_support_of_particle_radius ⟨ht.1, ht.2.trans hDT.le⟩
      (haa.trans ha1) hAbox hw (hparticles t ht)
  exact S.exists_extended_transported_support_window hD.le hDT hB0 hB ha₀ haa ha1
    hAbox hw (hparticles D ⟨hD.le, le_rfl⟩) hpast

end BoundedEulerParticleSystem
end Euler2D

end
