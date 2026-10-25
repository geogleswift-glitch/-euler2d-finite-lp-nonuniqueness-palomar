module

public import RequestProject.Euler.CircularFiniteSourceSupport

/-! A genuine bounded Euler particle system preserves a strict support
buffer for a positive time beyond an intermediate endpoint. This is a
local continuation time; dependence on the finite amplitude is allowed. -/

@[expose] public section

set_option maxHeartbeats 2500000

noncomputable section

open MeasureTheory Set Filter Topology Metric
open scoped NNReal ENNReal

namespace Euler2D
namespace BoundedEulerParticleSystem

variable {f : Lp ℝ 2 μT} {T : ℝ} (S : BoundedEulerParticleSystem f T)

theorem exists_extended_transported_support_window
    {w : R2 → ℝ} {A : Set R2} {D B a₀ a : ℝ}
    (hD : 0 ≤ D) (hDT : D < T)
    (hB0 : 0 ≤ B) (hB : ∀ᵐ x ∂μT, ‖f x‖ ≤ B)
    (ha₀ : 0 ≤ a₀) (haa : a₀ < a) (ha1 : a < 1)
    (hAbox : A ⊆ torusBox) (hw : ∀ x ∈ torusBox, x ∉ A → w x = 0)
    (hstart : ∀ y ∈ A, ‖S.forward D y - torusCenter‖ ≤ a₀)
    (hpast : ∀ t ∈ Icc (0 : ℝ) D, ∀ x ∈ torusBox,
      a₀ < ‖x - torusCenter‖ → S.transportedScalar w t x = 0) :
    ∃ δ > 0, D + δ ≤ T ∧ ∀ t ∈ Icc (0 : ℝ) (D + δ), ∀ x ∈ torusBox,
      a < ‖x - torusCenter‖ → S.transportedScalar w t x = 0 := by
  let V := B * ∫ z in torusBox, ‖torusBiotSavartKernel z‖
  have hV : 0 ≤ V := mul_nonneg hB0 (integral_nonneg (fun _ => norm_nonneg _))
  have hden : 0 < 2 * (V + 1) := by positivity
  let δ := min (T - D) ((a - a₀) / (2 * (V + 1)))
  have hδ : 0 < δ := lt_min (sub_pos.mpr hDT) (div_pos (sub_pos.mpr haa) hden)
  have hδT : D + δ ≤ T := by have hh := min_le_left (T - D) ((a - a₀) / (2 * (V + 1))); linarith
  have hDmem : D ∈ Icc (0 : ℝ) T := ⟨hD, hDT.le⟩
  have hfuture (t : ℝ) (ht : t ∈ Icc D (D + δ)) :
      ∀ x ∈ torusBox, a < ‖x - torusCenter‖ → S.transportedScalar w t x = 0 := by
    have htT : t ∈ Icc (0 : ℝ) T := ⟨hD.trans ht.1, ht.2.trans hδT⟩
    have htd : t - D ≤ δ := by linarith [ht.2]
    have hmul : (t - D) * (2 * (V + 1)) ≤ a - a₀ :=
      (le_div_iff₀ hden).mp (htd.trans (min_le_right _ _))
    have htime : V * (t - D) + a₀ < a := by nlinarith [sub_nonneg.mpr ht.1]
    have himage_norm (y : R2) (hy : y ∈ A) : ‖S.forward t y - torusCenter‖ < a := by
      have hdisp := norm_trajectory_sub_time_le (fun s hs => S.derivative s hs y)
        (fun s _ x => norm_particleVelocityRepresentative_le f hB S.backward S.backward_area s x)
        hDmem htT
      have hd : ‖S.forward t y - S.forward D y‖ ≤ V * (t - D) := by
        simpa only [abs_of_nonneg (sub_nonneg.mpr ht.1)] using hdisp
      exact ((norm_sub_le_norm_sub_add_norm_sub (S.forward t y) (S.forward D y) torusCenter).trans
        (add_le_add hd (hstart y hy))).trans_lt htime
    have himage : S.forward t '' A ⊆ torusBox := by
      rintro x ⟨y, hy, rfl⟩
      exact norm_sub_center_lt_one_mem_box ((himage_norm y hy).trans ha1)
    intro x hx hxa
    by_contra hne
    have hpre : torusWrap (S.backward t x) ∈ A := by
      by_contra hn
      exact hne (hw _ (torusRep_mem _) hn)
    have hximage : x ∈ S.forward t '' A := by
      rw [← S.preimage_patch_inter_box t htT hAbox himage]
      exact ⟨hpre, hx⟩
    obtain ⟨y, hy, he⟩ := hximage
    have hh := himage_norm y hy
    rw [he] at hh
    exact (not_lt_of_ge hh.le) hxa
  refine ⟨δ, hδ, hδT, ?_⟩
  intro t ht x hx hxa
  rcases le_total t D with hle | hge
  · exact hpast t ⟨ht.1, hle⟩ x hx (haa.trans hxa)
  · exact hfuture t ⟨hge, ht.2⟩ x hx hxa

end BoundedEulerParticleSystem
end Euler2D

end
