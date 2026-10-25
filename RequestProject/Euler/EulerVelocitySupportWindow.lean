module

public import RequestProject.Euler.CircularFiniteSourceSupport

/-! Support control from a genuine bound on the actual particle velocity.
The bound can be supplied by a sum over transported labels. -/

@[expose] public section

set_option maxHeartbeats 1800000

noncomputable section

open MeasureTheory Set Filter Topology Metric
open scoped NNReal ENNReal

namespace Euler2D
namespace BoundedEulerParticleSystem

variable {f : Lp ℝ 2 μT} {T : ℝ} (S : BoundedEulerParticleSystem f T)

theorem displacement_le_of_velocity_bound {V : ℝ} (hT : 0 ≤ T)
    (hV : ∀ s ∈ Icc (0 : ℝ) T, ∀ x,
      ‖particleVelocityRepresentative f S.backward S.backward_area s x‖ ≤ V)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) (a : R2) :
    ‖S.forward t a - a‖ ≤ V * t := by
  have hb := norm_trajectory_sub_time_le
    (fun s hs => S.derivative s hs a) hV (s := 0) ⟨le_rfl, hT⟩ ht
  simpa only [S.initial a, sub_zero, abs_of_nonneg ht.1] using hb

theorem transportedScalar_support_of_velocity_bound {V a₀ a : ℝ} {w : R2 → ℝ}
    (hT : 0 ≤ T) (hV0 : 0 ≤ V)
    (hV : ∀ s ∈ Icc (0 : ℝ) T, ∀ x,
      ‖particleVelocityRepresentative f S.backward S.backward_area s x‖ ≤ V)
    (ha₀ : 0 ≤ a₀) (ha1 : a < 1)
    (hw : ∀ x ∈ torusBox, a₀ < ‖x - torusCenter‖ → w x = 0)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) (htime : a₀ + V * t < a) :
    ∀ x ∈ torusBox, a < ‖x - torusCenter‖ → S.transportedScalar w t x = 0 := by
  let D : Set R2 := closedBall torusCenter a₀
  have haa : a₀ < a := by nlinarith [mul_nonneg hV0 ht.1]
  have hDbox : D ⊆ torusBox := by
    intro y hy
    have hn : ‖y - torusCenter‖ ≤ a₀ := mem_closedBall_iff_norm.mp hy
    exact norm_sub_center_lt_one_mem_box (hn.trans_lt (haa.trans ha1))
  have himage_norm (y : R2) (hy : y ∈ D) : ‖S.forward t y - torusCenter‖ < a := by
    have hn : ‖y - torusCenter‖ ≤ a₀ := mem_closedBall_iff_norm.mp hy
    have hd := S.displacement_le_of_velocity_bound hT hV ht y
    have htri : ‖S.forward t y - torusCenter‖ ≤ ‖S.forward t y - y‖ + ‖y - torusCenter‖ := by
      simpa only [sub_add_sub_cancel] using norm_add_le (S.forward t y - y) (y - torusCenter)
    exact (htri.trans (add_le_add hd hn)).trans_lt (by linarith)
  have himage : S.forward t '' D ⊆ torusBox := by
    rintro y ⟨z, hz, rfl⟩
    exact norm_sub_center_lt_one_mem_box ((himage_norm z hz).trans ha1)
  intro x hx hxa
  by_contra hne
  have hpre : torusWrap (S.backward t x) ∈ D := by
    apply mem_closedBall_iff_norm.mpr
    apply le_of_not_gt
    intro hn
    exact hne (hw _ (torusRep_mem _) hn)
  have hximage : x ∈ S.forward t '' D := by
    rw [← S.preimage_patch_inter_box t ht hDbox himage]
    exact ⟨hpre, hx⟩
  obtain ⟨y, hy, he⟩ := hximage
  have hn := himage_norm y hy
  rw [he] at hn
  exact (not_lt_of_ge hn.le) hxa

end BoundedEulerParticleSystem
end Euler2D

end
