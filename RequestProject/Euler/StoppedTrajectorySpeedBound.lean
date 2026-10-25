module

public import RequestProject.Euler.ContinuousCaptureSection
public import RequestProject.Euler.CoupledPlanarBiotSavartAffine

/-! A speed bound needed only before an actual first exit controls the
entire existing trajectory. The material corollary uses the genuine
singular Biot--Savart velocity and its actual initial-label mass. -/

@[expose] public section

set_option maxHeartbeats 4000000
set_option maxRecDepth 6000

noncomputable section

open Set MeasureTheory

namespace Euler2D

theorem trajectory_bound_of_stopped_speed
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {T C R B : ℝ} (hT : 0 ≤ T) (hC : 0 ≤ C)
    (X v : ℝ → E) (hX : ContinuousOn X (Icc (0 : ℝ) T))
    (hinit : ‖X 0‖ ≤ R) (hgap : R + C * T < B)
    (hderiv : ∀ t ∈ Icc (0 : ℝ) T, ‖X t‖ ≤ B → HasDerivAt X (v t) t)
    (hspeed : ∀ t ∈ Icc (0 : ℝ) T, ‖X t‖ ≤ B → ‖v t‖ ≤ C) :
    ∀ t ∈ Icc (0 : ℝ) T, ‖X t‖ < B ∧ ‖X t - X 0‖ ≤ C * t ∧ ‖X t‖ ≤ R + C * t := by
  have hstart : ‖X 0‖ < B := by nlinarith only [hinit, hgap, mul_nonneg hC hT]
  have hinside : ∀ t ∈ Icc (0 : ℝ) T, ‖X t‖ < B := by
    intro t ht
    by_contra hn
    have hsub : Icc (0 : ℝ) t ⊆ Icc (0 : ℝ) T := fun _ hu => ⟨hu.1, hu.2.trans ht.2⟩
    obtain ⟨τ, hτ, hnorm, hbefore⟩ := exists_first_continuous_norm_section ht.1 X
      (hX.mono hsub) hstart (not_lt.mp hn)
    have hτT : τ ≤ T := hτ.2.trans ht.2
    have hclosed (u : ℝ) (hu : u ∈ Icc (0 : ℝ) τ) : ‖X u‖ ≤ B := by
      rcases lt_or_eq_of_le hu.2 with hlt | rfl
      · exact (hbefore u ⟨hu.1, hlt⟩).le
      · exact hnorm.le
    have hdisp : ‖X τ - X 0‖ ≤ C * (τ - 0) := by
      apply norm_image_sub_le_of_norm_deriv_le_segment'
        (fun u hu => (hderiv u ⟨hu.1, hu.2.trans hτT⟩ (hclosed u hu)).hasDerivWithinAt)
        (fun u hu => hspeed u ⟨hu.1, hu.2.le.trans hτT⟩ (hclosed u ⟨hu.1, hu.2.le⟩))
        τ ⟨hτ.1.le, le_rfl⟩
    have htriangle := norm_le_norm_sub_add (X τ) (X 0)
    have htime := mul_le_mul_of_nonneg_left hτT hC
    rw [hnorm] at htriangle
    linarith only [htriangle, hdisp, hinit, htime, hgap]
  intro t ht
  have hdisp : ‖X t - X 0‖ ≤ C * t := by
    have hh : ‖X t - X 0‖ ≤ C * (t - 0) := by
      apply norm_image_sub_le_of_norm_deriv_le_segment'
        (fun u hu => (hderiv u ⟨hu.1, hu.2.trans ht.2⟩
          (hinside u ⟨hu.1, hu.2.trans ht.2⟩).le).hasDerivWithinAt)
        (fun u hu => hspeed u ⟨hu.1, hu.2.le.trans ht.2⟩
          (hinside u ⟨hu.1, hu.2.le.trans ht.2⟩).le) t ⟨ht.1, le_rfl⟩
    simpa only [sub_zero] using hh
  refine ⟨hinside t ht, hdisp, ?_⟩
  have hh := norm_le_norm_sub_add (X t) (X 0)
  linarith only [hh, hdisp, hinit]

theorem planar_material_trajectory_bound_of_stopped_error
    {w : R2 → ℝ} {T L M ε R B : ℝ}
    (hw : Integrable w) (hL : ∀ b, ‖w b‖ ≤ L)
    (hM : (∫ b : R2, ‖w b‖) ≤ M) (hε : 0 ≤ ε) (hT : 0 ≤ T)
    (H : ℝ → R2 ≃ₜ R2) (hH : ∀ t ∈ Icc (0 : ℝ) T, MeasurePreserving (H t) volume volume)
    (X v : ℝ → R2) (hX : ContinuousOn X (Icc (0 : ℝ) T))
    (hinit : ‖X 0‖ ≤ R) (hgap : R + (L + M + ε) * T < B)
    (hderiv : ∀ t ∈ Icc (0 : ℝ) T, ‖X t‖ ≤ B → HasDerivAt X (v t) t)
    (herror : ∀ t ∈ Icc (0 : ℝ) T, ‖X t‖ ≤ B →
      ‖v t - planarMaterialLabelVelocity kernelK w (H t) (X t)‖ ≤ ε) :
    ∀ t ∈ Icc (0 : ℝ) T, ‖X t‖ < B ∧
      ‖X t - X 0‖ ≤ (L + M + ε) * t ∧ ‖X t‖ ≤ R + (L + M + ε) * t := by
  have hL0 : 0 ≤ L := (norm_nonneg (w 0)).trans (hL 0)
  have hM0 : 0 ≤ M := (integral_nonneg (fun b : R2 => norm_nonneg (w b))).trans hM
  apply trajectory_bound_of_stopped_speed hT (by positivity) X v hX hinit hgap hderiv
  intro t ht hbound
  have hs := norm_planarMaterialBiotSavart_le_sum hw hL (H t) (hH t ht) (X t)
  have he := herror t ht hbound
  have htri := norm_le_norm_sub_add (v t) (planarMaterialLabelVelocity kernelK w (H t) (X t))
  linarith only [hs, he, htri, hM]

end Euler2D

end
