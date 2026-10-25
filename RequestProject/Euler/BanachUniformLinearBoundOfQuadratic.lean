module

public import RequestProject.Euler.BanachFlowQuadraticLinearization

/-! A uniform quadratic variation bound gives a uniform linear
displacement bound on a compact time window in the same Banach norm. -/

@[expose] public section

noncomputable section

open Set Filter Topology Metric

namespace Euler2D

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem exists_uniform_linear_bound_of_quadratic_variation
    {a : E} {c : ℝ → E} {T δ C : ℝ} {X : E → ℝ → E} {A : ℝ → E →L[ℝ] E}
    (hAc : ContinuousOn A (Icc (0 : ℝ) T)) (hδ : 0 < δ) (hC : 0 < C)
    (hquad : ∀ h : E, ‖h‖ ≤ δ → ∀ t ∈ Icc (0 : ℝ) T,
      ‖X (a + h) t - c t - A t h‖ ≤ C * ‖h‖ ^ 2) :
    ∃ ε > 0, ∃ B > 0, ∀ b : E, ‖b - a‖ ≤ ε → ∀ t ∈ Icc (0 : ℝ) T,
      ‖X b t - c t‖ ≤ B * ‖b - a‖ := by
  obtain ⟨M, hM⟩ := (isCompact_Icc.image_of_continuousOn hAc).isBounded.exists_norm_le
  refine ⟨min δ 1, lt_min hδ (by norm_num), |M| + C + 1, by positivity, ?_⟩
  intro b hb t ht
  let v := b - a
  have hvδ : ‖v‖ ≤ δ := hb.trans (min_le_left _ _)
  have hv1 : ‖v‖ ≤ 1 := hb.trans (min_le_right _ _)
  have hAv : ‖A t v‖ ≤ |M| * ‖v‖ := by
    calc
      _ ≤ ‖A t‖ * ‖v‖ := (A t).le_opNorm _
      _ ≤ |M| * ‖v‖ := mul_le_mul_of_nonneg_right
        ((hM _ (mem_image_of_mem A ht)).trans (le_abs_self M)) (norm_nonneg v)
  have he : a + v = b := by dsimp only [v]; abel
  have hq := hquad v hvδ t ht
  rw [he] at hq
  calc
    _ ≤ ‖X b t - c t - A t v‖ + ‖A t v‖ := norm_le_norm_sub_add _ _
    _ ≤ C * ‖v‖ ^ 2 + |M| * ‖v‖ := add_le_add hq hAv
    _ ≤ (|M| + C + 1) * ‖b - a‖ := by
      change C * ‖v‖ ^ 2 + |M| * ‖v‖ ≤ (|M| + C + 1) * ‖v‖
      have hh := mul_le_mul_of_nonneg_left hv1 (mul_nonneg hC.le (norm_nonneg v))
      nlinarith [norm_nonneg v]

end Euler2D

end
