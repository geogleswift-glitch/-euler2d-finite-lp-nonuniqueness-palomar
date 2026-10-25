module

public import RequestProject.Euler.BanachCompactReferenceQuadraticFlow
public import RequestProject.Euler.BanachFlowGlobalVariational

/-! The fundamental operator is actually constructed from the true
reference-field derivative. The original material flow then has the
proved uniform quadratic remainder on the full time interval. -/

@[expose] public section

set_option maxHeartbeats 2000000

noncomputable section

open Set Filter Topology Metric
open scoped NNReal ContDiff

namespace Euler2D

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem exists_banachReference_fundamental_operators
    {f : E → E} {U : Set E} (hU : IsOpen U) (hf : ContDiffOn ℝ 1 f U)
    {c : ℝ → E} (hc : Continuous c) (hcK : IsCompact (range c)) (hcU : ∀ t, c t ∈ U)
    {T : ℝ} (hT : 0 ≤ T) :
    ∃ A : ℝ → E →L[ℝ] E, Continuous A ∧ A 0 = ContinuousLinearMap.id ℝ E ∧
      ∀ t ∈ Icc (0 : ℝ) T, HasDerivAt A ((fderiv ℝ f (c t)).comp (A t)) t := by
  have hD : ContinuousOn (fderiv ℝ f) U :=
    (hf.fderiv_of_isOpen hU (m := 0) (by norm_num)).continuousOn
  have hB : Continuous (fun t : ℝ => fderiv ℝ f (c t)) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    exact ((hD (c t) (hcU t)).continuousAt (hU.mem_nhds (hcU t))).comp hc.continuousAt
  have hsub : range c ⊆ U := by rintro _ ⟨t, rfl⟩; exact hcU t
  obtain ⟨M, hM⟩ := (hcK.image_of_continuousOn (hD.mono hsub)).isBounded.exists_norm_le
  let K : ℝ≥0 := ⟨max M 0, le_max_right M 0⟩
  have hbound (t : ℝ) : ‖fderiv ℝ f (c t)‖ ≤ K :=
    (hM _ (mem_image_of_mem _ (mem_range_self t))).trans (le_max_left M 0)
  obtain ⟨A, hAc, hA0, hAd, hnorm⟩ := exists_banachFlow_global_variational_curve hB hbound hT
  exact ⟨A, hAc, hA0, hAd⟩

theorem exists_banachFlow_reference_quadratic_variation
    {f : E → E} {U : Set E} (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U)
    {c : ℝ → E} (hc : Continuous c) (hcK : IsCompact (range c))
    (hcU : ∀ t, c t ∈ U) (hcd : ∀ t, HasDerivAt c (f (c t)) t)
    {T ρ : ℝ} (hT : 0 < T) (hρ : 0 < ρ) {X : E → ℝ → E}
    (hX : IsBanachFlowOn f U (ball (c 0) ρ) T X) :
    ∃ A : ℝ → E →L[ℝ] E, Continuous A ∧ A 0 = ContinuousLinearMap.id ℝ E ∧
      (∀ t ∈ Icc (0 : ℝ) T, HasDerivAt A ((fderiv ℝ f (c t)).comp (A t)) t) ∧
      ∃ δ > 0, ∃ C > 0, ∀ h : E, ‖h‖ ≤ δ → ∀ t ∈ Icc (0 : ℝ) T,
        ‖X (c 0 + h) t - c t - A t h‖ ≤ C * ‖h‖ ^ 2 := by
  have hf1 : ContDiffOn ℝ 1 f U := hf.of_le (by
    change ((1 : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞)
    exact WithTop.coe_le_coe.mpr le_top)
  obtain ⟨A, hAc, hA0, hAd⟩ := exists_banachReference_fundamental_operators hU hf1 hc hcK hcU hT.le
  obtain ⟨δ, hδ, C, hC, hquad⟩ := banachFlow_uniform_quadratic_of_compact_reference
    hU hf hc hcK hcU hcd hT hρ hX hAc.continuousOn hA0 hAd
  exact ⟨A, hAc, hA0, hAd, δ, hδ, C, hC, hquad⟩

end Euler2D

end
