module

public import RequestProject.Euler.BanachFlowDerivative

/-! The actual variational solution is constructed and then identified
with the genuine initial-point derivative of the given actual flow. -/

@[expose] public section

noncomputable section

open Set Filter Topology Metric
open scoped NNReal ContDiff

namespace Euler2D

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem exists_banachFlow_initial_derivative
    {f : E → E} {U : Set E} (hU : IsOpen U) (hf : ContDiffOn ℝ 1 f U)
    {K : ℝ≥0} (hLip : LipschitzOnWith K f U) {a : E} {ρ T : ℝ}
    (hρ : 0 < ρ) (hT : 0 ≤ T) (hsmall : T ≤ banachFlowVariationalTime K)
    {X : E → ℝ → E} (hX : IsBanachFlowOn f U (ball a ρ) T X) :
    ∃ A : ℝ → E →L[ℝ] E, Continuous A ∧ A 0 = ContinuousLinearMap.id ℝ E ∧
      (∀ t ∈ Icc (0 : ℝ) T, HasDerivAt A ((fderiv ℝ f (X a t)).comp (A t)) t) ∧
      (∀ t ∈ Icc (0 : ℝ) T, HasFDerivAt (fun b => X b t) (A t) a) ∧
      ∀ t ∈ Icc (0 : ℝ) T, ‖A t‖ ≤ Real.exp ((K : ℝ) * t) := by
  have ha : a ∈ ball a ρ := mem_ball_self hρ
  let y : ℝ → E := fun t => X a (Set.projIcc (0 : ℝ) T hT t)
  have hyc : Continuous y :=
    (hX.continuous a ha).restrict.comp (continuous_projIcc (h := hT))
  have hym (t : ℝ) : y t ∈ U := hX.mem a ha _ (Set.projIcc _ _ _ t).property
  have hy (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) : y t = X a t := by
    dsimp only [y]
    rw [Set.projIcc_of_mem _ ht]
  let B : ℝ → E →L[ℝ] E := fun t => fderiv ℝ f (y t)
  have hDf : ContinuousOn (fderiv ℝ f) U :=
    (hf.fderiv_of_isOpen hU (m := 0) (by norm_num)).continuousOn
  have hBc : Continuous B := hDf.comp_continuous hyc hym
  have hB (t : ℝ) : ‖B t‖ ≤ K :=
    norm_fderiv_le_of_lipschitzOn ℝ (hU.mem_nhds (hym t)) hLip
  obtain ⟨A, hAc, hA0, hAd, hAn⟩ := exists_banachFlow_variational_curve hBc hB
  have hAd' (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) :
      HasDerivAt A ((fderiv ℝ f (X a t)).comp (A t)) t := by
    have hti : t ∈ Icc (-banachFlowVariationalTime K) (banachFlowVariationalTime K) :=
      ⟨by linarith [ht.1, banachFlowVariationalTime_pos K], ht.2.trans hsmall⟩
    simpa only [B, hy t ht] using hAd t hti
  refine ⟨A, hAc, hA0, hAd', ?_, ?_⟩
  · intro t ht
    exact hasFDerivAt_banachFlow_of_variational hU hf hLip hρ hT hX hAc.continuousOn hA0 hAd' ht
  · intro t ht
    exact hAn t ⟨ht.1, ht.2.trans hsmall⟩

theorem differentiableAt_banachFlow_initial
    {f : E → E} {U : Set E} (hU : IsOpen U) (hf : ContDiffOn ℝ 1 f U)
    {K : ℝ≥0} (hLip : LipschitzOnWith K f U) {a : E} {ρ T : ℝ}
    (hρ : 0 < ρ) (hT : 0 ≤ T) (hsmall : T ≤ banachFlowVariationalTime K)
    {X : E → ℝ → E} (hX : IsBanachFlowOn f U (ball a ρ) T X)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) : DifferentiableAt ℝ (fun b => X b t) a := by
  obtain ⟨_, _, _, _, hd, _⟩ := exists_banachFlow_initial_derivative hU hf hLip hρ hT hsmall hX
  exact (hd t ht).differentiableAt

end Euler2D

end
