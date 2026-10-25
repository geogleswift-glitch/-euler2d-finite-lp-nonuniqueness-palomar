module

public import RequestProject.Euler.BanachExistingForcedTrajectoryComparison

/-! The same reference-tube constants work on every provisional
subinterval of a fixed block. Thus the comparison can be applied at
an actual first-exit endpoint inside a block. -/

@[expose] public section

noncomputable section

open Set Metric
open scoped NNReal ContDiff

namespace Euler2D

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem dist_existing_forcedSubtrajectory_same_flow_le
    {f : E → E} {D U : Set E} (hD : IsOpen D) (hf : ContDiffOn ℝ 1 f D)
    (hUD : U ⊆ D) {T H r δ ε ρ : ℝ} {c : ℝ → E}
    (hc : ContinuousOn c (Icc (0 : ℝ) T))
    (hc' : ∀ t ∈ Icc (0 : ℝ) T, HasDerivAt c (f (c t)) t)
    {K : ℝ≥0} (hH : 0 < H) (hHT : H ≤ T)
    (hr : 0 < r) (hδ : 0 < δ) (hε : 0 ≤ ε)
    (htube : ∀ t ∈ Icc (0 : ℝ) T, closedBall (c t) r ⊆ U)
    (hLip : LipschitzOnWith K f U)
    (hsmall : δ * Real.exp (2 * (K : ℝ) * T) < r)
    {X : E → ℝ → E} (hX : IsBanachFlowOn f D (ball (c 0) ρ) T X)
    {b : E} (hb : b ∈ ball (c 0) (min ρ δ))
    {y p : ℝ → E} (hy0 : y 0 = b) (hyc : ContinuousOn y (Icc (0 : ℝ) H))
    (hyd : ∀ t ∈ Icc (0 : ℝ) H, HasDerivAt y (f (y t) + p t) t)
    (hym : ∀ t ∈ Icc (0 : ℝ) H, y t ∈ U)
    (hp : ∀ t ∈ Icc (0 : ℝ) H, ‖p t‖ ≤ ε) :
    ∀ t ∈ Icc (0 : ℝ) H, dist (y t) (X b t) ≤ ε * t * Real.exp ((K : ℝ) * t) := by
  have hsub : Icc (0 : ℝ) H ⊆ Icc (0 : ℝ) T := Icc_subset_Icc_right hHT
  have hXH : IsBanachFlowOn f D (ball (c 0) ρ) H X :=
    ⟨hX.initial, fun b hb => (hX.continuous b hb).mono hsub,
      fun b hb t ht => hX.hasDerivAt b hb t (hsub ht),
      fun b hb t ht => hX.mem b hb t (hsub ht)⟩
  have hsmallH : δ * Real.exp (2 * (K : ℝ) * H) < r :=
    (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_left hHT (by positivity))) hδ.le).trans_lt hsmall
  exact dist_existing_forcedTrajectory_same_flow_le hD hf hUD (hc.mono hsub)
    (fun t ht => hc' t (hsub ht)) hH hr hδ hε (fun t ht => htube t (hsub ht))
    hLip hsmallH hXH hb hy0 hyc hyd hym hp

end Euler2D

end
