module

public import RequestProject.Euler.LocalBanachContourODE
public import RequestProject.Euler.BanachFlowDerivative

/-! A common positive time and a genuine family of local integral
curves for all nearby initial points, with actual path membership. -/

@[expose] public section

noncomputable section

open Set Filter Topology Metric ODE
open scoped NNReal

namespace Euler2D

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem exists_local_banachFlow_of_lipschitzOn_nhds (F : E → E) (x : E)
    {K : ℝ≥0} {U : Set E} (hU : U ∈ 𝓝 x) (hLip : LipschitzOnWith K F U) :
    ∃ a > 0, ball x a ⊆ U ∧ ∃ T > 0, ∃ X : E → ℝ → E,
      IsBanachFlowOn F (ball x a) (ball x (a / 4)) T X := by
  classical
  obtain ⟨a, ha, hball⟩ := Metric.mem_nhds_iff.mp hU
  let L : ℝ := (K : ℝ) * a + ‖F x‖ + 1
  have hL : 0 < L := by dsimp only [L]; positivity
  have hb (y : E) (hy : y ∈ closedBall x (a / 2)) : ‖F y‖ ≤ L := by
    have hyU : y ∈ U := hball (closedBall_subset_ball (half_lt_self ha) hy)
    have hxU : x ∈ U := mem_of_mem_nhds hU
    have hd := hLip.dist_le_mul y hyU x hxU
    have hdist : dist y x ≤ a := (mem_closedBall.mp hy).trans (half_le_self ha.le)
    calc
      ‖F y‖ ≤ ‖F y - F x‖ + ‖F x‖ := norm_le_norm_sub_add _ _
      _ ≤ (K : ℝ) * a + ‖F x‖ := by
        rw [← dist_eq_norm]
        exact add_le_add (hd.trans (mul_le_mul_of_nonneg_left hdist K.coe_nonneg)) le_rfl
      _ ≤ L := le_add_of_nonneg_right zero_le_one
  let T : ℝ := a / (8 * L)
  have hT : 0 < T := div_pos ha (mul_pos (by norm_num) hL)
  let t₀ : Icc (-(2 * T)) (2 * T) := ⟨0, by constructor <;> linarith⟩
  have hpl : IsPicardLindelof (fun _ : ℝ => F) t₀ x
      (NNReal.mk (a / 2) (half_pos ha).le) (NNReal.mk (a / 4) (by positivity))
      (NNReal.mk L hL.le) K := by
    apply IsPicardLindelof.of_time_independent hb
      (hLip.mono ((closedBall_subset_ball (half_lt_self ha)).trans hball))
    change L * max (2 * T - 0) (0 - -(2 * T)) ≤ a / 2 - a / 4
    simp only [sub_zero, zero_sub, neg_neg, max_self]
    dsimp only [T]
    field_simp
    ring_nf
    exact le_rfl
  have hex (b : E) (hb : b ∈ closedBall x (a / 4)) :=
    FunSpace.exists_isFixedPt_next hpl hb
  choose β hβ using hex
  let X : E → ℝ → E := fun b =>
    if hb : b ∈ closedBall x (a / 4) then (β b hb).compProj else fun _ => b
  have hd (b : E) (hb : b ∈ closedBall x (a / 4))
      (t : ℝ) (ht : t ∈ Icc (-(2 * T)) (2 * T)) :
      HasDerivWithinAt (β b hb).compProj (F ((β b hb).compProj t))
        (Icc (-(2 * T)) (2 * T)) t := by
    apply hasDerivWithinAt_picard_Icc t₀.property hpl.continuousOn_uncurry
      (β b hb).continuous_compProj.continuousOn
      (fun _ _ => (β b hb).compProj_mem_closedBall hpl.mul_max_le) b ht |>.congr_of_mem _ ht
    intro t' ht'
    nth_rw 1 [← hβ b hb]
    rw [FunSpace.compProj_of_mem ht']
    exact FunSpace.next_apply hpl hb (β b hb) (t := ⟨t', ht'⟩)
  refine ⟨a, ha, hball, T, hT, X, ?_⟩
  constructor
  · intro b hb
    have hbc : b ∈ closedBall x (a / 4) := ball_subset_closedBall hb
    change (if hb : b ∈ closedBall x (a / 4) then (β b hb).compProj else fun _ => b) 0 = b
    rw [dif_pos hbc]
    change (β b hbc).compProj (t₀ : ℝ) = b
    rw [FunSpace.compProj_val, ← hβ b hbc]
    exact FunSpace.next_apply₀ hpl hbc (β b hbc)
  · intro b hb
    have hbc : b ∈ closedBall x (a / 4) := ball_subset_closedBall hb
    have he : X b = (β b hbc).compProj := dif_pos hbc
    rw [he]
    exact (β b hbc).continuous_compProj.continuousOn
  · intro b hb t ht
    have hbc : b ∈ closedBall x (a / 4) := ball_subset_closedBall hb
    have he : X b = (β b hbc).compProj := dif_pos hbc
    rw [he]
    exact (hd b hbc t (by constructor <;> linarith [ht.1, ht.2])).hasDerivAt
      (Icc_mem_nhds (by linarith [ht.1]) (by linarith [ht.2]))
  · intro b hb t _
    have hbc : b ∈ closedBall x (a / 4) := ball_subset_closedBall hb
    have he : X b = (β b hbc).compProj := dif_pos hbc
    rw [he]
    exact closedBall_subset_ball (half_lt_self ha)
      ((β b hbc).compProj_mem_closedBall hpl.mul_max_le)

end Euler2D

end
