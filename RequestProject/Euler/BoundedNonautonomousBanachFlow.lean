module

public import RequestProject.Euler.NonautonomousBanachFlowExistence

/-! Actual whole-interval Picard solutions for bounded globally Lipschitz
time-dependent fields. No smallness of the product of the Lipschitz
constant and the prescribed time interval is required. -/

@[expose] public section

set_option maxHeartbeats 2000000

noncomputable section

open Set Filter Topology Metric ODE
open scoped NNReal

namespace Euler2D

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem exists_bounded_nonautonomous_banachFlow
    (F : ℝ → E → E) (x : E) {K : ℝ≥0} {M R T : ℝ}
    (hM : 0 ≤ M) (hR : 0 < R) (hT : 0 < T)
    (hLip : ∀ t, LipschitzWith K (F t))
    (hcont : ∀ y, Continuous (fun t => F t y))
    (hbound : ∀ t y, ‖F t y‖ ≤ M) :
    ∃ X : E → ℝ → E,
      IsNonautonomousBanachFlowOn F univ (ball x R) T X := by
  classical
  let S : ℝ := T + 1
  have hS : 0 < S := by dsimp only [S]; positivity
  let a : ℝ := R + M * S + 1
  have ha : 0 < a := by dsimp only [a]; positivity
  let t₀ : Icc (-S) S := ⟨0, by constructor <;> linarith⟩
  have hpl : IsPicardLindelof F t₀ x
      (⟨a, ha.le⟩ : ℝ≥0) (⟨R, hR.le⟩ : ℝ≥0) (⟨M, hM⟩ : ℝ≥0) K := by
    refine ⟨fun t _ => (hLip t).lipschitzOnWith,
      fun y _ => (hcont y).continuousOn, fun t _ y _ => hbound t y, ?_⟩
    change M * max (S - 0) (0 - -S) ≤ a - R
    simp only [sub_zero, zero_sub, neg_neg, max_self]
    dsimp only [a]
    linarith
  have hex (b : E) (hb : b ∈ closedBall x R) := FunSpace.exists_isFixedPt_next hpl hb
  choose β hβ using hex
  let X : E → ℝ → E := fun b =>
    if hb : b ∈ closedBall x R then (β b hb).compProj else fun _ => b
  have hd (b : E) (hb : b ∈ closedBall x R)
      (t : ℝ) (ht : t ∈ Icc (-S) S) :
      HasDerivWithinAt (β b hb).compProj (F t ((β b hb).compProj t)) (Icc (-S) S) t := by
    apply hasDerivWithinAt_picard_Icc t₀.property hpl.continuousOn_uncurry
      (β b hb).continuous_compProj.continuousOn
      (fun _ _ => (β b hb).compProj_mem_closedBall hpl.mul_max_le) b ht |>.congr_of_mem _ ht
    intro t' ht'
    nth_rw 1 [← hβ b hb]
    rw [FunSpace.compProj_of_mem ht', FunSpace.next_apply]
  refine ⟨X, ?_⟩
  constructor
  · intro b hb
    have hbc : b ∈ closedBall x R := ball_subset_closedBall hb
    change (if hb : b ∈ closedBall x R then (β b hb).compProj else fun _ => b) 0 = b
    rw [dif_pos hbc]
    change (β b hbc).compProj (t₀ : ℝ) = b
    rw [FunSpace.compProj_val, ← hβ b hbc, FunSpace.next_apply₀]
  · intro b hb
    have hbc : b ∈ closedBall x R := ball_subset_closedBall hb
    have he : X b = (β b hbc).compProj := dif_pos hbc
    rw [he]
    exact (β b hbc).continuous_compProj.continuousOn
  · intro b hb t ht
    have hbc : b ∈ closedBall x R := ball_subset_closedBall hb
    have he : X b = (β b hbc).compProj := dif_pos hbc
    rw [he]
    have hti : t ∈ Ioo (-S) S := by dsimp only [S]; constructor <;> linarith [ht.1, ht.2]
    exact (hd b hbc t ⟨hti.1.le, hti.2.le⟩).hasDerivAt (Icc_mem_nhds hti.1 hti.2)
  · intro b hb t ht
    trivial

end Euler2D

end
