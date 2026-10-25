module

public import RequestProject.Euler.ClusterContourSourceStability
public import RequestProject.Euler.AnalyticContourCompositionBounds

/-! Uniform local dependence on candidate contours in an annular target
neighborhood. No Lipschitz bound across the rough inner source is used. -/

@[expose] public section

set_option maxHeartbeats 3500000

noncomputable section

open Complex ComplexConjugate Set MeasureTheory Filter Topology Metric
open scoped NNReal

namespace Euler2D

theorem exists_clusterContourLittle_uniform_lipschitz_neighborhood
    {γ : ℝ≥0} (hγ1 : (γ : ℝ) ≤ 1) {α : Type*}
    {u : α → ℂ → ℝ} {a d M₄ : ℝ}
    (ha : 0 ≤ a) (hM : 0 ≤ M₄) (hu : ∀ i, Integrable (u i))
    (hsu : ∀ i y, a < ‖y‖ → u i y = 0)
    (hmu : ∀ i, ∫ y, u i y = 0) (hyu : ∀ i y, u i (I * y) = u i y)
    (hM₄ : ∀ i, (∫ y : ℂ, ‖y‖ ^ 4 * |u i y|) ≤ M₄)
    (hd : 0 < d) (hsep : 16 * a ≤ d)
    (Z : LittleContourSpace γ) (hZ : ∀ x, d ≤ ‖ContourC1Space.toBCF γ Z.val x‖)
    (Q : α → LittleContourSpace γ → LittleContourSpace γ)
    (hQ : ∀ i W, (∀ x, d / 2 ≤ ‖ContourC1Space.toBCF γ W.val x‖) →
      ∀ θ, LittleContourSpace.lift γ (Q i W) θ = velocityC (u i) (LittleContourSpace.lift γ W θ)) :
    ∃ K : ℝ≥0, ∃ R > 0, ∀ i, LipschitzOnWith K (Q i) (ball Z R) := by
  let U : Set ℂ := {z | d / 4 < ‖z‖}
  have hF (i : α) : AnalyticOnNhd ℂ (fun z => conj (velocityC (u i) z)) U :=
    (analyticOnNhd_conj_velocityC (hu i) (hsu i)).mono (fun z hz => by
      change a < ‖z‖
      change d / 4 < ‖z‖ at hz
      linarith)
  let B : ℕ → ℝ := clusterDerivativeBound M₄ (d / 4)
  have hB (m : ℕ) : 0 ≤ B m := clusterDerivativeBound_nonneg hM (by positivity) m
  have hb (i : α) (m : ℕ) (z : ℂ) (hz : z ∈ U) :
      ‖iteratedDeriv m (fun x => conj (velocityC (u i) x)) z‖ ≤ B m :=
    cluster_iteratedDeriv_bound_on_target ha (hu i) (hsu i) (hmu i) (hyu i)
      (hM₄ i) (by positivity) (by linarith) (le_of_lt hz) m
  have h₁ (i : α) : ∀ z ∈ U,
      ‖deriv (fun x => conj (velocityC (u i) x)) z‖ ≤ B 1 := by
    simpa only [iteratedDeriv_one] using hb i 1
  have h₂ (i : α) : ∀ z ∈ U,
      ‖deriv (deriv (fun x => conj (velocityC (u i) x))) z‖ ≤ B 2 := by
    simpa only [iteratedDeriv_succ, iteratedDeriv_zero] using hb i 2
  have h₃ (i : α) : ∀ z ∈ U,
      ‖deriv (deriv (deriv (fun x => conj (velocityC (u i) x)))) z‖ ≤ B 3 := by
    simpa only [iteratedDeriv_succ, iteratedDeriv_zero] using hb i 3
  let R := min (d / 4) 1
  have hR : 0 < R := lt_min (by positivity) zero_lt_one
  let L := ‖Z‖ + 1
  have hL : 0 ≤ L := by dsimp only [L]; positivity
  let K := analyticCompositionShapeConstant (γ : ℝ) L (B 1) (B 2) (B 3)
  have hK : 0 ≤ K := by
    have hB1 := hB 1
    have hB2 := hB 2
    have hB3 := hB 3
    dsimp only [K, analyticCompositionShapeConstant]
    positivity
  have hval {W : LittleContourSpace γ} (hW : W ∈ ball Z R) (x : ContourCircle) :
      ‖ContourC1Space.toBCF γ W.val x - ContourC1Space.toBCF γ Z.val x‖ < d / 4 := by
    exact (ContourC1Space.norm_eval_le (W.val - Z.val) x).trans_lt
      ((show ‖W.val - Z.val‖ < R by simpa only [dist_eq_norm] using mem_ball.mp hW).trans_le
        (min_le_left _ _))
  have htarget {W : LittleContourSpace γ} (hW : W ∈ ball Z R) (x : ContourCircle) :
      d / 2 ≤ ‖ContourC1Space.toBCF γ W.val x‖ := by
    have he := hval hW x
    have hn := norm_sub_norm_le (ContourC1Space.toBCF γ Z.val x) (ContourC1Space.toBCF γ W.val x)
    rw [norm_sub_rev] at hn
    have hz := hZ x
    linarith
  have htargetU {W : LittleContourSpace γ} (hW : W ∈ ball Z R) (x : ContourCircle) :
      ContourC1Space.toBCF γ W.val x ∈ U := by
    have hh := htarget hW x
    change d / 4 < _
    linarith
  have hlength {W : LittleContourSpace γ} (hW : W ∈ ball Z R) : ‖W.val‖ ≤ L := by
    have hn := norm_le_norm_sub_add W.val Z.val
    have he : ‖W.val - Z.val‖ < R := by simpa only [dist_eq_norm] using mem_ball.mp hW
    have hR1 : R ≤ 1 := min_le_right _ _
    change ‖W.val‖ ≤ ‖Z.val‖ + 1
    linarith
  refine ⟨⟨K, hK⟩, R, hR, ?_⟩
  intro i
  apply LipschitzOnWith.of_dist_le_mul
  intro W hW V hV
  let AW := analyticContourComposition hγ1 (hF i) W.val (htargetU hW)
    (hB 2) (fun x => h₂ i _ (htargetU hW x))
  let AV := analyticContourComposition hγ1 (hF i) V.val (htargetU hV)
    (hB 2) (fun x => h₂ i _ (htargetU hV x))
  have heW : (Q i W).val = contourC1Conjugate AW := by
    apply ContourC1Space.ext
    intro x
    obtain ⟨θ, rfl⟩ := QuotientAddGroup.mk_surjective x
    change LittleContourSpace.lift γ (Q i W) θ = ContourC1Space.lift γ (contourC1Conjugate AW) θ
    rw [hQ i W (htarget hW) θ, lift_contourC1Conjugate]
    exact (conj_conj _).symm
  have heV : (Q i V).val = contourC1Conjugate AV := by
    apply ContourC1Space.ext
    intro x
    obtain ⟨θ, rfl⟩ := QuotientAddGroup.mk_surjective x
    change LittleContourSpace.lift γ (Q i V) θ = ContourC1Space.lift γ (contourC1Conjugate AV) θ
    rw [hQ i V (htarget hV) θ, lift_contourC1Conjugate]
    exact (conj_conj _).symm
  have he : (Q i W).val - (Q i V).val = contourC1Conjugate (AW - AV) := by
    rw [heW, heV]
    exact (map_sub (contourC1ConjugateCLM γ) AW AV).symm
  have hseg (x : ContourCircle) : segment ℝ (ContourC1Space.toBCF γ W.val x)
      (ContourC1Space.toBCF γ V.val x) ⊆ U := by
    have hball : ball (ContourC1Space.toBCF γ Z.val x) (d / 4) ⊆ U := by
      intro z hz
      have he : ‖z - ContourC1Space.toBCF γ Z.val x‖ < d / 4 := mem_ball_iff_norm.mp hz
      have hn := norm_sub_norm_le (ContourC1Space.toBCF γ Z.val x) z
      rw [norm_sub_rev] at hn
      have hz0 := hZ x
      change d / 4 < ‖z‖
      linarith
    exact ((convex_ball _ _).segment_subset
      (mem_ball_iff_norm.mpr (hval hW x)) (mem_ball_iff_norm.mpr (hval hV x))).trans hball
  rw [dist_eq_norm, dist_eq_norm]
  change ‖(Q i W).val - (Q i V).val‖ ≤ K * ‖W.val - V.val‖
  rw [he]
  exact (norm_contourC1Conjugate_le (AW - AV)).trans
    (norm_analyticContourComposition_sub_le hγ1 (hF i) W.val V.val (htargetU hW) (htargetU hV)
      (hB 1) (hB 2) (hB 3) hL (hlength hW) (hlength hV) (h₁ i) (h₂ i) (h₃ i) hseg)

end Euler2D

end
