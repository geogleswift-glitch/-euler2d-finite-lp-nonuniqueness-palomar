module

public import RequestProject.Euler.ClusterContourStateStability

/-! The true inner-cluster velocity supplies the time-continuous,
uniformly locally Lipschitz Little-space forcing needed by Picard flow.
The candidate neighborhood stays outside the actual inner source. -/

@[expose] public section

set_option maxHeartbeats 3500000

noncomputable section

open Complex Set MeasureTheory Filter Topology Metric
open scoped NNReal

namespace Euler2D

theorem exists_clusterLittle_continuous_forcing_neighborhood
    {γ : ℝ≥0} (hγ1 : (γ : ℝ) ≤ 1)
    (u : ℝ → ℂ → ℝ) {a d M M₄ : ℝ}
    (ha : 0 ≤ a) (hM₄ : 0 ≤ M₄) (hu : ∀ t, Integrable (u t))
    (hM : ∀ t y, |u t y| ≤ M)
    (hsu : ∀ t y, a < ‖y‖ → u t y = 0)
    (hmu : ∀ t, ∫ y, u t y = 0) (hyu : ∀ t y, u t (Complex.I * y) = u t y)
    (hmoment : ∀ t, (∫ y : ℂ, ‖y‖ ^ 4 * |u t y|) ≤ M₄)
    (hL1 : ∀ s, Tendsto (fun t => ∫ y, |u t y - u s y|) (𝓝 s) (𝓝 0))
    (hd : 0 < d) (hsep : 16 * a ≤ d)
    (Z : LittleContourSpace γ) (hZ : ∀ x, d ≤ ‖ContourC1Space.toBCF γ Z.val x‖) :
    ∃ E : ℝ → LittleContourSpace γ → LittleContourSpace γ,
      ∃ K : ℝ≥0, ∃ R > 0,
        (∀ t, LipschitzOnWith K (E t) (ball Z R)) ∧
        (∀ W ∈ ball Z R, Continuous (fun t => E t W)) ∧
        ∀ t W, W ∈ ball Z R → ∀ θ,
          LittleContourSpace.lift γ (E t W) θ = velocityC (u t) (LittleContourSpace.lift γ W θ) := by
  classical
  let P : LittleContourSpace γ → Prop := fun W =>
    ∀ x, d / 2 ≤ ‖ContourC1Space.toBCF γ W.val x‖
  have hex (t : ℝ) (W : LittleContourSpace γ) (hW : P W) :
      ∃ Q : LittleContourSpace γ, ∀ θ,
        LittleContourSpace.lift γ Q θ = velocityC (u t) (LittleContourSpace.lift γ W θ) := by
    obtain ⟨Q, hQ, _⟩ := exists_clusterContourLittle hγ1 ha (hu t) (hsu t)
      (hmu t) (hyu t) (hmoment t) (half_pos hd) (by linarith) W hW
    exact ⟨Q, hQ⟩
  let E : ℝ → LittleContourSpace γ → LittleContourSpace γ := fun t W =>
    if hW : P W then (hex t W hW).choose else 0
  have hEQ (t : ℝ) (W : LittleContourSpace γ) (hW : P W) (θ : ℝ) :
      LittleContourSpace.lift γ (E t W) θ = velocityC (u t) (LittleContourSpace.lift γ W θ) := by
    dsimp only [E]
    rw [dif_pos hW]
    exact (hex t W hW).choose_spec θ
  obtain ⟨K, R₀, hR₀, hLip⟩ := exists_clusterContourLittle_uniform_lipschitz_neighborhood
    hγ1 ha hM₄ hu hsu hmu hyu hmoment hd hsep Z hZ E hEQ
  let R := min R₀ (d / 4)
  have hR : 0 < R := lt_min hR₀ (by positivity)
  have hsmall : ball Z R ⊆ ball Z R₀ := ball_subset_ball (min_le_left _ _)
  have htarget (W : LittleContourSpace γ) (hW : W ∈ ball Z R) : P W := by
    intro x
    have he : ‖W.val - Z.val‖ < R := by
      change ‖W - Z‖ < R
      exact mem_ball_iff_norm.mp hW
    have hev := (ContourC1Space.norm_eval_le (W.val - Z.val) x).trans_lt
      (he.trans_le (min_le_right _ _))
    change ‖ContourC1Space.toBCF γ W.val x - ContourC1Space.toBCF γ Z.val x‖ < d / 4 at hev
    have hn := norm_sub_norm_le (ContourC1Space.toBCF γ Z.val x) (ContourC1Space.toBCF γ W.val x)
    rw [norm_sub_rev] at hn
    have hz := hZ x
    change d / 2 ≤ _
    linarith
  refine ⟨E, K, R, hR, fun t => (hLip t).mono hsmall, ?_, ?_⟩
  · intro W hW
    apply continuous_iff_continuousAt.mpr
    intro s
    exact tendsto_clusterContourLittle_of_L1 hγ1 ha hu (hu s) hM (hM s)
      hsu (hsu s) hmu (hmu s) hyu (hyu s) (half_pos hd) (by linarith)
      W (htarget W hW) (fun t => E t W) (E s W)
      (fun t => hEQ t W (htarget W hW)) (hEQ s W (htarget W hW)) (hL1 s)
  · intro t W hW θ
    exact hEQ t W (htarget W hW) θ

end Euler2D

end
