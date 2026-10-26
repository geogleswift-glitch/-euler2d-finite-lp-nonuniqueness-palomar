module

public import RequestProject.Euler.FiniteClusterLittleForcingNeighborhood

/-! One fixed inner-source forcing on the whole separated target set.
Each admissible target has a uniform local state bound, so restarts need
not replace the forcing used by an earlier material trajectory. -/

@[expose] public section

set_option maxHeartbeats 3500000

noncomputable section

open Complex Set MeasureTheory Filter Topology Metric
open scoped NNReal

namespace Euler2D

theorem exists_clusterLittle_fixed_forcing_on_targets
    {γ : ℝ≥0} (hγ1 : (γ : ℝ) ≤ 1)
    (u : ℝ → ℂ → ℝ) {a d M M₄ : ℝ}
    (ha : 0 ≤ a) (hM₄ : 0 ≤ M₄) (hu : ∀ t, Integrable (u t))
    (hM : ∀ t y, |u t y| ≤ M)
    (hsu : ∀ t y, a < ‖y‖ → u t y = 0)
    (hmu : ∀ t, ∫ y, u t y = 0) (hyu : ∀ t y, u t (Complex.I * y) = u t y)
    (hmoment : ∀ t, (∫ y : ℂ, ‖y‖ ^ 4 * |u t y|) ≤ M₄)
    (hL1 : ∀ s, Tendsto (fun t => ∫ y, |u t y - u s y|) (𝓝 s) (𝓝 0))
    (hd : 0 < d) (hsep : 16 * a ≤ d) :
    ∃ E : ℝ → LittleContourSpace γ → LittleContourSpace γ,
      (∀ t W, (∀ x, d / 2 ≤ ‖ContourC1Space.toBCF γ W.val x‖) → ∀ θ,
        LittleContourSpace.lift γ (E t W) θ = velocityC (u t) (LittleContourSpace.lift γ W θ)) ∧
      (∀ W, (∀ x, d / 2 ≤ ‖ContourC1Space.toBCF γ W.val x‖) →
        Continuous (fun t => E t W)) ∧
      ∀ Z, (∀ x, d ≤ ‖ContourC1Space.toBCF γ Z.val x‖) →
        ∃ K : ℝ≥0, ∃ R > 0, ∀ t, LipschitzOnWith K (E t) (ball Z R) := by
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
  refine ⟨E, hEQ, ?_, ?_⟩
  · intro W hW
    apply continuous_iff_continuousAt.mpr
    intro s
    exact tendsto_clusterContourLittle_of_L1 hγ1 ha hu (hu s) hM (hM s)
      hsu (hsu s) hmu (hmu s) hyu (hyu s) (half_pos hd) (by linarith)
      W hW (fun t => E t W) (E s W) (fun t => hEQ t W hW) (hEQ s W hW) (hL1 s)
  · intro Z hZ
    exact exists_clusterContourLittle_uniform_lipschitz_neighborhood hγ1 ha hM₄
      hu hsu hmu hyu hmoment hd hsep Z hZ E hEQ

theorem exists_finiteClusterLittle_fixed_forcing_on_targets
    {γ : ℝ≥0} {ι : Type*} [Fintype ι] (hγ1 : (γ : ℝ) ≤ 1)
    (u : ℝ → ℂ → ℝ) {a M M₄ : ℝ}
    (ha : 0 ≤ a) (hM₄ : 0 ≤ M₄) (hu : ∀ t, Integrable (u t))
    (hM : ∀ t y, |u t y| ≤ M)
    (hsu : ∀ t y, a < ‖y‖ → u t y = 0)
    (hmu : ∀ t, ∫ y, u t y = 0) (hyu : ∀ t y, u t (Complex.I * y) = u t y)
    (hmoment : ∀ t, (∫ y : ℂ, ‖y‖ ^ 4 * |u t y|) ≤ M₄)
    (hL1 : ∀ s, Tendsto (fun t => ∫ y, |u t y - u s y|) (𝓝 s) (𝓝 0))
    (d : ι → ℝ) (hd : ∀ i, 0 < d i) (hsep : ∀ i, 16 * a ≤ d i) :
    ∃ E : ℝ → (ι → LittleContourSpace γ) → ι → LittleContourSpace γ,
      (∀ t W, (∀ i x, d i / 2 ≤ ‖ContourC1Space.toBCF γ (W i).val x‖) → ∀ i θ,
        LittleContourSpace.lift γ (E t W i) θ = velocityC (u t) (LittleContourSpace.lift γ (W i) θ)) ∧
      (∀ W, (∀ i x, d i / 2 ≤ ‖ContourC1Space.toBCF γ (W i).val x‖) →
        Continuous (fun t => E t W)) ∧
      ∀ Z, (∀ i x, d i ≤ ‖ContourC1Space.toBCF γ (Z i).val x‖) →
        ∃ K : ℝ≥0, ∃ U : Set (ι → LittleContourSpace γ), U ∈ 𝓝 Z ∧
          ∀ t, LipschitzOnWith K (E t) U := by
  classical
  have hex (i : ι) := exists_clusterLittle_fixed_forcing_on_targets hγ1 u
    ha hM₄ hu hM hsu hmu hyu hmoment hL1 (hd i) (hsep i)
  choose E hE hc hloc using hex
  let EB : ℝ → (ι → LittleContourSpace γ) → ι → LittleContourSpace γ := fun t W i => E i t (W i)
  refine ⟨EB, ?_, ?_, ?_⟩
  · intro t W hW i θ
    exact hE i t (W i) (hW i) θ
  · intro W hW
    exact continuous_pi_iff.mpr (fun i => hc i (W i) (hW i))
  · intro Z hZ
    choose K R hR hLip using fun i => hloc i (Z i) (hZ i)
    let U : Set (ι → LittleContourSpace γ) := {W | ∀ i, W i ∈ ball (Z i) (R i)}
    have hUopen : IsOpen U := by
      have hi (i : ι) : IsOpen {W : ι → LittleContourSpace γ | W i ∈ ball (Z i) (R i)} :=
        isOpen_ball.preimage (continuous_apply i)
      simpa only [U, setOf_forall] using isOpen_iInter_of_finite hi
    let KB : ℝ≥0 := ∑ i, K i
    have hKB (i : ι) : K i ≤ KB :=
      Finset.single_le_sum (fun j _ => (zero_le : (0 : ℝ≥0) ≤ K j)) (Finset.mem_univ i)
    refine ⟨KB, U, hUopen.mem_nhds (fun i => mem_ball_self (hR i)), ?_⟩
    intro t
    apply LipschitzOnWith.of_dist_le_mul
    intro W hW V hV
    apply (dist_pi_le_iff (mul_nonneg KB.2 dist_nonneg)).mpr
    intro i
    have hh := (hLip i t).dist_le_mul (W i) (hW i) (V i) (hV i)
    exact hh.trans ((mul_le_mul_of_nonneg_left (dist_le_pi_dist W V i) (K i).2).trans
      (mul_le_mul_of_nonneg_right (by exact_mod_cast hKB i) dist_nonneg))

end Euler2D

end
