module

public import RequestProject.Euler.ClusterLittleForcingNeighborhood
public import RequestProject.Euler.FinitePhaseForcedLocalFlow

/-! A genuine inner-cluster forcing on a finite family of active
interfaces, with one common neighborhood and one uniform state bound. -/

@[expose] public section

set_option maxHeartbeats 3500000

noncomputable section

open Complex Set MeasureTheory Filter Topology Metric
open scoped NNReal

namespace Euler2D

theorem exists_finiteClusterLittle_forcing_neighborhood
    {γ : ℝ≥0} {ι : Type*} [Fintype ι] (hγ1 : (γ : ℝ) ≤ 1)
    (u : ℝ → ℂ → ℝ) {a M M₄ : ℝ}
    (ha : 0 ≤ a) (hM₄ : 0 ≤ M₄) (hu : ∀ t, Integrable (u t))
    (hM : ∀ t y, |u t y| ≤ M)
    (hsu : ∀ t y, a < ‖y‖ → u t y = 0)
    (hmu : ∀ t, ∫ y, u t y = 0) (hyu : ∀ t y, u t (Complex.I * y) = u t y)
    (hmoment : ∀ t, (∫ y : ℂ, ‖y‖ ^ 4 * |u t y|) ≤ M₄)
    (hL1 : ∀ s, Tendsto (fun t => ∫ y, |u t y - u s y|) (𝓝 s) (𝓝 0))
    (d : ι → ℝ) (hd : ∀ i, 0 < d i) (hsep : ∀ i, 16 * a ≤ d i)
    (Z : ι → LittleContourSpace γ)
    (hZ : ∀ i x, d i ≤ ‖ContourC1Space.toBCF γ (Z i).val x‖) :
    ∃ E : ℝ → (ι → LittleContourSpace γ) → ι → LittleContourSpace γ,
      ∃ K : ℝ≥0, ∃ U : Set (ι → LittleContourSpace γ), U ∈ 𝓝 Z ∧
        (∀ t, LipschitzOnWith K (E t) U) ∧
        (∀ W ∈ U, Continuous (fun t => E t W)) ∧
        ∀ t W, W ∈ U → ∀ i θ,
          LittleContourSpace.lift γ (E t W i) θ = velocityC (u t) (LittleContourSpace.lift γ (W i) θ) := by
  classical
  have hex (i : ι) := exists_clusterLittle_continuous_forcing_neighborhood hγ1 u
    ha hM₄ hu hM hsu hmu hyu hmoment hL1 (hd i) (hsep i) (Z i) (hZ i)
  choose E K R hR hLip hc hE using hex
  let U : Set (ι → LittleContourSpace γ) := {W | ∀ i, W i ∈ ball (Z i) (R i)}
  have hUopen : IsOpen U := by
    have hi (i : ι) : IsOpen {W : ι → LittleContourSpace γ | W i ∈ ball (Z i) (R i)} :=
      isOpen_ball.preimage (continuous_apply i)
    simpa only [U, setOf_forall] using isOpen_iInter_of_finite hi
  have hU : U ∈ 𝓝 Z := hUopen.mem_nhds (fun i => mem_ball_self (hR i))
  let KB : ℝ≥0 := ∑ i, K i
  have hKB (i : ι) : K i ≤ KB :=
    Finset.single_le_sum (fun j _ => (zero_le : (0 : ℝ≥0) ≤ K j)) (Finset.mem_univ i)
  let EB : ℝ → (ι → LittleContourSpace γ) → ι → LittleContourSpace γ := fun t W i => E i t (W i)
  have hEB (t : ℝ) : LipschitzOnWith KB (EB t) U := by
    apply LipschitzOnWith.of_dist_le_mul
    intro W hW V hV
    apply (dist_pi_le_iff (mul_nonneg KB.2 dist_nonneg)).mpr
    intro i
    have hh := (hLip i t).dist_le_mul (W i) (hW i) (V i) (hV i)
    exact hh.trans ((mul_le_mul_of_nonneg_left (dist_le_pi_dist W V i) (K i).2).trans
      (mul_le_mul_of_nonneg_right (by exact_mod_cast hKB i) dist_nonneg))
  refine ⟨EB, KB, U, hU, hEB, ?_, ?_⟩
  · intro W hW
    exact continuous_pi_iff.mpr (fun i => hc i (W i) (hW i))
  · intro t W hW i θ
    exact hE i t (W i) (hW i) θ

end Euler2D

end
