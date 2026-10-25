module

public import RequestProject.Euler.PlanarWeakDivergenceMollification

/-! True pointwise limits of uniformly bounded incompressible
planar fields preserve the original compact-test divergence identity. -/

@[expose] public section

set_option maxHeartbeats 1500000

noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal ContDiff

namespace Euler2D

theorem isPlanarWeaklyDivergenceFree_of_bounded_pointwise_limit
    {u : ℕ → R2 → R2} {v : R2 → R2} {M : ℝ}
    (hu : ∀ n, AEStronglyMeasurable (u n) volume)
    (hv : AEStronglyMeasurable v volume)
    (hM : ∀ n x, ‖u n x‖ ≤ M)
    (hlim : ∀ x, Tendsto (fun n => u n x) atTop (𝓝 (v x)))
    (hdiv : ∀ n, IsPlanarWeaklyDivergenceFree (u n)) : IsPlanarWeaklyDivergenceFree v := by
  intro ψ hψ hs
  have hgrad : Integrable (fderiv ℝ ψ) :=
    (hψ.continuous_fderiv (by norm_num)).integrable_of_hasCompactSupport (hs.fderiv ℝ)
  have hpd (i : Fin 2) : Integrable (pd i ψ) :=
    (ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.single i (1 : ℝ))).integrable_comp hgrad
  have hvM (x : R2) : ‖v x‖ ≤ M := le_of_tendsto (hlim x).norm (Eventually.of_forall fun n => hM n x)
  have hcoord (w : R2) (i : Fin 2) : ‖w i‖ ≤ ‖w‖ := by
    simpa only [Real.norm_eq_abs] using abs_coord_le w i
  have hi (w : R2 → R2) (hw : AEStronglyMeasurable w volume)
      (hb : ∀ x, ‖w x‖ ≤ M) (i : Fin 2) : Integrable (fun x => w x i * pd i ψ x) := by
    have hm := (EuclideanSpace.proj i : R2 →L[ℝ] ℝ).continuous.comp_aestronglyMeasurable hw
    exact (hpd i).bdd_mul hm (ae_of_all _ (fun x =>
      (hcoord (w x) i).trans (hb x)))
  have ht (i : Fin 2) : Tendsto (fun n => ∫ x, u n x i * pd i ψ x) atTop
      (𝓝 (∫ x, v x i * pd i ψ x)) := by
    have hdom (n : ℕ) : ∀ᵐ x, ‖u n x i * pd i ψ x‖ ≤ M * ‖pd i ψ x‖ := ae_of_all _ (fun x => by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right ((hcoord (u n x) i).trans (hM n x)) (norm_nonneg _))
    exact tendsto_integral_of_dominated_convergence (fun x => M * ‖pd i ψ x‖)
      (fun n => (hi (u n) (hu n) (hM n) i).aestronglyMeasurable) ((hpd i).norm.const_mul M) hdom
      (ae_of_all _ (fun x =>
        (((EuclideanSpace.proj i : R2 →L[ℝ] ℝ).continuous.tendsto (v x)).comp (hlim x)).mul_const (pd i ψ x))
      )
  have hzero (n : ℕ) : (∫ x, u n x 0 * pd 0 ψ x) + (∫ x, u n x 1 * pd 1 ψ x) = 0 := by
    have hn := hdiv n ψ hψ hs
    change (∫ x, ∑ i : Fin 2, u n x i * pd i ψ x) = 0 at hn
    simp only [Fin.sum_univ_two] at hn
    rw [integral_add (hi (u n) (hu n) (hM n) 0) (hi (u n) (hu n) (hM n) 1)] at hn
    exact hn
  have hzlim : Tendsto (fun n => (∫ x, u n x 0 * pd 0 ψ x) + (∫ x, u n x 1 * pd 1 ψ x)) atTop (𝓝 0) := by
    have he : (fun n => (∫ x, u n x 0 * pd 0 ψ x) + (∫ x, u n x 1 * pd 1 ψ x)) =
        (fun _ : ℕ => (0 : ℝ)) := funext hzero
    rw [he]
    exact tendsto_const_nhds
  change (∫ x, ∑ i : Fin 2, v x i * pd i ψ x) = 0
  simp only [Fin.sum_univ_two]
  rw [integral_add (hi v hv hvM 0) (hi v hv hvM 1)]
  exact tendsto_nhds_unique ((ht 0).add (ht 1)) hzlim

end Euler2D

end
