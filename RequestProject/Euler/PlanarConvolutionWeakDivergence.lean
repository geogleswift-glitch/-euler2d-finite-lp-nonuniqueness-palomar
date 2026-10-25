module

public import RequestProject.Euler.PlanarWeakDivergenceMollification

/-! A genuine integrable planar kernel with zero distributional
divergence produces an actually incompressible convolution velocity.
All pointwise integrals and the two-variable Fubini step are proved. -/

@[expose] public section

set_option maxHeartbeats 2000000

noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal ContDiff Convolution

namespace Euler2D

def planarKernelVelocity (K : R2 → R2) (w : R2 → ℝ) (x : R2) : R2 :=
  ∫ y, w y • K (x - y)

theorem integrable_planarKernelVelocity_integrand
    {K : R2 → R2} {w : R2 → ℝ} {M : ℝ}
    (hK : Integrable K) (hw : Integrable w) (hM : ∀ y, ‖w y‖ ≤ M) (x : R2) :
    Integrable (fun y => w y • K (x - y)) := by
  exact (hK.comp_sub_left x).bdd_smul M hw.aestronglyMeasurable (ae_of_all _ hM)

theorem planarWeakDivergenceFree_translate_kernel
    {K : R2 → R2} (hK : IsPlanarWeaklyDivergenceFree K)
    {ψ : R2 → ℝ} (hψ : ContDiff ℝ 1 ψ) (hs : HasCompactSupport ψ) (y : R2) :
    (∫ x, ∑ i : Fin 2, K (x - y) i * pd i ψ x) = 0 := by
  let φ : R2 → ℝ := fun z => ψ (z + y)
  have hφ : ContDiff ℝ 1 φ := hψ.comp (contDiff_id.add contDiff_const)
  have hsφ : HasCompactSupport φ := hs.comp_homeomorph (Homeomorph.addRight y)
  have hpd (i : Fin 2) (z : R2) : pd i φ z = pd i ψ (z + y) := by
    unfold pd
    change (fderiv ℝ (fun z => ψ (z + y)) z) _ = _
    rw [fderiv_comp_add_right]
  calc
    _ = ∫ z, ∑ i : Fin 2, K z i * pd i ψ (z + y) := by
      simpa only [add_sub_cancel_right] using
        (integral_add_right_eq_self (μ := volume) (fun x => ∑ i : Fin 2, K (x - y) i * pd i ψ x) y).symm
    _ = 0 := by simpa only [hpd] using hK φ hφ hsφ

theorem isPlanarWeaklyDivergenceFree_planarKernelVelocity
    {K : R2 → R2} {w : R2 → ℝ} {M : ℝ}
    (hK : Integrable K) (hKdiv : IsPlanarWeaklyDivergenceFree K)
    (hw : Integrable w) (hM : ∀ y, ‖w y‖ ≤ M) :
    IsPlanarWeaklyDivergenceFree (planarKernelVelocity K w) := by
  intro ψ hψ hs
  have hDcont : Continuous (fderiv ℝ ψ) := hψ.continuous_fderiv (by norm_num)
  obtain ⟨D, hD⟩ := (hs.fderiv ℝ).exists_bound_of_continuous hDcont
  have hp (i : Fin 2) : Continuous (pd i ψ) := hDcont.clm_apply continuous_const
  have hpbound (i : Fin 2) (x : R2) : ‖pd i ψ x‖ ≤ D := by
    calc
      _ ≤ ‖fderiv ℝ ψ x‖ * ‖EuclideanSpace.single i (1 : ℝ)‖ := (fderiv ℝ ψ x).le_opNorm _
      _ = ‖fderiv ℝ ψ x‖ := by simp
      _ ≤ D := hD x
  let F : R2 → R2 → ℝ := fun x y => ∑ i : Fin 2, w y * K (x - y) i * pd i ψ x
  have hbase : Integrable (fun p : R2 × R2 => w p.2 • K (p.1 - p.2)) (volume.prod volume) :=
    hw.convolution_integrand (ContinuousLinearMap.lsmul ℝ ℝ) hK
  have hpair (i : Fin 2) : Integrable
      (fun p : R2 × R2 => w p.2 * K (p.1 - p.2) i * pd i ψ p.1) (volume.prod volume) := by
    have hi := (EuclideanSpace.proj i : R2 →L[ℝ] ℝ).integrable_comp hbase
    exact hi.mul_bdd ((hp i).measurable.comp measurable_fst).aestronglyMeasurable
      (ae_of_all _ (fun p => hpbound i p.1))
  have hF : Integrable (Function.uncurry F) (volume.prod volume) :=
    integrable_finset_sum _ (fun i _ => hpair i)
  have hinner (x : R2) : (∑ i : Fin 2, planarKernelVelocity K w x i * pd i ψ x) = ∫ y, F x y := by
    have hi := integrable_planarKernelVelocity_integrand hK hw hM x
    have hcoord (i : Fin 2) : planarKernelVelocity K w x i = ∫ y, w y * K (x - y) i :=
      ((EuclideanSpace.proj i : R2 →L[ℝ] ℝ).integral_comp_comm hi).symm
    have hj (i : Fin 2) : Integrable (fun y => w y * K (x - y) i) :=
      (EuclideanSpace.proj i : R2 →L[ℝ] ℝ).integrable_comp hi
    dsimp only [F]
    rw [integral_finset_sum _ (fun i _ => (hj i).mul_const (pd i ψ x))]
    apply Finset.sum_congr rfl
    intro i _
    rw [hcoord i, integral_mul_const]
  calc
    _ = ∫ x, ∫ y, F x y := by simp_rw [hinner]
    _ = ∫ y, ∫ x, F x y := integral_integral_swap hF
    _ = 0 := by
      have hout (y : R2) : (∫ x, F x y) = 0 := by
        calc
          _ = ∫ x, w y * (∑ i : Fin 2, K (x - y) i * pd i ψ x) := by
            congr 1
            funext x
            simp only [F, Finset.mul_sum, mul_assoc]
          _ = 0 := by rw [integral_const_mul,
            planarWeakDivergenceFree_translate_kernel hKdiv hψ hs y, mul_zero]
      simp_rw [hout, integral_zero]

end Euler2D

end
