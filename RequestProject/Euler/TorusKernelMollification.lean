module

public import RequestProject.Euler.TorusKernelVelocityRegularity
public import RequestProject.Euler.SpatialC1ParticleFlow
public import RequestProject.Euler.ContinuousPeriodicEquality
public import Mathlib.Analysis.Calculus.BumpFunction.Normed
public import Mathlib.Analysis.Calculus.ContDiff.Convolution

/-!
# Actual normalized mollifiers and smooth periodic velocity kernels
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology Metric
open scoped ContDiff NNReal ENNReal Convolution

namespace Euler2D

theorem locallyIntegrable_torusPeriodize {F : Type*} [NormedAddCommGroup F]
    {f : R2 → F} (hf : Integrable f volume)
    (hzero : ∀ y, 1 ≤ ‖y - torusCenter‖ → f y = 0) :
    LocallyIntegrable (torusPeriodize f) volume := by
  classical
  intro x
  obtain ⟨N, hN⟩ := periodize_local_index_bound hzero x
  let K := Finset.Icc (fun _ : Fin 2 => -(N : ℤ)) (fun _ => (N : ℤ))
  have hI : Integrable (fun y => ∑ k ∈ K, f (y + torusLatticeShift k)) volume := by
    apply integrable_finset_sum
    intro k hk
    exact (measurePreserving_add_right volume (torusLatticeShift k)).integrable_comp_of_integrable hf
  refine ⟨ball x 1, ball_mem_nhds x (by norm_num), hI.integrableOn.congr ?_⟩
  filter_upwards [ae_restrict_mem measurableSet_ball] with y hy
  symm
  apply tsum_eq_sum
  intro k hk
  by_contra hn
  exact hk (hN y hy k hn)

theorem locallyIntegrable_torusBiotSavartKernel : LocallyIntegrable torusBiotSavartKernel volume := by
  have hlocal : LocallyIntegrable periodicLocalKernel volume :=
    locallyIntegrable_torusPeriodize
      ((measurePreserving_sub_right volume torusCenter).integrable_comp_of_integrable
        integrable_localPlanarKernel)
      (fun x hx => localPlanarKernel_eq_zero_of_one_le_norm hx)
  exact hlocal.add (contDiff_perpGradient torusGreenCorrection_smooth).continuous.locallyIntegrable

def kernelMollifierBump (ε : ℝ) (hε : 0 < ε) : ContDiffBump torusCenter where
  rIn := ε / 2
  rOut := ε
  rIn_pos := half_pos hε
  rIn_lt_rOut := half_lt_self hε

def rawKernelMollifier (ε : ℝ) (hε : 0 < ε) : R2 → ℝ :=
  (kernelMollifierBump ε hε).normed volume

def torusKernelMollifier (ε : ℝ) (hε : 0 < ε) : R2 → ℝ :=
  torusPeriodize (rawKernelMollifier ε hε)

lemma rawKernelMollifier_nonneg (ε : ℝ) (hε : 0 < ε) (x : R2) :
    0 ≤ rawKernelMollifier ε hε x := (kernelMollifierBump ε hε).nonneg_normed (μ := volume) x

lemma rawKernelMollifier_smooth (ε : ℝ) (hε : 0 < ε) :
    ContDiff ℝ ∞ (rawKernelMollifier ε hε) := (kernelMollifierBump ε hε).contDiff_normed

lemma rawKernelMollifier_compact (ε : ℝ) (hε : 0 < ε) :
    HasCompactSupport (rawKernelMollifier ε hε) :=
  (kernelMollifierBump ε hε).hasCompactSupport_normed (μ := volume)

lemma rawKernelMollifier_integral (ε : ℝ) (hε : 0 < ε) :
    (∫ x : R2, rawKernelMollifier ε hε x) = 1 :=
  (kernelMollifierBump ε hε).integral_normed (μ := volume)

lemma rawKernelMollifier_eq_zero {ε : ℝ} (hε : 0 < ε) {x : R2}
    (hx : ε ≤ ‖x - torusCenter‖) : rawKernelMollifier ε hε x = 0 := by
  unfold rawKernelMollifier ContDiffBump.normed
  rw [(kernelMollifierBump ε hε).zero_of_le_dist
    (by simpa only [dist_eq_norm, kernelMollifierBump] using hx), zero_div]

lemma rawKernelMollifier_zero_of_one_le {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (x : R2) (hx : 1 ≤ ‖x - torusCenter‖) : rawKernelMollifier ε hε x = 0 :=
  rawKernelMollifier_eq_zero hε (hε1.trans hx)

lemma torusKernelMollifier_eq_on_box {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    {x : R2} (hx : x ∈ torusBox) : torusKernelMollifier ε hε x = rawKernelMollifier ε hε x :=
  torusPeriodize_eq_on_box (rawKernelMollifier_zero_of_one_le hε hε1) hx

lemma torusKernelMollifier_test {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    IsScalarTest (torusKernelMollifier ε hε) :=
  isScalarTest_torusPeriodize (rawKernelMollifier_smooth ε hε)
    (rawKernelMollifier_zero_of_one_le hε hε1)

lemma torusKernelMollifier_nonneg (ε : ℝ) (hε : 0 < ε) (x : R2) :
    0 ≤ torusKernelMollifier ε hε x :=
  tsum_nonneg (fun k => rawKernelMollifier_nonneg ε hε (x + torusLatticeShift k))

lemma torusKernelMollifier_integral {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    (∫ x in torusBox, torusKernelMollifier ε hε x) = 1 := by
  calc
    _ = ∫ x in torusBox, rawKernelMollifier ε hε x :=
      setIntegral_congr_fun measurableSet_torusBox (fun x hx => torusKernelMollifier_eq_on_box hε hε1 hx)
    _ = ∫ x : R2, rawKernelMollifier ε hε x := by
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro x hx
      exact rawKernelMollifier_zero_of_one_le hε hε1 x
        (le_of_not_gt (fun hn => hx (norm_sub_center_lt_one_mem_box hn)))
    _ = 1 := rawKernelMollifier_integral ε hε

lemma torusKernelMollifier_eq_zero_on_box {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    {x : R2} (hx : x ∈ torusBox) (hxe : ε ≤ ‖x - torusCenter‖) :
    torusKernelMollifier ε hε x = 0 := by
  rw [torusKernelMollifier_eq_on_box hε hε1 hx]
  exact rawKernelMollifier_eq_zero hε hxe

def regularizedTorusKernel (ε : ℝ) (hε : 0 < ε) : R2 → R2 :=
  torusKernelVelocity (torusKernelMollifier ε hε)

theorem regularizedTorusKernel_eq_convolution {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (x : R2) :
    regularizedTorusKernel ε hε x =
      (rawKernelMollifier ε hε ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
        torusBiotSavartKernel) (x + torusCenter) := by
  change (∫ z in torusBox, torusKernelMollifier ε hε z •
    torusBiotSavartKernel (x - z + torusCenter)) = _
  calc
    _ = ∫ z in torusBox, rawKernelMollifier ε hε z •
        torusBiotSavartKernel (x - z + torusCenter) := by
      apply setIntegral_congr_fun measurableSet_torusBox
      intro z hz
      dsimp only
      rw [torusKernelMollifier_eq_on_box hε hε1 hz]
    _ = ∫ z : R2, rawKernelMollifier ε hε z •
        torusBiotSavartKernel (x - z + torusCenter) := by
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro z hz
      rw [rawKernelMollifier_zero_of_one_le hε hε1 z
        (le_of_not_gt (fun hn => hz (norm_sub_center_lt_one_mem_box hn))), zero_smul]
    _ = _ := by
      unfold convolution
      apply integral_congr_ae
      exact Eventually.of_forall (fun z => by
        simp only [ContinuousLinearMap.lsmul_apply]
        congr 2
        abel)

theorem regularizedTorusKernel_smooth {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ContDiff ℝ ∞ (regularizedTorusKernel ε hε) := by
  have hc : ContDiff ℝ ∞ (rawKernelMollifier ε hε ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
      torusBiotSavartKernel) :=
    (rawKernelMollifier_compact ε hε).contDiff_convolution_left _
      (rawKernelMollifier_smooth ε hε) locallyIntegrable_torusBiotSavartKernel
  have heq : regularizedTorusKernel ε hε = fun x =>
      (rawKernelMollifier ε hε ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
        torusBiotSavartKernel) (x + torusCenter) :=
    funext (regularizedTorusKernel_eq_convolution hε hε1)
  rw [heq]
  exact hc.comp (contDiff_id.add contDiff_const)

theorem regularizedTorusKernel_periodic (ε : ℝ) (hε : 0 < ε) :
    IsTorusPeriodic (regularizedTorusKernel ε hε) := isTorusPeriodic_torusKernelVelocity _

theorem pointwise_divergence_zero_of_smooth_divFree {u : R2 → R2}
    (huc : ContDiff ℝ ∞ u) (hup : IsTorusPeriodic u) (hu : DivFree u) (x : R2) :
    pd 0 u x 0 + pd 1 u x 1 = 0 := by
  have hc (i : Fin 2) : ContDiff ℝ ∞ (fun y => u y i) :=
    (EuclideanSpace.proj i : R2 →L[ℝ] ℝ).contDiff.comp huc
  have hp (i : Fin 2) : IsTorusPeriodic (fun y => u y i) :=
    fun y j => congrArg (fun z : R2 => z i) (hup y j)
  let d : R2 → ℝ := fun y => pd 0 (fun z => u z 0) y + pd 1 (fun z => u z 1) y
  have hdc : ContDiff ℝ ∞ d := (contDiff_pd_infty (hc 0) 0).add (contDiff_pd_infty (hc 1) 1)
  have hdp : IsTorusPeriodic d := by
    intro y j
    dsimp only [d]
    rw [isTorusPeriodic_pd (hp 0) 0 y j, isTorusPeriodic_pd (hp 1) 1 y j]
  have hdtest := hu d ⟨hdc, hdp⟩
  have hi (i : Fin 2) : Integrable (fun y => u y i * pd i d y) μT :=
    integrable_torusBox_of_continuous ((hc i).continuous.mul (contDiff_pd_infty hdc i).continuous)
  have hj (i : Fin 2) : Integrable (fun y => pd i (fun z => u z i) y * d y) μT :=
    integrable_torusBox_of_continuous ((contDiff_pd_infty (hc i) i).continuous.mul hdc.continuous)
  simp only [Fin.sum_univ_two] at hdtest
  rw [integral_add (hi 0) (hi 1),
    integral_mul_pd_periodic _ d ((hc 0).of_le (by simp)) (hdc.of_le (by simp)) (hp 0) hdp 0,
    integral_mul_pd_periodic _ d ((hc 1).of_le (by simp)) (hdc.of_le (by simp)) (hp 1) hdp 1] at hdtest
  have hsq : (∫ y in torusBox, d y ^ 2) = 0 := by
    have heq : (∫ y in torusBox, d y ^ 2) =
        (∫ y in torusBox, pd 0 (fun z => u z 0) y * d y) +
          ∫ y in torusBox, pd 1 (fun z => u z 1) y * d y := by
      rw [← integral_add (hj 0) (hj 1)]
      apply integral_congr_ae
      exact Eventually.of_forall (fun y => by dsimp only [d]; ring)
    linarith
  have hdae : d =ᵐ[μT] (fun _ => 0) := by
    have hsquare := (integral_eq_zero_iff_of_nonneg (fun y => sq_nonneg (d y))
      (integrable_torusBox_of_continuous (hdc.continuous.pow 2))).mp hsq
    filter_upwards [hsquare] with y hy
    exact sq_eq_zero_iff.mp hy
  have heq : d = (fun _ => 0) := hdc.continuous.eq_of_periodic_ae_eq continuous_const hdp
    (fun _ _ => rfl) hdae
  have hdiff := huc.differentiable (by simp)
  rw [← torus_pd_component u x (hdiff x) 0 0, ← torus_pd_component u x (hdiff x) 1 1]
  exact congrFun heq x

theorem regularizedTorusKernel_divFree {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    DivFree (regularizedTorusKernel ε hε) := by
  have hc := (torusKernelMollifier_test hε hε1).1.continuous
  obtain ⟨C, hC⟩ := bound_on_box hc
  apply divFree_torusKernelVelocity hc.aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_torusBox] with x hx
  simpa only [Real.norm_eq_abs] using hC x hx

theorem regularizedTorusKernel_divergence {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (x : R2) :
    pd 0 (regularizedTorusKernel ε hε) x 0 + pd 1 (regularizedTorusKernel ε hε) x 1 = 0 :=
  pointwise_divergence_zero_of_smooth_divFree (regularizedTorusKernel_smooth hε hε1)
    (regularizedTorusKernel_periodic ε hε) (regularizedTorusKernel_divFree hε hε1) x

theorem regularizedTorusKernel_bounds {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ C : ℝ≥0, (∀ x, ‖regularizedTorusKernel ε hε x‖ ≤ C) ∧
      (∀ x, ‖fderiv ℝ (regularizedTorusKernel ε hε) x‖ ≤ C) ∧
      LipschitzWith C (regularizedTorusKernel ε hε) :=
  exists_bounded_lipschitz_of_contDiff_periodic
    ((regularizedTorusKernel_smooth hε hε1).of_le (by simp))
    (regularizedTorusKernel_periodic ε hε)

theorem integral_regularizedTorusKernel {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    (∫ x in torusBox, regularizedTorusKernel ε hε x) = 0 := by
  have hc := (torusKernelMollifier_test hε hε1).1.continuous
  obtain ⟨C, hC⟩ := bound_on_box hc
  apply integral_torusKernelVelocity hc.aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_torusBox] with x hx
  simpa only [Real.norm_eq_abs] using hC x hx

end Euler2D

end
