module

public import RequestProject.Euler.TorusKernelSymmetry
public import RequestProject.Euler.TorusMollificationApproximation

/-!
# Explicit fourfold averaging of the actual normalized mollifier

The four rotated copies are averaged before convolution.  This makes the
required scalar symmetry explicit without imposing any extra invariance
on the arbitrary smooth bump chosen by the library.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology Metric
open scoped ContDiff NNReal ENNReal Convolution

namespace Euler2D

def fourfoldRawKernelMollifier (ε : ℝ) (hε : 0 < ε) (x : R2) : ℝ :=
  (rawKernelMollifier ε hε x + rawKernelMollifier ε hε (torusQuarterTurn x) +
    rawKernelMollifier ε hε (torusQuarterTurn (torusQuarterTurn x)) +
    rawKernelMollifier ε hε (torusQuarterTurn (torusQuarterTurn (torusQuarterTurn x)))) / 4

def fourfoldTorusKernelMollifier (ε : ℝ) (hε : 0 < ε) : R2 → ℝ :=
  torusPeriodize (fourfoldRawKernelMollifier ε hε)

def fourfoldRegularizedTorusKernel (ε : ℝ) (hε : 0 < ε) : R2 → R2 :=
  torusKernelVelocity (fourfoldTorusKernelMollifier ε hε)

theorem fourfoldRawKernelMollifier_quarterTurn (ε : ℝ) (hε : 0 < ε) (x : R2) :
    fourfoldRawKernelMollifier ε hε (torusQuarterTurn x) = fourfoldRawKernelMollifier ε hε x := by
  unfold fourfoldRawKernelMollifier
  rw [torusQuarterTurn_four]
  ring

theorem fourfoldRawKernelMollifier_nonneg (ε : ℝ) (hε : 0 < ε) (x : R2) :
    0 ≤ fourfoldRawKernelMollifier ε hε x := by
  unfold fourfoldRawKernelMollifier
  have h0 := rawKernelMollifier_nonneg ε hε x
  have h1 := rawKernelMollifier_nonneg ε hε (torusQuarterTurn x)
  have h2 := rawKernelMollifier_nonneg ε hε (torusQuarterTurn (torusQuarterTurn x))
  have h3 := rawKernelMollifier_nonneg ε hε (torusQuarterTurn (torusQuarterTurn (torusQuarterTurn x)))
  positivity

theorem fourfoldRawKernelMollifier_smooth (ε : ℝ) (hε : 0 < ε) :
    ContDiff ℝ ∞ (fourfoldRawKernelMollifier ε hε) := by
  have h0 := rawKernelMollifier_smooth ε hε
  have h1 := h0.comp torusQuarterTurn_smooth
  have h2 := h1.comp torusQuarterTurn_smooth
  have h3 := h2.comp torusQuarterTurn_smooth
  exact ((h0.add h1).add h2 |>.add h3).div_const 4

theorem fourfoldRawKernelMollifier_eq_zero {ε : ℝ} (hε : 0 < ε) {x : R2}
    (hx : ε ≤ ‖x - torusCenter‖) : fourfoldRawKernelMollifier ε hε x = 0 := by
  have h1 : ε ≤ ‖torusQuarterTurn x - torusCenter‖ := by
    rwa [norm_torusQuarterTurn_sub_center]
  have h2 : ε ≤ ‖torusQuarterTurn (torusQuarterTurn x) - torusCenter‖ := by
    rwa [norm_torusQuarterTurn_sub_center]
  have h3 : ε ≤ ‖torusQuarterTurn (torusQuarterTurn (torusQuarterTurn x)) - torusCenter‖ := by
    rwa [norm_torusQuarterTurn_sub_center]
  simp only [fourfoldRawKernelMollifier, rawKernelMollifier_eq_zero hε hx,
    rawKernelMollifier_eq_zero hε h1, rawKernelMollifier_eq_zero hε h2,
    rawKernelMollifier_eq_zero hε h3, add_zero, zero_div]

theorem fourfoldRawKernelMollifier_zero_of_one_le {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (x : R2) (hx : 1 ≤ ‖x - torusCenter‖) : fourfoldRawKernelMollifier ε hε x = 0 :=
  fourfoldRawKernelMollifier_eq_zero hε (hε1.trans hx)

theorem fourfoldRawKernelMollifier_compact (ε : ℝ) (hε : 0 < ε) :
    HasCompactSupport (fourfoldRawKernelMollifier ε hε) := by
  apply HasCompactSupport.intro' (isCompact_closedBall torusCenter ε) isClosed_closedBall
  intro x hx
  apply fourfoldRawKernelMollifier_eq_zero hε
  have hn : ε < dist x torusCenter := lt_of_not_ge (fun hn => hx (mem_closedBall.mpr hn))
  simpa only [dist_eq_norm] using hn.le

lemma integral_comp_torusQuarterTurn {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : R2 → F} (hf : Integrable f volume) :
    (∫ x : R2, f (torusQuarterTurn x)) = ∫ x : R2, f x := by
  have hm : AEStronglyMeasurable f (Measure.map torusQuarterTurn volume) := by
    rw [measurePreserving_torusQuarterTurn.map_eq]
    exact hf.aestronglyMeasurable
  have hi := integral_map measurePreserving_torusQuarterTurn.aemeasurable hm
  rw [measurePreserving_torusQuarterTurn.map_eq] at hi
  exact hi.symm

theorem fourfoldRawKernelMollifier_integral (ε : ℝ) (hε : 0 < ε) :
    (∫ x : R2, fourfoldRawKernelMollifier ε hε x) = 1 := by
  have h0 : Integrable (rawKernelMollifier ε hε) volume :=
    (rawKernelMollifier_smooth ε hε).continuous.integrable_of_hasCompactSupport
      (rawKernelMollifier_compact ε hε)
  have h1 := measurePreserving_torusQuarterTurn.integrable_comp_of_integrable h0
  have h2 := measurePreserving_torusQuarterTurn.integrable_comp_of_integrable h1
  have h3 := measurePreserving_torusQuarterTurn.integrable_comp_of_integrable h2
  have i1 := integral_comp_torusQuarterTurn h0
  have i2 := integral_comp_torusQuarterTurn h1
  have i3 := integral_comp_torusQuarterTurn h2
  simp only [Function.comp_def] at h1 h2 h3 i2 i3
  have h01 : Integrable (fun x => rawKernelMollifier ε hε x +
      rawKernelMollifier ε hε (torusQuarterTurn x)) volume := h0.add h1
  have h012 : Integrable (fun x => rawKernelMollifier ε hε x +
      rawKernelMollifier ε hε (torusQuarterTurn x) +
      rawKernelMollifier ε hε (torusQuarterTurn (torusQuarterTurn x))) volume := h01.add h2
  unfold fourfoldRawKernelMollifier
  rw [integral_div, integral_add h012 h3, integral_add h01 h2, integral_add h0 h1]
  rw [i3, i2, i1, rawKernelMollifier_integral]
  norm_num

theorem fourfoldTorusKernelMollifier_eq_on_box {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    {x : R2} (hx : x ∈ torusBox) :
    fourfoldTorusKernelMollifier ε hε x = fourfoldRawKernelMollifier ε hε x :=
  torusPeriodize_eq_on_box (fourfoldRawKernelMollifier_zero_of_one_le hε hε1) hx

theorem fourfoldTorusKernelMollifier_test {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    IsScalarTest (fourfoldTorusKernelMollifier ε hε) :=
  isScalarTest_torusPeriodize (fourfoldRawKernelMollifier_smooth ε hε)
    (fourfoldRawKernelMollifier_zero_of_one_le hε hε1)

theorem fourfoldTorusKernelMollifier_nonneg (ε : ℝ) (hε : 0 < ε) (x : R2) :
    0 ≤ fourfoldTorusKernelMollifier ε hε x :=
  tsum_nonneg (fun k => fourfoldRawKernelMollifier_nonneg ε hε (x + torusLatticeShift k))

theorem fourfoldTorusKernelMollifier_integral {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    (∫ x in torusBox, fourfoldTorusKernelMollifier ε hε x) = 1 := by
  calc
    _ = ∫ x in torusBox, fourfoldRawKernelMollifier ε hε x :=
      setIntegral_congr_fun measurableSet_torusBox
        (fun x hx => fourfoldTorusKernelMollifier_eq_on_box hε hε1 hx)
    _ = ∫ x : R2, fourfoldRawKernelMollifier ε hε x := by
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro x hx
      exact fourfoldRawKernelMollifier_zero_of_one_le hε hε1 x
        (le_of_not_gt (fun hn => hx (norm_sub_center_lt_one_mem_box hn)))
    _ = 1 := fourfoldRawKernelMollifier_integral ε hε

theorem fourfoldTorusKernelMollifier_eq_zero_on_box {ε : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1) {x : R2} (hx : x ∈ torusBox)
    (hxe : ε ≤ ‖x - torusCenter‖) : fourfoldTorusKernelMollifier ε hε x = 0 := by
  rw [fourfoldTorusKernelMollifier_eq_on_box hε hε1 hx]
  exact fourfoldRawKernelMollifier_eq_zero hε hxe

theorem fourfoldTorusKernelMollifier_quarterTurn (ε : ℝ) (hε : 0 < ε) (x : R2) :
    fourfoldTorusKernelMollifier ε hε (torusQuarterTurn x) =
      fourfoldTorusKernelMollifier ε hε x := by
  change (∑' k, fourfoldRawKernelMollifier ε hε (torusQuarterTurn x + torusLatticeShift k)) = _
  rw [← torusLatticeQuarterTurn.tsum_eq]
  apply tsum_congr
  intro k
  rw [torusLatticeShift_quarterTurn, ← torusQuarterTurn_add,
    fourfoldRawKernelMollifier_quarterTurn]

theorem fourfoldRegularizedTorusKernel_eq_convolution {ε : ℝ} (hε : 0 < ε)
    (hε1 : ε ≤ 1) (x : R2) :
    fourfoldRegularizedTorusKernel ε hε x =
      (fourfoldRawKernelMollifier ε hε ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
        torusBiotSavartKernel) (x + torusCenter) := by
  change (∫ z in torusBox, fourfoldTorusKernelMollifier ε hε z •
    torusBiotSavartKernel (x - z + torusCenter)) = _
  calc
    _ = ∫ z in torusBox, fourfoldRawKernelMollifier ε hε z •
        torusBiotSavartKernel (x - z + torusCenter) := by
      apply setIntegral_congr_fun measurableSet_torusBox
      intro z hz
      dsimp only
      rw [fourfoldTorusKernelMollifier_eq_on_box hε hε1 hz]
    _ = ∫ z : R2, fourfoldRawKernelMollifier ε hε z •
        torusBiotSavartKernel (x - z + torusCenter) := by
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro z hz
      rw [fourfoldRawKernelMollifier_zero_of_one_le hε hε1 z
        (le_of_not_gt (fun hn => hz (norm_sub_center_lt_one_mem_box hn))), zero_smul]
    _ = _ := by
      unfold convolution
      apply integral_congr_ae
      exact Eventually.of_forall (fun z => by
        simp only [ContinuousLinearMap.lsmul_apply]
        congr 2
        abel)

theorem fourfoldRegularizedTorusKernel_smooth {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ContDiff ℝ ∞ (fourfoldRegularizedTorusKernel ε hε) := by
  have hc : ContDiff ℝ ∞ (fourfoldRawKernelMollifier ε hε ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
      torusBiotSavartKernel) :=
    (fourfoldRawKernelMollifier_compact ε hε).contDiff_convolution_left _
      (fourfoldRawKernelMollifier_smooth ε hε) locallyIntegrable_torusBiotSavartKernel
  have heq := funext (fourfoldRegularizedTorusKernel_eq_convolution hε hε1)
  rw [heq]
  exact hc.comp (contDiff_id.add contDiff_const)

theorem fourfoldRegularizedTorusKernel_periodic (ε : ℝ) (hε : 0 < ε) :
    IsTorusPeriodic (fourfoldRegularizedTorusKernel ε hε) := isTorusPeriodic_torusKernelVelocity _

theorem fourfoldRegularizedTorusKernel_divFree {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    DivFree (fourfoldRegularizedTorusKernel ε hε) := by
  have hc := (fourfoldTorusKernelMollifier_test hε hε1).1.continuous
  obtain ⟨C, hC⟩ := bound_on_box hc
  apply divFree_torusKernelVelocity hc.aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_torusBox] with x hx
  simpa only [Real.norm_eq_abs] using hC x hx

theorem fourfoldRegularizedTorusKernel_divergence {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (x : R2) :
    pd 0 (fourfoldRegularizedTorusKernel ε hε) x 0 + pd 1 (fourfoldRegularizedTorusKernel ε hε) x 1 = 0 :=
  pointwise_divergence_zero_of_smooth_divFree (fourfoldRegularizedTorusKernel_smooth hε hε1)
    (fourfoldRegularizedTorusKernel_periodic ε hε) (fourfoldRegularizedTorusKernel_divFree hε hε1) x

theorem fourfoldRegularizedTorusKernel_bounds {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ C : ℝ≥0, (∀ x, ‖fourfoldRegularizedTorusKernel ε hε x‖ ≤ C) ∧
      (∀ x, ‖fderiv ℝ (fourfoldRegularizedTorusKernel ε hε) x‖ ≤ C) ∧
      LipschitzWith C (fourfoldRegularizedTorusKernel ε hε) :=
  exists_bounded_lipschitz_of_contDiff_periodic
    ((fourfoldRegularizedTorusKernel_smooth hε hε1).of_le (by simp))
    (fourfoldRegularizedTorusKernel_periodic ε hε)

theorem integral_fourfoldRegularizedTorusKernel {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    (∫ x in torusBox, fourfoldRegularizedTorusKernel ε hε x) = 0 := by
  have hc := (fourfoldTorusKernelMollifier_test hε hε1).1.continuous
  obtain ⟨C, hC⟩ := bound_on_box hc
  apply integral_torusKernelVelocity hc.aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_torusBox] with x hx
  simpa only [Real.norm_eq_abs] using hC x hx

end Euler2D

end
