module

public import RequestProject.Euler.TorusKernelConvolution
public import RequestProject.Euler.PlanarKernelIntegrals

/-! Genuine periodic `L²` approximations of the singular torus kernel. -/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology Metric Real
open scoped ENNReal ContDiff

namespace Euler2D

def truncatedLocalPlanarKernel (ε : ℝ) (x : R2) : R2 :=
  (closedBall (0 : R2) ε)ᶜ.indicator localPlanarKernel x

lemma measurable_truncatedLocalPlanarKernel (ε : ℝ) :
    Measurable (truncatedLocalPlanarKernel ε) :=
  measurable_localPlanarKernel.indicator measurableSet_closedBall.compl

lemma truncatedLocalPlanarKernel_eq_zero_of_one_le_norm (ε : ℝ) {x : R2}
    (hx : 1 ≤ ‖x‖) : truncatedLocalPlanarKernel ε x = 0 := by
  unfold truncatedLocalPlanarKernel
  by_cases hm : x ∈ (closedBall (0 : R2) ε)ᶜ
  · rw [Set.indicator_of_mem hm, localPlanarKernel_eq_zero_of_one_le_norm hx]
  · rw [Set.indicator_of_notMem hm]

lemma norm_truncatedLocalPlanarKernel_le {ε : ℝ} (hε : 0 < ε) (x : R2) :
    ‖truncatedLocalPlanarKernel ε x‖ ≤ (2 * Real.pi)⁻¹ * ε⁻¹ := by
  by_cases hx : x ∈ (closedBall (0 : R2) ε)ᶜ
  · have hxn : ε < ‖x‖ := lt_of_not_ge (fun hn => hx (mem_closedBall_zero_iff.mpr hn))
    rw [truncatedLocalPlanarKernel, Set.indicator_of_mem hx]
    exact (norm_localPlanarKernel_le x).trans
      (mul_le_mul_of_nonneg_left ((inv_le_inv₀ (hε.trans hxn) hε).mpr hxn.le) (by positivity))
  · rw [truncatedLocalPlanarKernel, Set.indicator_of_notMem hx, norm_zero]
    positivity

def periodicTruncatedLocalKernel (ε : ℝ) : R2 → R2 :=
  torusPeriodize (fun x => truncatedLocalPlanarKernel ε (x - torusCenter))

lemma isTorusPeriodic_periodicTruncatedLocalKernel (ε : ℝ) :
    IsTorusPeriodic (periodicTruncatedLocalKernel ε) := isTorusPeriodic_torusPeriodize _

lemma periodicTruncatedLocalKernel_eq_on_box (ε : ℝ) {x : R2} (hx : x ∈ torusBox) :
    periodicTruncatedLocalKernel ε x = truncatedLocalPlanarKernel ε (x - torusCenter) :=
  torusPeriodize_eq_on_box (fun _ hy => truncatedLocalPlanarKernel_eq_zero_of_one_le_norm ε hy) hx

lemma periodicTruncatedLocalKernel_eq_wrapped (ε : ℝ) (x : R2) :
    periodicTruncatedLocalKernel ε x = truncatedLocalPlanarKernel ε (torusWrap x - torusCenter) := by
  rw [← (isTorusPeriodic_periodicTruncatedLocalKernel ε).eq_torusWrap x]
  exact periodicTruncatedLocalKernel_eq_on_box ε (torusRep_mem _)

lemma measurable_periodicTruncatedLocalKernel (ε : ℝ) :
    Measurable (periodicTruncatedLocalKernel ε) := by
  have he := funext (periodicTruncatedLocalKernel_eq_wrapped ε)
  rw [he]
  exact (measurable_truncatedLocalPlanarKernel ε).comp (measurable_torusWrap.sub measurable_const)

lemma memLp_periodicTruncatedLocalKernel {ε : ℝ} (hε : 0 < ε) (q : ENNReal) :
    MemLp (periodicTruncatedLocalKernel ε) q μT := by
  apply MemLp.of_bound (measurable_periodicTruncatedLocalKernel ε).aestronglyMeasurable
    ((2 * Real.pi)⁻¹ * ε⁻¹)
  exact Eventually.of_forall fun x => by
    rw [periodicTruncatedLocalKernel_eq_wrapped]
    exact norm_truncatedLocalPlanarKernel_le hε _

def torusKernelL2Approx (ε : ℝ) (x : R2) : R2 :=
  periodicTruncatedLocalKernel ε x + perpGradient torusGreenCorrection x

lemma isTorusPeriodic_torusKernelL2Approx (ε : ℝ) : IsTorusPeriodic (torusKernelL2Approx ε) := by
  intro x i
  simp only [torusKernelL2Approx, isTorusPeriodic_periodicTruncatedLocalKernel ε x i,
    isTorusPeriodic_perpGradient torusGreenCorrection_periodic x i]

lemma measurable_torusKernelL2Approx (ε : ℝ) : Measurable (torusKernelL2Approx ε) :=
  (measurable_periodicTruncatedLocalKernel ε).add
    (contDiff_perpGradient torusGreenCorrection_smooth).continuous.measurable

theorem memLp_torusKernelL2Approx {ε : ℝ} (hε : 0 < ε) (q : ENNReal) :
    MemLp (torusKernelL2Approx ε) q μT :=
  (memLp_periodicTruncatedLocalKernel hε q).add
    (continuous_vector_memLp_torus (contDiff_perpGradient torusGreenCorrection_smooth).continuous q)

lemma torusKernelL2Approx_error_on_box (ε : ℝ) {x : R2} (hx : x ∈ torusBox) :
    torusBiotSavartKernel x - torusKernelL2Approx ε x =
      (closedBall (0 : R2) ε).indicator localPlanarKernel (x - torusCenter) := by
  simp only [torusBiotSavartKernel, torusKernelL2Approx, add_sub_add_right_eq_sub]
  rw [periodicLocalKernel_eq_on_box hx, periodicTruncatedLocalKernel_eq_on_box ε hx]
  unfold truncatedLocalPlanarKernel
  by_cases hm : x - torusCenter ∈ closedBall (0 : R2) ε
  · rw [Set.indicator_of_mem hm, Set.indicator_of_notMem (show x - torusCenter ∉
      (closedBall (0 : R2) ε)ᶜ from fun h => h hm), sub_zero]
  · rw [Set.indicator_of_notMem hm, Set.indicator_of_mem hm, sub_self]

theorem integral_norm_torusKernelL2Approx_error_le {ε : ℝ} (hε : 0 ≤ ε) :
    (∫ x in torusBox, ‖torusBiotSavartKernel x - torusKernelL2Approx ε x‖) ≤ ε := by
  calc
    _ = ∫ x in torusBox,
        ‖(closedBall (0 : R2) ε).indicator localPlanarKernel (x - torusCenter)‖ := by
      apply setIntegral_congr_fun measurableSet_torusBox
      intro x hx
      change ‖torusBiotSavartKernel x - torusKernelL2Approx ε x‖ = _
      rw [torusKernelL2Approx_error_on_box ε hx]
    _ = ∫ x : R2, ‖(closedBall (0 : R2) ε).indicator localPlanarKernel (x - torusCenter)‖ := by
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro x hx
      have hz := localPlanarKernel_eq_zero_of_one_le_norm
        (le_of_not_gt (fun hn => hx (norm_sub_center_lt_one_mem_box hn)))
      by_cases hm : x - torusCenter ∈ closedBall (0 : R2) ε
      · rw [Set.indicator_of_mem hm, hz, norm_zero]
      · rw [Set.indicator_of_notMem hm, norm_zero]
    _ = ∫ x : R2, ‖(closedBall (0 : R2) ε).indicator localPlanarKernel x‖ :=
      integral_sub_right_eq_self (μ := volume)
        (fun x : R2 => ‖(closedBall (0 : R2) ε).indicator localPlanarKernel x‖) torusCenter
    _ = ∫ x in closedBall (0 : R2) ε, ‖localPlanarKernel x‖ := by
      rw [← integral_indicator measurableSet_closedBall]
      congr 1
      funext x
      exact norm_indicator_eq_indicator_norm _ _
    _ ≤ ε := integral_norm_localPlanarKernel_closedBall_le hε

lemma TorusAreaPreserving.memLp_comp {F : Type*} [NormedAddCommGroup F]
    {X : R2 → R2} (hX : TorusAreaPreserving X) {f : R2 → F} {q : ENNReal}
    (hf : MemLp f q μT) (hp : IsTorusPeriodic f) : MemLp (f ∘ X) q μT := by
  have he : f ∘ X = f ∘ (torusWrap ∘ X) := by
    funext x
    exact (hp.eq_torusWrap (X x)).symm
  rw [he]
  exact hf.comp_measurePreserving hX

end Euler2D

end
