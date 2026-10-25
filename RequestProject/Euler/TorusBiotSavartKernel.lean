module

public import RequestProject.Euler.TorusLocalKernel
public import RequestProject.Euler.TorusGreenCorrection
public import RequestProject.Euler.PlanarKernelBounds
public import RequestProject.Euler.VorticityMomentum
public import RequestProject.Euler.TorusTranslations

/-!
# The actual torus Biot–Savart kernel

The explicit local singular kernel and the constructed smooth Poisson
correction give a periodic integrable kernel. Its distributional curl is
the Dirac mass at the center minus the physical reciprocal area.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology Real
open scoped ContDiff ENNReal
open Laplacian

namespace Euler2D

lemma DivFree.congr_ae {u v : R2 → R2} (hu : DivFree u)
    (huv : u =ᵐ[μT] v) : DivFree v := by
  intro ψ hψ
  calc
    _ = ∫ x in torusBox, ∑ i : Fin 2, u x i * pd i ψ x := by
      apply integral_congr_ae
      filter_upwards [huv] with x hx
      rw [hx]
    _ = 0 := hu ψ hψ

lemma integrable_coord_of_integrable {u : R2 → R2} (hu : Integrable u μT)
    (i : Fin 2) : Integrable (fun x => u x i) μT := by
  apply hu.norm.mono' ((EuclideanSpace.proj i : R2 →L[ℝ] ℝ).continuous.comp_aestronglyMeasurable
    hu.aestronglyMeasurable)
  exact Eventually.of_forall fun x => by
    simpa only [PiLp.proj_apply, Real.norm_eq_abs] using abs_coord_le (u x) i

lemma integrable_coord_mul_continuous {u : R2 → R2} (hu : Integrable u μT)
    {f : R2 → ℝ} (hf : Continuous f) (i : Fin 2) :
    Integrable (fun x => u x i * f x) μT := by
  obtain ⟨C, hC⟩ := bound_on_box hf
  apply (integrable_coord_of_integrable hu i).mul_bdd hf.aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_torusBox] with x hx
  simpa only [Real.norm_eq_abs] using hC x hx

lemma divFree_perpGradient {f : R2 → ℝ} (hf : ContDiff ℝ ∞ f)
    (hp : IsTorusPeriodic f) : DivFree (perpGradient f) := by
  have hm := continuous_vector_memLp_torus (contDiff_perpGradient hf).continuous 2
  have hd := divFree_of_pointwise_divergence_zero hm.coeFn_toLp
    ((contDiff_perpGradient hf).of_le (by simp)) (isTorusPeriodic_perpGradient hp)
    (perpGradient_divergence hf)
  exact hd.congr_ae hm.coeFn_toLp

lemma isCurl_perpGradient {f : R2 → ℝ} (hf : ContDiff ℝ ∞ f)
    (hp : IsTorusPeriodic f) : IsCurl (perpGradient f) (fun x => Δ f x) := by
  have hd := (contDiff_perpGradient hf).differentiable (by simp)
  apply (isCurl_of_C1_matching_faces ((contDiff_perpGradient hf).of_le (by simp))
    (isTorusPeriodic_perpGradient hp).matchesTorusFaces).congr_ae (EventuallyEq.rfl)
  apply Eventually.of_forall
  intro x
  dsimp only
  rw [← torus_pd_component _ x (hd x) 0 1, ← torus_pd_component _ x (hd x) 1 0]
  simp only [perpGradient_one, perpGradient_zero]
  have hneg : pd 1 (fun y => -pd 1 f y) x = -pd 1 (pd 1 f) x := by
    unfold pd
    rw [show (fun y => -(fderiv ℝ f y) (EuclideanSpace.single 1 1)) =
      -(fun y => (fderiv ℝ f y) (EuclideanSpace.single 1 1)) from rfl, fderiv_neg]
    rfl
  rw [hneg]
  change pd 0 (pd 0 f) x - -pd 1 (pd 1 f) x = Δ f x
  rw [laplacian_eq_pd_sum (hf.of_le (by decide))]
  ring

/-- The kernel has its singularity at `torusCenter`. -/
def torusBiotSavartKernel (x : R2) : R2 :=
  periodicLocalKernel x + perpGradient torusGreenCorrection x

lemma measurable_localPlanarKernel : Measurable localPlanarKernel :=
  (contDiff_planarCutoff.continuous.measurable.comp
    (continuous_norm.measurable.pow_const 2)).smul measurable_kernelK

lemma periodicLocalKernel_eq_wrapped (x : R2) :
    periodicLocalKernel x = localPlanarKernel (torusWrap x - torusCenter) := by
  rw [← isTorusPeriodic_periodicLocalKernel.eq_torusWrap x]
  exact periodicLocalKernel_eq_on_box (torusRep_mem _)

lemma measurable_periodicLocalKernel : Measurable periodicLocalKernel := by
  have he : periodicLocalKernel = fun x => localPlanarKernel (torusWrap x - torusCenter) :=
    funext periodicLocalKernel_eq_wrapped
  rw [he]
  exact measurable_localPlanarKernel.comp (measurable_torusWrap.sub measurable_const)

theorem measurable_torusBiotSavartKernel : Measurable torusBiotSavartKernel :=
  measurable_periodicLocalKernel.add
    (contDiff_perpGradient torusGreenCorrection_smooth).continuous.measurable

theorem isTorusPeriodic_torusBiotSavartKernel : IsTorusPeriodic torusBiotSavartKernel := by
  intro x i
  simp only [torusBiotSavartKernel, isTorusPeriodic_periodicLocalKernel x i,
    isTorusPeriodic_perpGradient torusGreenCorrection_periodic x i]

theorem integrable_torusBiotSavartKernel : Integrable torusBiotSavartKernel μT := by
  exact integrable_periodicLocalKernel.add
    ((continuous_vector_memLp_torus
      (contDiff_perpGradient torusGreenCorrection_smooth).continuous 1).integrable (le_refl 1))

lemma integral_perpGradient {f : R2 → ℝ} (hf : ContDiff ℝ ∞ f)
    (hp : IsTorusPeriodic f) : (∫ x in torusBox, perpGradient f x) = 0 := by
  have hi := (continuous_vector_memLp_torus (contDiff_perpGradient hf).continuous 1).integrable
    (le_refl 1)
  have hc := integral_pd_eq_zero f (hf.of_le (by simp)) hp
  ext i
  have he := (EuclideanSpace.proj i : R2 →L[ℝ] ℝ).integral_comp_comm hi
  change (∫ x in torusBox, perpGradient f x i) = (∫ x in torusBox, perpGradient f x) i at he
  rw [← he]
  fin_cases i
  · change (∫ x in torusBox, -pd 1 f x) = 0
    rw [integral_neg, hc, neg_zero]
  · change (∫ x in torusBox, pd 0 f x) = 0
    exact hc 0

lemma integral_periodicLocalKernel : (∫ x in torusBox, periodicLocalKernel x) = 0 := by
  calc
    _ = ∫ x in torusBox, localPlanarKernel (x - torusCenter) := by
      apply setIntegral_congr_fun measurableSet_torusBox
      intro x hx
      exact periodicLocalKernel_eq_on_box hx
    _ = ∫ x : R2, localPlanarKernel (x - torusCenter) := by
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro x hx
      exact localPlanarKernel_eq_zero_of_one_le_norm
        (le_of_not_gt (fun hn => hx (norm_sub_center_lt_one_mem_box hn)))
    _ = 0 := by
      rw [integral_sub_right_eq_self, integral_localPlanarKernel]

theorem integral_torusBiotSavartKernel : (∫ x in torusBox, torusBiotSavartKernel x) = 0 := by
  have hi := (continuous_vector_memLp_torus
    (contDiff_perpGradient torusGreenCorrection_smooth).continuous 1).integrable (le_refl 1)
  change (∫ x in torusBox, periodicLocalKernel x + perpGradient torusGreenCorrection x) = 0
  rw [integral_add integrable_periodicLocalKernel hi, integral_periodicLocalKernel,
    integral_perpGradient torusGreenCorrection_smooth torusGreenCorrection_periodic, add_zero]

theorem divFree_torusBiotSavartKernel : DivFree torusBiotSavartKernel := by
  intro ψ hψ
  have hp (i : Fin 2) : Continuous (pd i ψ) := (contDiff_pd_infty hψ.1 i).continuous
  have hlocal : Integrable (fun x => ∑ i : Fin 2,
      periodicLocalKernel x i * pd i ψ x) μT :=
    integrable_finset_sum _ (fun i _ => integrable_coord_mul_continuous
      integrable_periodicLocalKernel (hp i) i)
  have hsmooth : Integrable (fun x => ∑ i : Fin 2,
      perpGradient torusGreenCorrection x i * pd i ψ x) μT :=
    integrable_torusBox_of_continuous (continuous_finset_sum _ (fun i _ =>
      ((EuclideanSpace.proj i : R2 →L[ℝ] ℝ).continuous.comp
        (contDiff_perpGradient torusGreenCorrection_smooth).continuous).mul (hp i)))
  calc
    _ = ∫ x in torusBox, (∑ i : Fin 2, periodicLocalKernel x i * pd i ψ x) +
        ∑ i : Fin 2, perpGradient torusGreenCorrection x i * pd i ψ x := by
      congr 1
      funext x
      simp only [torusBiotSavartKernel, PiLp.add_apply, add_mul, Finset.sum_add_distrib]
    _ = 0 := by
      rw [integral_add hlocal hsmooth, divFree_periodicLocalKernel ψ hψ,
        divFree_perpGradient torusGreenCorrection_smooth torusGreenCorrection_periodic ψ hψ]
      simp

theorem torusBiotSavartKernel_weak_curl {ψ : R2 → ℝ} (hψ : IsScalarTest ψ) :
    (∫ x in torusBox, torusBiotSavartKernel x 0 * pd 1 ψ x -
      torusBiotSavartKernel x 1 * pd 0 ψ x) =
      ψ torusCenter - ((2 * π) ^ 2)⁻¹ * ∫ x in torusBox, ψ x := by
  have hp (i : Fin 2) : Continuous (pd i ψ) := (contDiff_pd_infty hψ.1 i).continuous
  have hlocal : Integrable (fun x => periodicLocalKernel x 0 * pd 1 ψ x -
      periodicLocalKernel x 1 * pd 0 ψ x) μT :=
    (integrable_coord_mul_continuous integrable_periodicLocalKernel (hp 1) 0).sub
      (integrable_coord_mul_continuous integrable_periodicLocalKernel (hp 0) 1)
  have hc := (contDiff_perpGradient torusGreenCorrection_smooth).continuous
  have hsmooth : Integrable (fun x => perpGradient torusGreenCorrection x 0 * pd 1 ψ x -
      perpGradient torusGreenCorrection x 1 * pd 0 ψ x) μT :=
    integrable_torusBox_of_continuous
      ((((EuclideanSpace.proj 0 : R2 →L[ℝ] ℝ).continuous.comp hc).mul (hp 1)).sub
        (((EuclideanSpace.proj 1 : R2 →L[ℝ] ℝ).continuous.comp hc).mul (hp 0)))
  have herr : Integrable (fun x => periodicCenteredSource localPlanarKernelError x * ψ x) μT :=
    integrable_torusBox_of_continuous
      ((isScalarTest_periodicCenteredSource contDiff_localPlanarKernelError
        (fun _ hy => localPlanarKernelError_eq_zero_of_one_le_norm hy)).1.continuous.mul
          hψ.1.continuous)
  have hconst : Integrable (fun x => ((2 * π) ^ 2)⁻¹ * ψ x) μT :=
    (integrable_torusBox_of_continuous hψ.1.continuous).const_mul _
  have heq : (∫ x in torusBox, Δ torusGreenCorrection x * ψ x) =
      -(∫ x in torusBox, periodicCenteredSource localPlanarKernelError x * ψ x) -
        ((2 * π) ^ 2)⁻¹ * ∫ x in torusBox, ψ x := by
    simp_rw [torusGreenCorrection_laplacian, canonicalTorusCorrectionSource,
      torusCorrectionSource, sub_mul, neg_mul]
    calc
      _ = (∫ x in torusBox, -(periodicCenteredSource localPlanarKernelError x * ψ x)) -
          ∫ x in torusBox, ((2 * π) ^ 2)⁻¹ * ψ x := integral_sub herr.neg hconst
      _ = _ := by rw [integral_neg, integral_const_mul]
  calc
    _ = (∫ x in torusBox, periodicLocalKernel x 0 * pd 1 ψ x -
        periodicLocalKernel x 1 * pd 0 ψ x) +
        ∫ x in torusBox, perpGradient torusGreenCorrection x 0 * pd 1 ψ x -
          perpGradient torusGreenCorrection x 1 * pd 0 ψ x := by
      rw [← integral_add hlocal hsmooth]
      congr 1
      funext x
      simp only [torusBiotSavartKernel, PiLp.add_apply]
      ring
    _ = _ := by
      rw [periodicLocalKernel_weak_curl (hψ.1.of_le (by simp)),
        ← isCurl_perpGradient torusGreenCorrection_smooth torusGreenCorrection_periodic ψ hψ,
        heq]
      ring

end Euler2D

end
