module

public import RequestProject.Euler.EulerPatchTransport
public import RequestProject.Euler.TorusSmoothKernelBounds
public import RequestProject.Euler.RegularizedVelocitySmoothness

/-! The genuine smooth torus correction along an actual Euler system.
Its time and spatial regularity come from the same particle maps and
the actual Green correction. The label integral is identified with the
convolution of the actual transported vorticity, not assumed to equal it. -/

@[expose] public section

set_option maxHeartbeats 2500000

noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal ContDiff

namespace Euler2D

def torusSmoothCorrectionKernel : R2 → R2 := perpGradient torusGreenCorrection

theorem torusSmoothCorrectionKernel_smooth : ContDiff ℝ ∞ torusSmoothCorrectionKernel :=
  contDiff_perpGradient torusGreenCorrection_smooth

theorem torusSmoothCorrectionKernel_periodic : IsTorusPeriodic torusSmoothCorrectionKernel :=
  isTorusPeriodic_perpGradient torusGreenCorrection_periodic

namespace BoundedEulerParticleSystem

variable {f : Lp ℝ 2 μT} {T : ℝ} (S : BoundedEulerParticleSystem f T)

def correctionLabelField (t : ℝ) (x : R2) : R2 :=
  ∫ b, f b • torusSmoothCorrectionKernel (x - S.forward t b + torusCenter) ∂μT

def correctionLabelDerivative (t : ℝ) (x : R2) : R2 →L[ℝ] R2 :=
  ∫ b, f b • fderiv ℝ torusSmoothCorrectionKernel (x - S.forward t b + torusCenter) ∂μT

theorem integrable_correctionLabelField_integrand (t : ℝ) (x : R2) :
    Integrable (fun b => f b • torusSmoothCorrectionKernel
      (x - S.forward t b + torusCenter)) μT := by
  obtain ⟨C, hC, _, _⟩ := exists_torusGreenCorrection_perpGradient_bounds
  have hw := (Lp.memLp f).integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  apply (hw.norm.const_mul (C : ℝ)).mono'
  · exact (Lp.aestronglyMeasurable f).smul
      (torusSmoothCorrectionKernel_smooth.continuous.comp
        ((continuous_const.sub (S.forward_continuous.comp
          (continuous_const.prodMk continuous_id))).add continuous_const)).aestronglyMeasurable
  · exact ae_of_all _ fun b => by
      rw [norm_smul, mul_comm (C : ℝ)]
      exact mul_le_mul_of_nonneg_left (hC _) (norm_nonneg _)

theorem integrable_correctionLabelDerivative_integrand (t : ℝ) (x : R2) :
    Integrable (fun b => f b • fderiv ℝ torusSmoothCorrectionKernel
      (x - S.forward t b + torusCenter)) μT := by
  obtain ⟨C, _, hC, _⟩ := exists_torusGreenCorrection_perpGradient_bounds
  have hw := (Lp.memLp f).integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  apply (hw.norm.const_mul (C : ℝ)).mono'
  · exact (Lp.aestronglyMeasurable f).smul
      ((torusSmoothCorrectionKernel_smooth.continuous_fderiv (by simp)).comp
        ((continuous_const.sub (S.forward_continuous.comp
          (continuous_const.prodMk continuous_id))).add continuous_const)).aestronglyMeasurable
  · exact ae_of_all _ fun b => by
      rw [norm_smul, mul_comm (C : ℝ)]
      exact mul_le_mul_of_nonneg_left (hC _) (norm_nonneg _)

theorem continuous_correctionLabelField : Continuous (Function.uncurry S.correctionLabelField) := by
  obtain ⟨C, hC, _, _⟩ := exists_torusGreenCorrection_perpGradient_bounds
  have hw := (Lp.memLp f).integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  apply continuous_of_dominated
    (F := fun p : ℝ × R2 => fun b =>
      f b • torusSmoothCorrectionKernel (p.2 - S.forward p.1 b + torusCenter))
    (bound := fun b => (C : ℝ) * ‖f b‖)
  · intro p
    exact (S.integrable_correctionLabelField_integrand p.1 p.2).aestronglyMeasurable
  · intro p
    exact ae_of_all _ fun b => by
      rw [norm_smul, mul_comm (C : ℝ)]
      exact mul_le_mul_of_nonneg_left (hC _) (norm_nonneg _)
  · exact hw.norm.const_mul _
  · exact ae_of_all _ fun b =>
      (torusSmoothCorrectionKernel_smooth.continuous.comp
        ((continuous_snd.sub (S.forward_continuous.comp
          (continuous_fst.prodMk continuous_const))).add continuous_const)).const_smul (f b)

theorem continuous_correctionLabelDerivative :
    Continuous (Function.uncurry S.correctionLabelDerivative) := by
  obtain ⟨C, _, hC, _⟩ := exists_torusGreenCorrection_perpGradient_bounds
  have hw := (Lp.memLp f).integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  apply continuous_of_dominated
    (F := fun p : ℝ × R2 => fun b =>
      f b • fderiv ℝ torusSmoothCorrectionKernel (p.2 - S.forward p.1 b + torusCenter))
    (bound := fun b => (C : ℝ) * ‖f b‖)
  · intro p
    exact (S.integrable_correctionLabelDerivative_integrand p.1 p.2).aestronglyMeasurable
  · intro p
    exact ae_of_all _ fun b => by
      rw [norm_smul, mul_comm (C : ℝ)]
      exact mul_le_mul_of_nonneg_left (hC _) (norm_nonneg _)
  · exact hw.norm.const_mul _
  · exact ae_of_all _ fun b =>
      ((torusSmoothCorrectionKernel_smooth.continuous_fderiv (by simp)).comp
        ((continuous_snd.sub (S.forward_continuous.comp
          (continuous_fst.prodMk continuous_const))).add continuous_const)).const_smul (f b)

theorem hasFDerivAt_correctionLabelField (t : ℝ) (x : R2) :
    HasFDerivAt (S.correctionLabelField t) (S.correctionLabelDerivative t x) x := by
  obtain ⟨C, _, hC, _⟩ := exists_torusGreenCorrection_perpGradient_bounds
  have hw := (Lp.memLp f).integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le (μ := μT)
    (F := fun x b => f b • torusSmoothCorrectionKernel (x - S.forward t b + torusCenter))
    (F' := fun x b => f b • fderiv ℝ torusSmoothCorrectionKernel (x - S.forward t b + torusCenter))
    (bound := fun b => (C : ℝ) * ‖f b‖) (s := univ) (by simp)
  · exact Eventually.of_forall fun y => (S.integrable_correctionLabelField_integrand t y).aestronglyMeasurable
  · exact S.integrable_correctionLabelField_integrand t x
  · exact (S.integrable_correctionLabelDerivative_integrand t x).aestronglyMeasurable
  · exact ae_of_all _ fun b y _ => by
      rw [norm_smul, mul_comm (C : ℝ)]
      exact mul_le_mul_of_nonneg_left (hC _) (norm_nonneg _)
  · exact hw.norm.const_mul _
  · exact ae_of_all _ fun b y _ => by
      have hd := ((torusSmoothCorrectionKernel_smooth.differentiable (by simp) _).hasFDerivAt.comp y
        (((hasFDerivAt_id y).sub_const (S.forward t b)).add_const torusCenter)).const_smul (f b)
      simpa only [ContinuousLinearMap.comp_id] using hd

theorem isC1SpatialVelocity_correctionLabelField : IsC1SpatialVelocity S.correctionLabelField where
  differentiable t x := (S.hasFDerivAt_correctionLabelField t x).differentiableAt
  continuous_fderiv := by
    have he : (fun p : ℝ × R2 => fderiv ℝ (S.correctionLabelField p.1) p.2) =
        Function.uncurry S.correctionLabelDerivative := by
      funext p
      exact (S.hasFDerivAt_correctionLabelField p.1 p.2).fderiv
    rw [he]
    exact S.continuous_correctionLabelDerivative

theorem correctionLabelField_eq_transported_convolution {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T)
    (x : R2) : S.correctionLabelField t x =
      ∫ y, particleCurlL2 f S.backward S.backward_area t y •
        torusSmoothCorrectionKernel (x - y + torusCenter) ∂μT := by
  have hw := (Lp.memLp f).integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hp : IsVorticityPushForward T (f : R2 → ℝ) (S.transportedScalar f) S.forward := by
    apply IsVorticityPushForward.of_torusInverse hw S.forward_area (fun t _ => S.backward_area t)
    intro t ht
    filter_upwards [ae_restrict_mem measurableSet_torusBox] with a ha
    rw [torusWrap_comp_torusWrap_of_lattice_equivariant (S.backward_lattice t),
      S.backward_forward t ht a]
    exact torusRep_torusProj ha
  obtain ⟨C, hC, _, _⟩ := exists_torusGreenCorrection_perpGradient_bounds
  have hir : Integrable (fun y => S.transportedScalar f t y •
      torusSmoothCorrectionKernel (x - y + torusCenter)) μT := by
    apply ((hp.integrable t ht).norm.const_mul (C : ℝ)).mono'
    · exact (hp.integrable t ht).aestronglyMeasurable.smul
        (torusSmoothCorrectionKernel_smooth.continuous.comp
          ((continuous_const.sub continuous_id).add continuous_const)).aestronglyMeasurable
    · exact ae_of_all _ fun y => by
        rw [norm_smul, mul_comm (C : ℝ)]
        exact mul_le_mul_of_nonneg_left (hC _) (norm_nonneg _)
  have hper : IsTorusPeriodic (fun y => torusSmoothCorrectionKernel (x - y + torusCenter)) := by
    intro y i
    have he : x - (y + EuclideanSpace.single i (2 * Real.pi)) + torusCenter +
        EuclideanSpace.single i (2 * Real.pi) = x - y + torusCenter := by abel
    exact (torusSmoothCorrectionKernel_periodic _ i).symm.trans (congrArg torusSmoothCorrectionKernel he)
  have heq : S.correctionLabelField t x = ∫ y, S.transportedScalar f t y •
      torusSmoothCorrectionKernel (x - y + torusCenter) ∂μT := by
    ext j
    have hl := (EuclideanSpace.proj j : R2 →L[ℝ] ℝ).integral_comp_comm
      (S.integrable_correctionLabelField_integrand t x)
    have hr := (EuclideanSpace.proj j : R2 →L[ℝ] ℝ).integral_comp_comm hir
    simp only [PiLp.proj_apply] at hl hr
    have hpair := hp.pairing t ht (fun y => torusSmoothCorrectionKernel (x - y + torusCenter) j)
      ((EuclideanSpace.proj j : R2 →L[ℝ] ℝ).continuous.comp
        (torusSmoothCorrectionKernel_smooth.continuous.comp
          ((continuous_const.sub continuous_id).add continuous_const)))
      (fun y i => congrArg (fun z : R2 => z j) (hper y i))
    change (∫ b, f b • torusSmoothCorrectionKernel (x - S.forward t b + torusCenter) ∂μT) j = _
    rw [← hl, ← hr]
    simpa only [PiLp.smul_apply, smul_eq_mul] using hpair.symm
  refine heq.trans (integral_congr_ae ?_)
  filter_upwards [particleCurlL2_ae f S.backward S.backward_area t] with y hy
  rw [hy]
  rfl

end BoundedEulerParticleSystem

end Euler2D

end
