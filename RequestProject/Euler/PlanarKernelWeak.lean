module

public import RequestProject.Euler.KernelIdentities
public import RequestProject.Euler.Stationary
public import RequestProject.Euler.LagrangianTransport
public import Mathlib.Analysis.SpecialFunctions.PolarCoord

/-!
# The genuine planar Biot--Savart distribution identities

Polar change of variables is performed on actual Lebesgue measure.
The Jacobian cancels the kernel's radial singularity before Fubini and
the fundamental theorem of calculus are used.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology Metric Real
open scoped ENNReal ContDiff

namespace Euler2D

def planeCoordinates : R2 ≃ᵐ (ℝ × ℝ) :=
  (MeasurableEquiv.toLp 2 (Fin 2 → ℝ)).symm.trans (MeasurableEquiv.finTwoArrow (α := ℝ))

lemma planeCoordinates_measurePreserving : MeasurePreserving planeCoordinates volume volume :=
  (volume_preserving_finTwoArrow ℝ).comp (PiLp.volume_preserving_ofLp (Fin 2))

def polarUnit (θ : ℝ) : R2 := torusVec (Real.cos θ) (Real.sin θ)

def polarPoint (r θ : ℝ) : R2 := r • polarUnit θ

@[simp] lemma polarUnit_zero (θ : ℝ) : polarUnit θ 0 = Real.cos θ := rfl
@[simp] lemma polarUnit_one (θ : ℝ) : polarUnit θ 1 = Real.sin θ := rfl
@[simp] lemma polarPoint_zero (r θ : ℝ) : polarPoint r θ 0 = r * Real.cos θ := rfl
@[simp] lemma polarPoint_one (r θ : ℝ) : polarPoint r θ 1 = r * Real.sin θ := rfl

lemma norm_polarUnit (θ : ℝ) : ‖polarUnit θ‖ = 1 := by
  rw [EuclideanSpace.norm_eq]
  simp [Fin.sum_univ_two, Real.cos_sq_add_sin_sq]

lemma norm_polarPoint (r θ : ℝ) : ‖polarPoint r θ‖ = |r| := by
  rw [polarPoint, norm_smul, norm_polarUnit, mul_one, Real.norm_eq_abs]

lemma continuous_polarUnit : Continuous polarUnit := by
  exact continuous_torusVec.comp (Real.continuous_cos.prodMk Real.continuous_sin)

lemma continuous_polarPoint : Continuous (fun p : ℝ × ℝ => polarPoint p.1 p.2) :=
  continuous_fst.smul (continuous_polarUnit.comp continuous_snd)

lemma planeCoordinates_symm_polar (p : ℝ × ℝ) :
    planeCoordinates.symm (polarCoord.symm p) = polarPoint p.1 p.2 := by
  ext i
  fin_cases i <;> rfl

/-- The exact polar integration formula on the project's Euclidean plane. -/
theorem integral_polarR2 {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : R2 → F) :
    (∫ p in polarCoord.target, p.1 • f (polarPoint p.1 p.2)) = ∫ x, f x := by
  have h := integral_comp_polarCoord_symm (fun q => f (planeCoordinates.symm q))
  simp_rw [planeCoordinates_symm_polar] at h
  have hcart := planeCoordinates_measurePreserving.integral_comp
    planeCoordinates.measurableEmbedding (fun q => f (planeCoordinates.symm q))
  simp only [MeasurableEquiv.symm_apply_apply] at hcart
  exact h.trans hcart.symm

theorem lintegral_polarR2 (f : R2 → ENNReal) :
    (∫⁻ p in polarCoord.target,
      ENNReal.ofReal p.1 * f (polarPoint p.1 p.2)) = ∫⁻ x, f x := by
  have h := lintegral_comp_polarCoord_symm (fun q => f (planeCoordinates.symm q))
  simp_rw [planeCoordinates_symm_polar, smul_eq_mul] at h
  have hcart := planeCoordinates_measurePreserving.lintegral_comp_emb
    planeCoordinates.measurableEmbedding (fun q => f (planeCoordinates.symm q))
  simp only [MeasurableEquiv.symm_apply_apply] at hcart
  exact h.trans hcart.symm

/-- Integrability can be checked after the singularity has been cancelled
by the genuine polar Jacobian. -/
lemma integrable_of_polarR2 {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : R2 → F} (hf : AEStronglyMeasurable f volume)
    (hpolar : IntegrableOn (fun p : ℝ × ℝ => p.1 • f (polarPoint p.1 p.2))
      polarCoord.target) : Integrable f := by
  refine ⟨hf, ?_⟩
  rw [hasFiniteIntegral_iff_enorm, ← lintegral_polarR2 (fun x => ‖f x‖ₑ)]
  have he : (fun p : ℝ × ℝ => ENNReal.ofReal p.1 * ‖f (polarPoint p.1 p.2)‖ₑ) =ᵐ[
      volume.restrict polarCoord.target]
      (fun p => ‖p.1 • f (polarPoint p.1 p.2)‖ₑ) := by
    filter_upwards [ae_restrict_mem polarCoord.open_target.measurableSet] with p hp
    rw [enorm_smul, Real.enorm_of_nonneg hp.1.le]
  rw [lintegral_congr_ae he]
  exact (hasFiniteIntegral_iff_enorm.mp hpolar.hasFiniteIntegral)

def polarDirectional (ψ : R2 → ℝ) (V : ℝ → R2) (p : ℝ × ℝ) : ℝ :=
  fderiv ℝ ψ (polarPoint p.1 p.2) (V p.2)

lemma continuous_polarDirectional {ψ : R2 → ℝ} (hψ : ContDiff ℝ 1 ψ)
    {V : ℝ → R2} (hV : Continuous V) : Continuous (polarDirectional ψ V) :=
  ((hψ.continuous_fderiv one_ne_zero).comp continuous_polarPoint).clm_apply
    (hV.comp continuous_snd)

/-- Compact support of the test gives a common finite radial rectangle
for every continuous angular direction, including at radial coordinate zero. -/
lemma integrableOn_polarDirectional {ψ : R2 → ℝ} (hψ : ContDiff ℝ 1 ψ)
    (hs : HasCompactSupport ψ) {V : ℝ → R2} (hV : Continuous V) :
    IntegrableOn (polarDirectional ψ V) polarCoord.target := by
  obtain ⟨R, hR, hzero⟩ := (hs.fderiv ℝ).exists_pos_le_norm
  let Q : Set (ℝ × ℝ) := Icc (0 : ℝ) R ×ˢ Icc (-Real.pi) Real.pi
  have hQ : MeasurableSet Q := measurableSet_Icc.prod measurableSet_Icc
  have hI : IntegrableOn (polarDirectional ψ V) Q :=
    (continuous_polarDirectional hψ hV).continuousOn.integrableOn_compact
      (isCompact_Icc.prod isCompact_Icc)
  apply hI.integrable_indicator hQ |>.integrableOn.congr
  filter_upwards [ae_restrict_mem polarCoord.open_target.measurableSet] with p hp
  by_cases hr : p.1 ≤ R
  · have hpQ : p ∈ Q := ⟨⟨hp.1.le, hr⟩, hp.2.1.le, hp.2.2.le⟩
    exact Set.indicator_of_mem hpQ _
  · have hpQ : p ∉ Q := fun h => hr h.1.2
    have hD : polarDirectional ψ V p = 0 := by
      unfold polarDirectional
      rw [hzero _ (by rw [norm_polarPoint, abs_of_pos hp.1]; exact (le_of_not_ge hr))]
      rfl
    rw [Set.indicator_of_notMem hpQ, hD]

lemma hasDerivAt_polarPoint_radius (r θ : ℝ) :
    HasDerivAt (fun s => polarPoint s θ) (polarUnit θ) r := by
  simpa only [polarPoint, id_eq, one_smul] using (hasDerivAt_id r).smul_const (polarUnit θ)

lemma hasDerivAt_test_polar_radius {ψ : R2 → ℝ} (hψ : ContDiff ℝ 1 ψ) (r θ : ℝ) :
    HasDerivAt (fun s => ψ (polarPoint s θ))
      (polarDirectional ψ polarUnit (r, θ)) r :=
  (hψ.differentiable one_ne_zero (polarPoint r θ)).hasFDerivAt.comp_hasDerivAt r
    (hasDerivAt_polarPoint_radius r θ)

lemma hasCompactSupport_test_polar_line {ψ : R2 → ℝ} (hs : HasCompactSupport ψ) (θ : ℝ) :
    HasCompactSupport (fun r => ψ (polarPoint r θ)) := by
  have hi : Isometry (fun r : ℝ => polarPoint r θ) := by
    apply Isometry.of_dist_eq
    intro r s
    rw [dist_eq_norm, show polarPoint r θ - polarPoint s θ = polarPoint (r - s) θ by
      simp only [polarPoint, sub_smul], norm_polarPoint, Real.dist_eq]
  exact hs.comp_isClosedEmbedding hi.isClosedEmbedding

lemma integral_polar_radialDerivative {ψ : R2 → ℝ} (hψ : ContDiff ℝ 1 ψ)
    (hs : HasCompactSupport ψ) (θ : ℝ) :
    (∫ r in Ioi (0 : ℝ), polarDirectional ψ polarUnit (r, θ)) = -ψ 0 := by
  have hl : ContDiff ℝ 1 (fun r => ψ (polarPoint r θ)) :=
    hψ.comp (contDiff_id.smul contDiff_const)
  have hd (r : ℝ) : deriv (fun s => ψ (polarPoint s θ)) r =
      polarDirectional ψ polarUnit (r, θ) := (hasDerivAt_test_polar_radius hψ r θ).deriv
  have hftc := HasCompactSupport.integral_Ioi_deriv_eq hl (hasCompactSupport_test_polar_line hs θ) 0
  simp_rw [hd] at hftc
  simpa only [polarPoint, zero_smul] using hftc

lemma polar_curl_kernel {ψ : R2 → ℝ} (r θ : ℝ) (hr : 0 < r) :
    r * (kernelK (polarPoint r θ) 0 * pd 1 ψ (polarPoint r θ) -
      kernelK (polarPoint r θ) 1 * pd 0 ψ (polarPoint r θ)) =
      -(polarDirectional ψ polarUnit (r, θ)) / (2 * Real.pi) := by
  rw [polarDirectional, fderiv_apply_eq_sum_pd]
  simp only [Fin.sum_univ_two, polarUnit_zero, polarUnit_one]
  simp only [kernelK, PiLp.smul_apply, smul_eq_mul, norm_polarPoint, abs_of_pos hr]
  change r * ((2 * Real.pi * r ^ 2)⁻¹ * (-(r * Real.sin θ)) * pd 1 ψ (polarPoint r θ) -
    (2 * Real.pi * r ^ 2)⁻¹ * (r * Real.cos θ) * pd 0 ψ (polarPoint r θ)) =
      -(Real.cos θ * pd 0 ψ (polarPoint r θ) + Real.sin θ * pd 1 ψ (polarPoint r θ)) / (2 * Real.pi)
  field_simp [hr.ne', Real.pi_ne_zero]
  ring

def kernelCurlTest (ψ : R2 → ℝ) (x : R2) : ℝ :=
  kernelK x 0 * pd 1 ψ x - kernelK x 1 * pd 0 ψ x

def kernelDivTest (ψ : R2 → ℝ) (x : R2) : ℝ :=
  ∑ i : Fin 2, kernelK x i * pd i ψ x

lemma measurable_kernelK : Measurable kernelK := by
  have hd : Measurable (fun x : R2 => (2 * Real.pi * ‖x‖ ^ 2)⁻¹) :=
    (measurable_const.mul (continuous_norm.measurable.pow_const 2)).inv
  exact hd.smul perpJL.continuous.measurable

lemma measurable_kernelCurlTest {ψ : R2 → ℝ} (hψ : ContDiff ℝ 1 ψ) :
    Measurable (kernelCurlTest ψ) := by
  have hK (i : Fin 2) : Measurable (fun x => kernelK x i) :=
    (EuclideanSpace.proj i : R2 →L[ℝ] ℝ).continuous.measurable.comp measurable_kernelK
  exact ((hK 0).mul (continuous_pd_of_contDiff_one ψ hψ 1).measurable).sub
    ((hK 1).mul (continuous_pd_of_contDiff_one ψ hψ 0).measurable)

lemma integrable_polar_kernelCurlTest {ψ : R2 → ℝ} (hψ : ContDiff ℝ 1 ψ)
    (hs : HasCompactSupport ψ) :
    IntegrableOn (fun p : ℝ × ℝ => p.1 * kernelCurlTest ψ (polarPoint p.1 p.2))
      polarCoord.target := by
  apply ((integrableOn_polarDirectional hψ hs continuous_polarUnit).neg.div_const
    (2 * Real.pi)).congr
  filter_upwards [ae_restrict_mem polarCoord.open_target.measurableSet] with p hp
  exact (polar_curl_kernel p.1 p.2 hp.1).symm

/-- The singular curl-test integrand is genuinely Lebesgue integrable. -/
theorem integrable_kernelCurlTest {ψ : R2 → ℝ} (hψ : ContDiff ℝ 1 ψ)
    (hs : HasCompactSupport ψ) : Integrable (kernelCurlTest ψ) :=
  integrable_of_polarR2 (measurable_kernelCurlTest hψ).aestronglyMeasurable
    (integrable_polar_kernelCurlTest hψ hs)

lemma integral_polar_radialDirectional {ψ : R2 → ℝ} (hψ : ContDiff ℝ 1 ψ)
    (hs : HasCompactSupport ψ) :
    (∫ p in polarCoord.target, polarDirectional ψ polarUnit p) = -(2 * Real.pi) * ψ 0 := by
  have hI := integrableOn_polarDirectional hψ hs continuous_polarUnit
  have hIprod : Integrable (polarDirectional ψ polarUnit)
      ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioo (-Real.pi) Real.pi))) := by
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
    exact hI
  calc
    _ = ∫ r in Ioi (0 : ℝ), ∫ θ in Ioo (-Real.pi) Real.pi,
        polarDirectional ψ polarUnit (r, θ) := by
      change (∫ p in Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi,
        polarDirectional ψ polarUnit p) = _
      rw [Measure.volume_eq_prod, ← Measure.prod_restrict]
      exact integral_prod _ hIprod
    _ = ∫ θ in Ioo (-Real.pi) Real.pi, ∫ r in Ioi (0 : ℝ),
        polarDirectional ψ polarUnit (r, θ) := integral_integral_swap hIprod
    _ = ∫ θ in Ioo (-Real.pi) Real.pi, -ψ 0 := by
      apply integral_congr_ae
      exact Eventually.of_forall fun θ => integral_polar_radialDerivative hψ hs θ
    _ = -(2 * Real.pi) * ψ 0 := by
      rw [setIntegral_congr_set Ioo_ae_eq_Ioc,
        ← intervalIntegral.integral_of_le (neg_le_self Real.pi_pos.le),
        intervalIntegral.integral_const]
      simp only [smul_eq_mul]
      ring

/-- The actual planar Biot--Savart kernel has unit distributional curl. -/
theorem kernelK_weak_curl {ψ : R2 → ℝ} (hψ : ContDiff ℝ 1 ψ)
    (hs : HasCompactSupport ψ) :
    (∫ x, kernelK x 0 * pd 1 ψ x - kernelK x 1 * pd 0 ψ x) = ψ 0 := by
  change (∫ x, kernelCurlTest ψ x) = ψ 0
  rw [← integral_polarR2 (kernelCurlTest ψ)]
  calc
    _ = ∫ p in polarCoord.target, -(polarDirectional ψ polarUnit p) / (2 * Real.pi) := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem polarCoord.open_target.measurableSet] with p hp
      exact polar_curl_kernel p.1 p.2 hp.1
    _ = -(∫ p in polarCoord.target, polarDirectional ψ polarUnit p) / (2 * Real.pi) := by
      rw [integral_div, integral_neg]
    _ = ψ 0 := by
      rw [integral_polar_radialDirectional hψ hs]
      field_simp [Real.pi_ne_zero]

lemma hasDerivAt_polarUnit (θ : ℝ) : HasDerivAt polarUnit (perpJ (polarUnit θ)) θ := by
  have he : polarUnit = fun a => Real.cos a • EuclideanSpace.single 0 (1 : ℝ) +
      Real.sin a • EuclideanSpace.single 1 (1 : ℝ) := by
    funext a
    ext i
    fin_cases i <;> simp [polarUnit, torusVec, EuclideanSpace.single_apply]
  have hd := ((Real.hasDerivAt_cos θ).smul_const
    (EuclideanSpace.single (0 : Fin 2) (1 : ℝ))).add
    ((Real.hasDerivAt_sin θ).smul_const (EuclideanSpace.single (1 : Fin 2) (1 : ℝ)))
  change HasDerivAt (fun a => Real.cos a • EuclideanSpace.single (0 : Fin 2) (1 : ℝ) +
    Real.sin a • EuclideanSpace.single (1 : Fin 2) (1 : ℝ)) _ θ at hd
  rw [← he] at hd
  convert hd using 1
  ext i
  fin_cases i <;> simp [perpJ, polarUnit, torusVec, EuclideanSpace.single_apply]

lemma hasDerivAt_polarPoint_angle (r θ : ℝ) :
    HasDerivAt (polarPoint r) (r • perpJ (polarUnit θ)) θ :=
  (hasDerivAt_polarUnit θ).const_smul r

lemma hasDerivAt_test_polar_angle {ψ : R2 → ℝ} (hψ : ContDiff ℝ 1 ψ) (r θ : ℝ) :
    HasDerivAt (fun a => ψ (polarPoint r a))
      (r * polarDirectional ψ (fun a => perpJ (polarUnit a)) (r, θ)) θ := by
  simpa only [Function.comp_def, polarDirectional, map_smul, smul_eq_mul] using
    (hψ.differentiable one_ne_zero (polarPoint r θ)).hasFDerivAt.comp_hasDerivAt θ
      (hasDerivAt_polarPoint_angle r θ)

lemma continuous_polarPerpUnit : Continuous (fun a => perpJ (polarUnit a)) :=
  perpJL.continuous.comp continuous_polarUnit

lemma integral_polar_angularDerivative {ψ : R2 → ℝ} (hψ : ContDiff ℝ 1 ψ)
    {r : ℝ} (hr : 0 < r) :
    (∫ θ in Ioo (-Real.pi) Real.pi,
      polarDirectional ψ (fun a => perpJ (polarUnit a)) (r, θ)) = 0 := by
  have hcont : Continuous (fun θ =>
      r * polarDirectional ψ (fun a => perpJ (polarUnit a)) (r, θ)) :=
    continuous_const.mul ((continuous_polarDirectional hψ continuous_polarPerpUnit).comp
      (continuous_const.prodMk continuous_id))
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun θ _ => hasDerivAt_test_polar_angle hψ r θ) (hcont.intervalIntegrable (-Real.pi) Real.pi)
  have hend : polarPoint r Real.pi = polarPoint r (-Real.pi) := by
    ext i
    fin_cases i <;> simp [polarPoint, polarUnit, torusVec]
  rw [hend, sub_self, intervalIntegral.integral_const_mul] at hftc
  rw [setIntegral_congr_set Ioo_ae_eq_Ioc,
    ← intervalIntegral.integral_of_le (neg_le_self Real.pi_pos.le)]
  exact (mul_eq_zero.mp hftc).resolve_left hr.ne'

lemma polar_div_kernel {ψ : R2 → ℝ} (r θ : ℝ) (hr : 0 < r) :
    r * kernelDivTest ψ (polarPoint r θ) =
      polarDirectional ψ (fun a => perpJ (polarUnit a)) (r, θ) / (2 * Real.pi) := by
  rw [polarDirectional, fderiv_apply_eq_sum_pd]
  simp only [kernelDivTest, Fin.sum_univ_two]
  simp only [kernelK, PiLp.smul_apply, smul_eq_mul, norm_polarPoint, abs_of_pos hr]
  change r * ((2 * Real.pi * r ^ 2)⁻¹ * (-(r * Real.sin θ)) * pd 0 ψ (polarPoint r θ) +
    (2 * Real.pi * r ^ 2)⁻¹ * (r * Real.cos θ) * pd 1 ψ (polarPoint r θ)) =
      ((-Real.sin θ) * pd 0 ψ (polarPoint r θ) +
        Real.cos θ * pd 1 ψ (polarPoint r θ)) / (2 * Real.pi)
  field_simp [hr.ne', Real.pi_ne_zero]

lemma measurable_kernelDivTest {ψ : R2 → ℝ} (hψ : ContDiff ℝ 1 ψ) :
    Measurable (kernelDivTest ψ) := by
  have hK (i : Fin 2) : Measurable (fun x => kernelK x i) :=
    (EuclideanSpace.proj i : R2 →L[ℝ] ℝ).continuous.measurable.comp measurable_kernelK
  change Measurable (fun x => ∑ i : Fin 2, kernelK x i * pd i ψ x)
  simp only [Fin.sum_univ_two]
  exact ((hK 0).mul (continuous_pd_of_contDiff_one ψ hψ 0).measurable).add
      ((hK 1).mul (continuous_pd_of_contDiff_one ψ hψ 1).measurable)

lemma integrable_polar_kernelDivTest {ψ : R2 → ℝ} (hψ : ContDiff ℝ 1 ψ)
    (hs : HasCompactSupport ψ) :
    IntegrableOn (fun p : ℝ × ℝ => p.1 * kernelDivTest ψ (polarPoint p.1 p.2))
      polarCoord.target := by
  apply ((integrableOn_polarDirectional hψ hs continuous_polarPerpUnit).div_const
    (2 * Real.pi)).congr
  filter_upwards [ae_restrict_mem polarCoord.open_target.measurableSet] with p hp
  exact (polar_div_kernel p.1 p.2 hp.1).symm

theorem integrable_kernelDivTest {ψ : R2 → ℝ} (hψ : ContDiff ℝ 1 ψ)
    (hs : HasCompactSupport ψ) : Integrable (kernelDivTest ψ) :=
  integrable_of_polarR2 (measurable_kernelDivTest hψ).aestronglyMeasurable
    (integrable_polar_kernelDivTest hψ hs)

/-- The same genuine singular kernel is distributionally divergence free. -/
theorem kernelK_weak_divergence {ψ : R2 → ℝ} (hψ : ContDiff ℝ 1 ψ)
    (hs : HasCompactSupport ψ) : (∫ x, ∑ i : Fin 2, kernelK x i * pd i ψ x) = 0 := by
  change (∫ x, kernelDivTest ψ x) = 0
  rw [← integral_polarR2 (kernelDivTest ψ)]
  have hD : (∫ p in polarCoord.target,
      polarDirectional ψ (fun a => perpJ (polarUnit a)) p) = 0 := by
    have hI := integrableOn_polarDirectional hψ hs continuous_polarPerpUnit
    have hIprod : Integrable (polarDirectional ψ (fun a => perpJ (polarUnit a)))
        ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioo (-Real.pi) Real.pi))) := by
      rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
      exact hI
    calc
      _ = ∫ r in Ioi (0 : ℝ), ∫ θ in Ioo (-Real.pi) Real.pi,
          polarDirectional ψ (fun a => perpJ (polarUnit a)) (r, θ) := by
        change (∫ p in Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi,
          polarDirectional ψ (fun a => perpJ (polarUnit a)) p) = _
        rw [Measure.volume_eq_prod, ← Measure.prod_restrict]
        exact integral_prod _ hIprod
      _ = 0 := by
        apply integral_eq_zero_of_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
        exact integral_polar_angularDerivative hψ hr
  calc
    _ = ∫ p in polarCoord.target,
        polarDirectional ψ (fun a => perpJ (polarUnit a)) p / (2 * Real.pi) := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem polarCoord.open_target.measurableSet] with p hp
      exact polar_div_kernel p.1 p.2 hp.1
    _ = 0 := by rw [integral_div, hD, zero_div]

def radialKernelCutoff (χ : ℝ → ℝ) (x : R2) : ℝ := χ (‖x‖ ^ 2)

def cutoffKernelK (χ : ℝ → ℝ) (x : R2) : R2 := radialKernelCutoff χ x • kernelK x

def radialKernelError (χ : ℝ → ℝ) (x : R2) : ℝ := deriv χ (‖x‖ ^ 2) / Real.pi

lemma contDiff_radialKernelCutoff {χ : ℝ → ℝ} (hχ : ContDiff ℝ 1 χ) :
    ContDiff ℝ 1 (radialKernelCutoff χ) := hχ.comp (contDiff_norm_sq ℝ)

lemma pd_radialKernelCutoff {χ : ℝ → ℝ} (hχ : ContDiff ℝ 1 χ) (i : Fin 2) (x : R2) :
    pd i (radialKernelCutoff χ) x = 2 * deriv χ (‖x‖ ^ 2) * x i := by
  have hd := (hχ.differentiable one_ne_zero (‖x‖ ^ 2)).hasDerivAt.comp_hasFDerivAt x
    (hasStrictFDerivAt_norm_sq x).hasFDerivAt
  change HasFDerivAt (radialKernelCutoff χ) _ x at hd
  rw [pd, hd.fderiv]
  simp [EuclideanSpace.inner_single_right]
  ring

lemma kernelK_radial_cutoff_curl {χ : ℝ → ℝ} (hχ : ContDiff ℝ 1 χ)
    {x : R2} (hx : x ≠ 0) :
    kernelK x 0 * pd 1 (radialKernelCutoff χ) x -
      kernelK x 1 * pd 0 (radialKernelCutoff χ) x = -radialKernelError χ x := by
  rw [pd_radialKernelCutoff hχ, pd_radialKernelCutoff hχ]
  simp only [kernelK, PiLp.smul_apply, smul_eq_mul]
  change (2 * Real.pi * ‖x‖ ^ 2)⁻¹ * (-x 1) * (2 * deriv χ (‖x‖ ^ 2) * x 1) -
    (2 * Real.pi * ‖x‖ ^ 2)⁻¹ * x 0 * (2 * deriv χ (‖x‖ ^ 2) * x 0) =
      -(deriv χ (‖x‖ ^ 2) / Real.pi)
  have hn : ‖x‖ ^ 2 = x 0 ^ 2 + x 1 ^ 2 := by
    simp [EuclideanSpace.norm_sq_eq, Fin.sum_univ_two]
  field_simp [norm_ne_zero_iff.mpr hx, Real.pi_ne_zero]
  rw [hn]
  ring

lemma kernelK_radial_cutoff_div {χ : ℝ → ℝ} (hχ : ContDiff ℝ 1 χ) (x : R2) :
    (∑ i : Fin 2, kernelK x i * pd i (radialKernelCutoff χ) x) = 0 := by
  simp only [Fin.sum_univ_two, pd_radialKernelCutoff hχ, kernelK, PiLp.smul_apply, smul_eq_mul]
  change (2 * Real.pi * ‖x‖ ^ 2)⁻¹ * (-x 1) * (2 * deriv χ (‖x‖ ^ 2) * x 0) +
    (2 * Real.pi * ‖x‖ ^ 2)⁻¹ * x 0 * (2 * deriv χ (‖x‖ ^ 2) * x 1) = 0
  ring

lemma kernelCurlTest_cutoff_product {χ : ℝ → ℝ} (hχ : ContDiff ℝ 1 χ)
    {ψ : R2 → ℝ} (hψ : ContDiff ℝ 1 ψ) {x : R2} (hx : x ≠ 0) :
    kernelCurlTest (fun y => radialKernelCutoff χ y * ψ y) x =
      ((cutoffKernelK χ x) 0 * pd 1 ψ x - (cutoffKernelK χ x) 1 * pd 0 ψ x) -
        radialKernelError χ x * ψ x := by
  have hd := kernelK_radial_cutoff_curl hχ hx
  unfold kernelCurlTest cutoffKernelK
  rw [torus_pd_mul _ _ x ((contDiff_radialKernelCutoff hχ).differentiable one_ne_zero x)
    (hψ.differentiable one_ne_zero x),
    torus_pd_mul _ _ x ((contDiff_radialKernelCutoff hχ).differentiable one_ne_zero x)
      (hψ.differentiable one_ne_zero x)]
  simp only [PiLp.smul_apply, smul_eq_mul]
  linear_combination ψ x * hd

lemma continuous_radialKernelError {χ : ℝ → ℝ} (hχ : ContDiff ℝ 1 χ) :
    Continuous (radialKernelError χ) :=
  ((hχ.continuous_deriv le_rfl).comp (continuous_norm.pow 2)).div_const Real.pi

/-- Multiplying the genuine singular kernel by a smooth radial cutoff
produces exactly the Dirac source plus its actual smooth radial error. -/
theorem cutoffKernelK_weak_curl {χ : ℝ → ℝ} (hχ : ContDiff ℝ 1 χ)
    {ψ : R2 → ℝ} (hψ : ContDiff ℝ 1 ψ) (hs : HasCompactSupport ψ) :
    (∫ x, (cutoffKernelK χ x) 0 * pd 1 ψ x - (cutoffKernelK χ x) 1 * pd 0 ψ x) =
      χ 0 * ψ 0 + ∫ x, radialKernelError χ x * ψ x := by
  let Φ : R2 → ℝ := fun x => radialKernelCutoff χ x * ψ x
  have hΦ : ContDiff ℝ 1 Φ := (contDiff_radialKernelCutoff hχ).mul hψ
  have hsΦ : HasCompactSupport Φ := hs.mul_left
  have hI := integrable_kernelCurlTest hΦ hsΦ
  have hJ : Integrable (fun x => radialKernelError χ x * ψ x) :=
    ((continuous_radialKernelError hχ).mul hψ.continuous).integrable_of_hasCompactSupport hs.mul_left
  have he : (fun x => (cutoffKernelK χ x) 0 * pd 1 ψ x -
      (cutoffKernelK χ x) 1 * pd 0 ψ x) =ᵐ[volume]
      (fun x => kernelCurlTest Φ x + radialKernelError χ x * ψ x) := by
    filter_upwards [volume.ae_ne (0 : R2)] with x hx
    have hp := kernelCurlTest_cutoff_product hχ hψ hx
    change kernelCurlTest Φ x = _ at hp
    linarith
  rw [integral_congr_ae he, integral_add hI hJ,
    show (∫ x, kernelCurlTest Φ x) = Φ 0 from kernelK_weak_curl hΦ hsΦ]
  simp only [Φ, radialKernelCutoff, norm_zero, zero_pow (by norm_num : 2 ≠ 0)]

theorem cutoffKernelK_weak_divergence {χ : ℝ → ℝ} (hχ : ContDiff ℝ 1 χ)
    {ψ : R2 → ℝ} (hψ : ContDiff ℝ 1 ψ) (hs : HasCompactSupport ψ) :
    (∫ x, ∑ i : Fin 2, (cutoffKernelK χ x) i * pd i ψ x) = 0 := by
  let Φ : R2 → ℝ := fun x => radialKernelCutoff χ x * ψ x
  have hΦ : ContDiff ℝ 1 Φ := (contDiff_radialKernelCutoff hχ).mul hψ
  have hsΦ : HasCompactSupport Φ := hs.mul_left
  have he (x : R2) : (∑ i : Fin 2, (cutoffKernelK χ x) i * pd i ψ x) = kernelDivTest Φ x := by
    have hd := kernelK_radial_cutoff_div hχ x
    simp only [Fin.sum_univ_two] at hd
    simp only [kernelDivTest, Φ, Fin.sum_univ_two, cutoffKernelK, PiLp.smul_apply, smul_eq_mul]
    rw [torus_pd_mul _ _ x ((contDiff_radialKernelCutoff hχ).differentiable one_ne_zero x)
      (hψ.differentiable one_ne_zero x),
      torus_pd_mul _ _ x ((contDiff_radialKernelCutoff hχ).differentiable one_ne_zero x)
        (hψ.differentiable one_ne_zero x)]
    linear_combination -ψ x * hd
  simp_rw [he]
  exact kernelK_weak_divergence hΦ hsΦ

lemma hasCompactSupport_radialKernelError {χ : ℝ → ℝ} (hs : HasCompactSupport χ) :
    HasCompactSupport (radialKernelError χ) := by
  obtain ⟨R, hR, hzero⟩ := hs.deriv.exists_pos_le_norm
  apply HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0 : R2) (R + 1))
  intro x hx
  rw [mem_closedBall_zero_iff]
  by_contra hn
  have hb : R ≤ ‖x‖ ^ 2 := by have := norm_nonneg x; nlinarith
  have hd : deriv χ (‖x‖ ^ 2) = 0 :=
    hzero _ (by simpa only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ‖x‖)] using hb)
  exact hx (by simp only [radialKernelError, hd, zero_div])

lemma contDiff_radialKernelError {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) :
    ContDiff ℝ ∞ (radialKernelError χ) := by
  have hd : ContDiff ℝ ∞ (deriv χ) := (contDiff_infty_iff_deriv.mp hχ).2
  exact (hd.comp (contDiff_norm_sq ℝ)).div_const Real.pi

lemma radialKernelError_eq_zero_near {χ : ℝ → ℝ} {ε : ℝ} (hε : 0 < ε)
    (hone : ∀ s ∈ Ioo (-ε) ε, χ s = 1) {x : R2} (hx : ‖x‖ ^ 2 < ε) :
    radialKernelError χ x = 0 := by
  have hmem : ‖x‖ ^ 2 ∈ Ioo (-ε) ε := ⟨by nlinarith [sq_nonneg ‖x‖], hx⟩
  have he : χ =ᶠ[𝓝 (‖x‖ ^ 2)] fun _ => (1 : ℝ) := by
    filter_upwards [isOpen_Ioo.mem_nhds hmem] with s hs
    exact hone s hs
  have hd := he.deriv_eq
  simp only [deriv_const] at hd
  simp only [radialKernelError, hd, zero_div]

lemma hasCompactSupport_comp_square {χ : ℝ → ℝ} (hs : HasCompactSupport χ) :
    HasCompactSupport (fun r : ℝ => χ (r ^ 2)) := by
  obtain ⟨R, hR, hzero⟩ := hs.exists_pos_le_norm
  apply HasCompactSupport.of_support_subset_isCompact (isCompact_Icc : IsCompact (Icc (-(R + 1)) (R + 1)))
  intro r hr
  by_contra hn
  have hab : R + 1 < |r| := by
    rw [mem_Icc, ← abs_le] at hn
    exact lt_of_not_ge hn
  have hb : R ≤ r ^ 2 := by
    have hsq : |r| ^ 2 = r ^ 2 := sq_abs r
    nlinarith [abs_nonneg r]
  exact hr (hzero _ (by simpa only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg r)] using hb))

lemma deriv_comp_square {χ : ℝ → ℝ} (hχ : ContDiff ℝ 1 χ) (r : ℝ) :
    deriv (fun s : ℝ => χ (s ^ 2)) r = 2 * r * deriv χ (r ^ 2) := by
  have hd := (hχ.differentiable one_ne_zero (r ^ 2)).hasDerivAt.comp r ((hasDerivAt_id r).pow 2)
  change HasDerivAt (fun s : ℝ => χ (s ^ 2)) _ r at hd
  rw [hd.deriv]
  simp only [id_eq]
  ring

/-- The correction has exactly the compensating total mass. For a cutoff
equal to one near zero, this is the required mass `-1`. -/
theorem integral_radialKernelError {χ : ℝ → ℝ} (hχ : ContDiff ℝ 1 χ)
    (hs : HasCompactSupport χ) : (∫ x, radialKernelError χ x) = -χ 0 := by
  have hf : ContDiff ℝ 1 (fun r : ℝ => χ (r ^ 2)) := hχ.comp (contDiff_id.pow 2)
  have hftc := HasCompactSupport.integral_Ioi_deriv_eq hf (hasCompactSupport_comp_square hs) 0
  simp only [zero_pow (by norm_num : 2 ≠ 0)] at hftc
  have hangle : (∫ θ in Ioo (-Real.pi) Real.pi, (1 : ℝ)) = 2 * Real.pi := by
    rw [setIntegral_congr_set Ioo_ae_eq_Ioc,
      ← intervalIntegral.integral_of_le (neg_le_self Real.pi_pos.le), intervalIntegral.integral_const]
    simp only [smul_eq_mul]
    ring
  rw [← integral_polarR2 (radialKernelError χ)]
  calc
    _ = ∫ p in polarCoord.target,
        (deriv (fun r : ℝ => χ (r ^ 2)) p.1 / (2 * Real.pi)) * (1 : ℝ) := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem polarCoord.open_target.measurableSet] with p hp
      have hp0 : 0 < p.1 := hp.1
      simp only [smul_eq_mul, radialKernelError, norm_polarPoint, abs_of_pos hp0,
        deriv_comp_square hχ, mul_one]
      ring
    _ = (∫ r in Ioi (0 : ℝ), deriv (fun s : ℝ => χ (s ^ 2)) r / (2 * Real.pi)) *
        (∫ θ in Ioo (-Real.pi) Real.pi, (1 : ℝ)) := by
      change (∫ p in Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi,
        (deriv (fun r : ℝ => χ (r ^ 2)) p.1 / (2 * Real.pi)) * (1 : ℝ)) = _
      rw [Measure.volume_eq_prod]
      exact setIntegral_prod_mul
        (fun r : ℝ => deriv (fun s : ℝ => χ (s ^ 2)) r / (2 * Real.pi))
        (fun _ : ℝ => (1 : ℝ)) (Ioi (0 : ℝ)) (Ioo (-Real.pi) Real.pi)
    _ = -χ 0 := by
      rw [integral_div, hftc, hangle]
      field_simp [Real.pi_ne_zero]

/-- A concrete smooth cutoff on squared radius: one up to `1/4`, zero
from `1` onwards. Consequently the physical inner and outer radii are
`1/2` and `1`. -/
def planarCutoffBump : ContDiffBump (0 : ℝ) where
  rIn := 1 / 4
  rOut := 1
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num

def planarCutoff : ℝ → ℝ := planarCutoffBump

lemma contDiff_planarCutoff : ContDiff ℝ ∞ planarCutoff := planarCutoffBump.contDiff

lemma hasCompactSupport_planarCutoff : HasCompactSupport planarCutoff :=
  planarCutoffBump.hasCompactSupport

lemma planarCutoff_eq_one {s : ℝ} (hs : |s| ≤ 1 / 4) : planarCutoff s = 1 := by
  apply planarCutoffBump.one_of_mem_closedBall
  change s ∈ closedBall (0 : ℝ) (1 / 4)
  simpa only [mem_closedBall_zero_iff, Real.norm_eq_abs] using hs

lemma planarCutoff_eq_zero {s : ℝ} (hs : 1 ≤ |s|) : planarCutoff s = 0 := by
  apply planarCutoffBump.zero_of_le_dist
  change (1 : ℝ) ≤ dist s 0
  simpa only [dist_zero_right, Real.norm_eq_abs] using hs

@[simp] lemma planarCutoff_zero : planarCutoff 0 = 1 := planarCutoff_eq_one (by norm_num)

def localPlanarKernel : R2 → R2 := cutoffKernelK planarCutoff

def localPlanarKernelError : R2 → ℝ := radialKernelError planarCutoff

lemma contDiff_localPlanarKernelError : ContDiff ℝ ∞ localPlanarKernelError :=
  contDiff_radialKernelError contDiff_planarCutoff

lemma hasCompactSupport_localPlanarKernelError : HasCompactSupport localPlanarKernelError :=
  hasCompactSupport_radialKernelError hasCompactSupport_planarCutoff

lemma localPlanarKernelError_eq_zero_of_norm_lt_half {x : R2} (hx : ‖x‖ < 1 / 2) :
    localPlanarKernelError x = 0 := by
  apply radialKernelError_eq_zero_near (ε := (1 / 4 : ℝ)) (by norm_num)
  · intro s hs
    exact planarCutoff_eq_one (abs_le.mpr ⟨hs.1.le, hs.2.le⟩)
  · have := norm_nonneg x
    nlinarith

lemma localPlanarKernelError_eq_zero_of_one_lt_norm {x : R2} (hx : 1 < ‖x‖) :
    localPlanarKernelError x = 0 := by
  have hsq : 1 < ‖x‖ ^ 2 := by have := norm_nonneg x; nlinarith
  have he : planarCutoff =ᶠ[𝓝 (‖x‖ ^ 2)] fun _ => (0 : ℝ) := by
    filter_upwards [isOpen_Ioi.mem_nhds hsq] with s hs
    exact planarCutoff_eq_zero (hs.le.trans (le_abs_self s))
  have hd := he.deriv_eq
  simp only [deriv_const] at hd
  simp only [localPlanarKernelError, radialKernelError, hd, zero_div]

lemma localPlanarKernelError_eq_zero_of_one_le_norm {x : R2} (hx : 1 ≤ ‖x‖) :
    localPlanarKernelError x = 0 := by
  have hsq : 1 ≤ |‖x‖ ^ 2| := by
    rw [abs_of_nonneg (sq_nonneg ‖x‖)]
    nlinarith [norm_nonneg x]
  have hz : planarCutoff (‖x‖ ^ 2) = 0 := planarCutoff_eq_zero hsq
  have hmin : IsLocalMin planarCutoff (‖x‖ ^ 2) := by
    apply Eventually.of_forall
    intro s
    rw [hz]
    exact planarCutoffBump.nonneg
  simp only [localPlanarKernelError, radialKernelError, hmin.deriv_eq_zero, zero_div]

lemma support_localPlanarKernelError_subset_ball :
    Function.support localPlanarKernelError ⊆ ball (0 : R2) 1 := by
  intro x hx
  rw [mem_ball_zero_iff]
  by_contra hn
  exact hx (localPlanarKernelError_eq_zero_of_one_le_norm (le_of_not_gt hn))

lemma support_localPlanarKernelError_subset :
    Function.support localPlanarKernelError ⊆ closedBall (0 : R2) 1 := by
  intro x hx
  rw [mem_closedBall_zero_iff]
  by_contra hn
  exact hx (localPlanarKernelError_eq_zero_of_one_lt_norm (lt_of_not_ge hn))

lemma localPlanarKernel_eq_zero_of_one_le_norm {x : R2} (hx : 1 ≤ ‖x‖) :
    localPlanarKernel x = 0 := by
  have hsq : 1 ≤ |‖x‖ ^ 2| := by
    rw [abs_of_nonneg (sq_nonneg ‖x‖)]
    nlinarith [norm_nonneg x]
  change planarCutoff (‖x‖ ^ 2) • kernelK x = 0
  rw [planarCutoff_eq_zero hsq, zero_smul]

lemma support_localPlanarKernel_subset :
    Function.support localPlanarKernel ⊆ closedBall (0 : R2) 1 := by
  intro x hx
  rw [mem_closedBall_zero_iff]
  by_contra hn
  exact hx (localPlanarKernel_eq_zero_of_one_le_norm (le_of_not_ge hn))

lemma integral_localPlanarKernelError : (∫ x, localPlanarKernelError x) = -1 := by
  simpa only [localPlanarKernelError, planarCutoff_zero] using
    integral_radialKernelError (contDiff_planarCutoff.of_le (by simp)) hasCompactSupport_planarCutoff

theorem localPlanarKernel_weak_curl {ψ : R2 → ℝ} (hψ : ContDiff ℝ 1 ψ)
    (hs : HasCompactSupport ψ) :
    (∫ x, localPlanarKernel x 0 * pd 1 ψ x - localPlanarKernel x 1 * pd 0 ψ x) =
      ψ 0 + ∫ x, localPlanarKernelError x * ψ x := by
  simpa only [localPlanarKernel, localPlanarKernelError, planarCutoff_zero, one_mul] using
    cutoffKernelK_weak_curl (contDiff_planarCutoff.of_le (by simp)) hψ hs

theorem localPlanarKernel_weak_divergence {ψ : R2 → ℝ} (hψ : ContDiff ℝ 1 ψ)
    (hs : HasCompactSupport ψ) :
    (∫ x, ∑ i : Fin 2, localPlanarKernel x i * pd i ψ x) = 0 :=
  cutoffKernelK_weak_divergence (contDiff_planarCutoff.of_le (by simp)) hψ hs

lemma hasCompactSupport_radialKernelCutoff {χ : ℝ → ℝ} (hs : HasCompactSupport χ) :
    HasCompactSupport (radialKernelCutoff χ) := by
  obtain ⟨R, hR, hzero⟩ := hs.exists_pos_le_norm
  apply HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0 : R2) (R + 1))
  intro x hx
  rw [mem_closedBall_zero_iff]
  by_contra hn
  have hb : R ≤ ‖x‖ ^ 2 := by have := norm_nonneg x; nlinarith
  exact hx (hzero _ (by simpa only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ‖x‖)] using hb))

/-- A compact radial cutoff permits arbitrary global `C¹` tests, in
particular periodic tests whose supports need not be compact. -/
theorem cutoffKernelK_weak_curl_global {χ : ℝ → ℝ} (hχ : ContDiff ℝ 1 χ)
    (hsχ : HasCompactSupport χ) {ψ : R2 → ℝ} (hψ : ContDiff ℝ 1 ψ) :
    (∫ x, (cutoffKernelK χ x) 0 * pd 1 ψ x - (cutoffKernelK χ x) 1 * pd 0 ψ x) =
      χ 0 * ψ 0 + ∫ x, radialKernelError χ x * ψ x := by
  let Φ : R2 → ℝ := fun x => radialKernelCutoff χ x * ψ x
  have hΦ : ContDiff ℝ 1 Φ := (contDiff_radialKernelCutoff hχ).mul hψ
  have hsΦ : HasCompactSupport Φ := (hasCompactSupport_radialKernelCutoff hsχ).mul_right
  have hI := integrable_kernelCurlTest hΦ hsΦ
  have hJ : Integrable (fun x => radialKernelError χ x * ψ x) :=
    ((continuous_radialKernelError hχ).mul hψ.continuous).integrable_of_hasCompactSupport
      (hasCompactSupport_radialKernelError hsχ).mul_right
  have he : (fun x => (cutoffKernelK χ x) 0 * pd 1 ψ x -
      (cutoffKernelK χ x) 1 * pd 0 ψ x) =ᵐ[volume]
      (fun x => kernelCurlTest Φ x + radialKernelError χ x * ψ x) := by
    filter_upwards [volume.ae_ne (0 : R2)] with x hx
    have hp := kernelCurlTest_cutoff_product hχ hψ hx
    change kernelCurlTest Φ x = _ at hp
    linarith
  rw [integral_congr_ae he, integral_add hI hJ,
    show (∫ x, kernelCurlTest Φ x) = Φ 0 from kernelK_weak_curl hΦ hsΦ]
  simp only [Φ, radialKernelCutoff, norm_zero, zero_pow (by norm_num : 2 ≠ 0)]

theorem cutoffKernelK_weak_divergence_global {χ : ℝ → ℝ} (hχ : ContDiff ℝ 1 χ)
    (hsχ : HasCompactSupport χ) {ψ : R2 → ℝ} (hψ : ContDiff ℝ 1 ψ) :
    (∫ x, ∑ i : Fin 2, (cutoffKernelK χ x) i * pd i ψ x) = 0 := by
  let Φ : R2 → ℝ := fun x => radialKernelCutoff χ x * ψ x
  have hΦ : ContDiff ℝ 1 Φ := (contDiff_radialKernelCutoff hχ).mul hψ
  have hsΦ : HasCompactSupport Φ := (hasCompactSupport_radialKernelCutoff hsχ).mul_right
  have he (x : R2) : (∑ i : Fin 2, (cutoffKernelK χ x) i * pd i ψ x) = kernelDivTest Φ x := by
    have hd := kernelK_radial_cutoff_div hχ x
    simp only [Fin.sum_univ_two] at hd
    simp only [kernelDivTest, Φ, Fin.sum_univ_two, cutoffKernelK, PiLp.smul_apply, smul_eq_mul]
    rw [torus_pd_mul _ _ x ((contDiff_radialKernelCutoff hχ).differentiable one_ne_zero x)
      (hψ.differentiable one_ne_zero x),
      torus_pd_mul _ _ x ((contDiff_radialKernelCutoff hχ).differentiable one_ne_zero x)
        (hψ.differentiable one_ne_zero x)]
    linear_combination -ψ x * hd
  simp_rw [he]
  exact kernelK_weak_divergence hΦ hsΦ

theorem localPlanarKernel_weak_curl_global {ψ : R2 → ℝ} (hψ : ContDiff ℝ 1 ψ) :
    (∫ x, localPlanarKernel x 0 * pd 1 ψ x - localPlanarKernel x 1 * pd 0 ψ x) =
      ψ 0 + ∫ x, localPlanarKernelError x * ψ x := by
  simpa only [localPlanarKernel, localPlanarKernelError, planarCutoff_zero, one_mul] using
    cutoffKernelK_weak_curl_global (contDiff_planarCutoff.of_le (by simp))
      hasCompactSupport_planarCutoff hψ

theorem localPlanarKernel_weak_divergence_global {ψ : R2 → ℝ} (hψ : ContDiff ℝ 1 ψ) :
    (∫ x, ∑ i : Fin 2, localPlanarKernel x i * pd i ψ x) = 0 :=
  cutoffKernelK_weak_divergence_global (contDiff_planarCutoff.of_le (by simp))
    hasCompactSupport_planarCutoff hψ

end Euler2D

end

