module

public import RequestProject.Euler.SmoothFlowDerivative
public import Mathlib.MeasureTheory.Function.Jacobian

/-!
# The actual Jacobian and planar volume of smooth particle flows
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology Metric
open scoped NNReal ContDiff

namespace Euler2D

def linearDet2 (A : R2 →L[ℝ] R2) : ℝ :=
  A (EuclideanSpace.single 0 1) 0 * A (EuclideanSpace.single 1 1) 1 -
    A (EuclideanSpace.single 1 1) 0 * A (EuclideanSpace.single 0 1) 1

lemma linearDet2_eq_det (A : R2 →L[ℝ] R2) : linearDet2 A = A.det := by
  change linearDet2 A = LinearMap.det (A : R2 →ₗ[ℝ] R2)
  rw [← LinearMap.det_toMatrix (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis
    (A : R2 →ₗ[ℝ] R2)]
  rw [Matrix.det_fin_two]
  rfl

@[simp] lemma linearDet2_id : linearDet2 (ContinuousLinearMap.id ℝ R2) = 1 := by
  simp [linearDet2, EuclideanSpace.single_apply]

lemma clm_apply_coordinate_two (B : R2 →L[ℝ] R2) (x : R2) (i : Fin 2) :
    B x i = x 0 * B (EuclideanSpace.single 0 1) i +
      x 1 * B (EuclideanSpace.single 1 1) i := by
  have hx : x = x 0 • EuclideanSpace.single 0 1 + x 1 • EuclideanSpace.single 1 1 := by
    ext j
    fin_cases j <;> simp [EuclideanSpace.single_apply]
  conv_lhs => rw [hx]
  simp only [map_add, map_smul, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]

theorem hasDerivAt_linearDet2_variational {A : ℝ → R2 →L[ℝ] R2}
    {B : R2 →L[ℝ] R2} {t : ℝ} (hA : HasDerivAt A (B.comp (A t)) t) :
    HasDerivAt (fun u => linearDet2 (A u))
      ((B (EuclideanSpace.single 0 1) 0 + B (EuclideanSpace.single 1 1) 1) * linearDet2 (A t)) t := by
  have hd (j i : Fin 2) : HasDerivAt (fun u => A u (EuclideanSpace.single j 1) i)
      (B (A t (EuclideanSpace.single j 1)) i) t := by
    have hentry := (EuclideanSpace.proj i : R2 →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivAt t
      (hA.clm_apply (hasDerivAt_const t (EuclideanSpace.single j 1)))
    simpa only [Function.comp_def, EuclideanSpace.coe_proj,
      ContinuousLinearMap.comp_apply, map_zero, add_zero] using hentry
  have hdet := ((hd 0 0).mul (hd 1 1)).sub ((hd 1 0).mul (hd 0 1))
  convert hdet using 1
  · funext u
    simp only [linearDet2, Pi.sub_apply, Pi.mul_apply]
  · simp only [linearDet2]
    rw [clm_apply_coordinate_two B (A t (EuclideanSpace.single 0 1)) 0,
      clm_apply_coordinate_two B (A t (EuclideanSpace.single 0 1)) 1,
      clm_apply_coordinate_two B (A t (EuclideanSpace.single 1 1)) 0,
      clm_apply_coordinate_two B (A t (EuclideanSpace.single 1 1)) 1]
    ring

theorem linearDet2_variational_eq_one {A B : ℝ → R2 →L[ℝ] R2}
    {T : ℝ} (_hT : 0 ≤ T) (hA0 : A 0 = ContinuousLinearMap.id ℝ R2)
    (hAd : ∀ t ∈ Icc (0 : ℝ) T, HasDerivAt A ((B t).comp (A t)) t)
    (htrace : ∀ t ∈ Icc (0 : ℝ) T,
      B t (EuclideanSpace.single 0 1) 0 + B t (EuclideanSpace.single 1 1) 1 = 0)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) : linearDet2 (A t) = 1 := by
  have hd (u : ℝ) (hu : u ∈ Icc (0 : ℝ) T) :
      HasDerivAt (fun r => linearDet2 (A r)) 0 u := by
    simpa only [htrace u hu, zero_mul] using hasDerivAt_linearDet2_variational (hAd u hu)
  exact eq_of_has_deriv_right_eq
    (fun u hu => (hd u ⟨hu.1, hu.2.le⟩).hasDerivWithinAt)
    (fun u hu => (hasDerivAt_const u (1 : ℝ)).hasDerivWithinAt)
    (HasDerivAt.continuousOn hd) continuous_const.continuousOn
    (by simp only [hA0, linearDet2_id]) t ht

theorem det_fderiv_boundedParticleForward {v : ℝ → R2 → R2} {K M : ℝ≥0}
    (hv : IsBoundedLipschitzVelocity v K M)
    (hC1 : ContDiff ℝ 1 (Function.uncurry v)) {T : ℝ} (hT : 0 ≤ T)
    (hdiv : ∀ t x, pd 0 (v t) x 0 + pd 1 (v t) x 1 = 0)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) (a : R2) :
    (fderiv ℝ (boundedParticleForward hv hT t) a).det = 1 := by
  obtain ⟨A, hAc, hA0, hAd, hAf⟩ := exists_particleForward_spatial_derivative hv hC1 hT a
  rw [(hAf t ht).fderiv, ← linearDet2_eq_det]
  exact linearDet2_variational_eq_one hT hA0 hAd
    (fun u hu => hdiv u (boundedParticleForward hv hT u a)) ht

theorem measurePreserving_boundedParticleForward {v : ℝ → R2 → R2} {K M : ℝ≥0}
    (hv : IsBoundedLipschitzVelocity v K M)
    (hC1 : ContDiff ℝ 1 (Function.uncurry v)) {T : ℝ} (hT : 0 ≤ T)
    (hdiv : ∀ t x, pd 0 (v t) x 0 + pd 1 (v t) x 1 = 0)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    MeasurePreserving (boundedParticleForward hv hT t) volume volume := by
  let X := boundedParticleHomeomorph hv hT ⟨0, le_rfl, hT⟩ ⟨t, ht⟩
  have hX : (X : R2 → R2) = boundedParticleForward hv hT t := rfl
  have hdiff (a : R2) : DifferentiableAt ℝ (boundedParticleForward hv hT t) a := by
    obtain ⟨A, hAc, hA0, hAd, hAf⟩ := exists_particleForward_spatial_derivative hv hC1 hT a
    exact (hAf t ht).differentiableAt
  have hXm : Measurable (boundedParticleForward hv hT t) := by
    rw [← hX]; exact X.continuous.measurable
  refine ⟨hXm, ?_⟩
  apply Measure.ext
  intro s hs
  rw [Measure.map_apply hXm hs]
  have hp : MeasurableSet ((boundedParticleForward hv hT t) ⁻¹' s) :=
    hXm hs
  have himage : (boundedParticleForward hv hT t) '' ((boundedParticleForward hv hT t) ⁻¹' s) = s :=
    Set.image_preimage_eq s (by rw [← hX]; exact X.surjective)
  have hj := lintegral_abs_det_fderiv_eq_addHaar_image volume hp
    (fun a ha => (hdiff a).hasFDerivAt.hasFDerivWithinAt)
    (by rw [← hX]; exact X.injective.injOn)
  simpa only [det_fderiv_boundedParticleForward hv hC1 hT hdiv ht, abs_one,
    ENNReal.ofReal_one, lintegral_one, Measure.restrict_apply_univ, himage] using hj

theorem measurePreserving_boundedParticleBackward {v : ℝ → R2 → R2} {K M : ℝ≥0}
    (hv : IsBoundedLipschitzVelocity v K M)
    (hC1 : ContDiff ℝ 1 (Function.uncurry v)) {T : ℝ} (hT : 0 ≤ T)
    (hdiv : ∀ t x, pd 0 (v t) x 0 + pd 1 (v t) x 1 = 0)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    MeasurePreserving (boundedParticleBackward hv hT t) volume volume := by
  let X := boundedParticleHomeomorph hv hT ⟨0, le_rfl, hT⟩ ⟨t, ht⟩
  have hXm : MeasurePreserving (X : R2 → R2) volume volume :=
    measurePreserving_boundedParticleForward hv hC1 hT hdiv ht
  have heq : boundedParticleBackward hv hT t = (X.symm : R2 → R2) := by
    funext a
    simp only [boundedParticleBackward, projIcc_of_mem _ ht]
    rfl
  rw [heq]
  refine ⟨X.symm.continuous.measurable, ?_⟩
  calc
    Measure.map (X.symm : R2 → R2) volume =
        Measure.map (X.symm : R2 → R2) (Measure.map (X : R2 → R2) volume) :=
      congrArg (Measure.map (X.symm : R2 → R2)) hXm.map_eq.symm
    _ = Measure.map ((X.symm : R2 → R2) ∘ X) volume :=
      Measure.map_map X.symm.continuous.measurable X.continuous.measurable
    _ = volume := by
      have hc : (X.symm : R2 → R2) ∘ X = id := by funext a; exact X.symm_apply_apply a
      rw [hc, Measure.map_id]

end Euler2D

end
