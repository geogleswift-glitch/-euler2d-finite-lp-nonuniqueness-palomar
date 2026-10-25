module

public import RequestProject.Euler.PlanarConvolutionWeakDivergence

/-! The actual compact convolution divergence formula also holds
for a locally integrable singular field. This includes the genuine
Biot--Savart kernel at its pole. -/

@[expose] public section

set_option maxHeartbeats 2000000

noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal ContDiff Convolution

namespace Euler2D

theorem divergence_planarLocalConvolution_eq_integral
    {φ : R2 → ℝ} {u : R2 → R2}
    (hs : HasCompactSupport φ) (hφ : ContDiff ℝ ∞ φ)
    (hu : LocallyIntegrable u volume) (x : R2) :
    pd 0 (planarKernelVelocity u φ) x 0 + pd 1 (planarKernelVelocity u φ) x 1 =
      ∫ y, ∑ i : Fin 2, pd i φ y * u (x - y) i := by
  let L := (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] R2 →L[ℝ] R2)
  let L' := L.precompL R2
  let I : R2 → R2 →L[ℝ] R2 := fun y => L' (fderiv ℝ φ y) (u (x - y))
  have hdφ : Continuous (fderiv ℝ φ) := hφ.continuous_fderiv (by simp)
  have hI : Integrable I := (hs.fderiv ℝ).convolutionExists_left L' hdφ hu x
  have hd : fderiv ℝ (planarKernelVelocity u φ) x = ∫ y, I y :=
    (hs.hasFDerivAt_convolution_left (μ := volume) (g := u) L (hφ.of_le (by simp)) hu x).fderiv
  let J : (R2 →L[ℝ] R2) →L[ℝ] ℝ :=
    (EuclideanSpace.proj 0 : R2 →L[ℝ] ℝ).comp
      (ContinuousLinearMap.apply ℝ R2 (EuclideanSpace.single 0 1)) +
    (EuclideanSpace.proj 1 : R2 →L[ℝ] ℝ).comp
      (ContinuousLinearMap.apply ℝ R2 (EuclideanSpace.single 1 1))
  change J (fderiv ℝ (planarKernelVelocity u φ) x) = _
  rw [hd]
  have hcoord (i : Fin 2) : Integrable (fun y => I y (EuclideanSpace.single i 1) i) := by
    simpa only [PiLp.proj_apply] using
      (EuclideanSpace.proj i : R2 →L[ℝ] ℝ).integrable_comp
        (hI.apply_continuousLinearMap (EuclideanSpace.single i 1))
  have hcoord_integral (i : Fin 2) :
      (∫ y, I y) (EuclideanSpace.single i 1) i =
        ∫ y, I y (EuclideanSpace.single i 1) i := by
    rw [ContinuousLinearMap.integral_apply hI]
    simpa only [PiLp.proj_apply] using
      ((EuclideanSpace.proj i : R2 →L[ℝ] ℝ).integral_comp_comm
        (hI.apply_continuousLinearMap (EuclideanSpace.single i 1))).symm
  change (∫ y, I y) (EuclideanSpace.single 0 1) 0 +
    (∫ y, I y) (EuclideanSpace.single 1 1) 1 = _
  rw [hcoord_integral 0, hcoord_integral 1, ← integral_add (hcoord 0) (hcoord 1)]
  apply integral_congr_ae
  exact ae_of_all _ (fun y => by
    simp only [I, L', ContinuousLinearMap.precompL_apply, L,
      ContinuousLinearMap.lsmul_apply, PiLp.smul_apply, smul_eq_mul, pd, Fin.sum_univ_two])

theorem divergence_planarLocalConvolution_zero
    {φ : R2 → ℝ} {u : R2 → R2}
    (hs : HasCompactSupport φ) (hφ : ContDiff ℝ ∞ φ)
    (hu : LocallyIntegrable u volume) (hdiv : IsPlanarWeaklyDivergenceFree u) (x : R2) :
    pd 0 (planarKernelVelocity u φ) x 0 + pd 1 (planarKernelVelocity u φ) x 1 = 0 := by
  let ψ : R2 → ℝ := fun z => φ (x - z)
  have hψ : ContDiff ℝ 1 ψ := (hφ.of_le (by simp)).comp (contDiff_const.sub contDiff_id)
  have hsψ : HasCompactSupport ψ := hs.comp_homeomorph (Homeomorph.subLeft x)
  have hpd (i : Fin 2) (z : R2) : pd i ψ z = -pd i φ (x - z) := by
    have hd := ((hφ.differentiable (by simp)).differentiableAt (x := x - z)).hasFDerivAt.comp z
      ((hasFDerivAt_const x z).sub (hasFDerivAt_id z))
    change HasFDerivAt ψ ((fderiv ℝ φ (x - z)).comp (0 - ContinuousLinearMap.id ℝ R2)) z at hd
    unfold pd
    rw [hd.fderiv]
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.zero_apply, ContinuousLinearMap.neg_apply, ContinuousLinearMap.id_apply, zero_sub, map_neg]
  have hweak := hdiv ψ hψ hsψ
  have hpoint (z : R2) : (∑ i : Fin 2, u z i * pd i ψ z) =
      -(∑ i : Fin 2, pd i φ (x - z) * u z i) := by
    simp only [Fin.sum_univ_two, hpd]
    ring
  simp_rw [hpoint] at hweak
  rw [integral_neg, neg_eq_zero] at hweak
  rw [divergence_planarLocalConvolution_eq_integral hs hφ hu x]
  calc
    _ = ∫ z, ∑ i : Fin 2, pd i φ (x - z) * u z i := by
      simpa only [sub_sub_cancel] using integral_sub_left_eq_self (μ := volume)
        (fun z => ∑ i : Fin 2, pd i φ (x - z) * u z i) x
    _ = 0 := hweak

end Euler2D

end
