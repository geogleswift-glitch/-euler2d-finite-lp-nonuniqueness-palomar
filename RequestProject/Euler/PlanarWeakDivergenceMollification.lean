module

public import RequestProject.Euler.BoundedVelocityMollificationSpatialC1

/-! Genuine compact spatial smoothing turns distributional planar
incompressibility into the actual pointwise divergence identity used
by the particle Jacobian theorem. -/

@[expose] public section

set_option maxHeartbeats 2000000

noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal ContDiff Convolution

namespace Euler2D

def IsPlanarWeaklyDivergenceFree (u : R2 → R2) : Prop :=
  ∀ ψ : R2 → ℝ, ContDiff ℝ 1 ψ → HasCompactSupport ψ →
    (∫ x, ∑ i : Fin 2, u x i * pd i ψ x) = 0

theorem divergence_boundedVelocityMollification_eq_integral
    {φ : R2 → ℝ} {v : ℝ → R2 → R2}
    (hs : HasCompactSupport φ) (hφ : ContDiff ℝ ∞ φ)
    (hv : Continuous (Function.uncurry v)) (t : ℝ) (x : R2) :
    pd 0 (boundedVelocityMollification φ v t) x 0 +
      pd 1 (boundedVelocityMollification φ v t) x 1 =
      ∫ y, ∑ i : Fin 2, pd i φ y * v t (x - y) i := by
  let L := (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] R2 →L[ℝ] R2)
  let L' := L.precompL R2
  let I : R2 → R2 →L[ℝ] R2 := fun y => L' (fderiv ℝ φ y) (v t (x - y))
  have hdφ : Continuous (fderiv ℝ φ) := hφ.continuous_fderiv (by simp)
  have hIc : Continuous I := (L'.continuous.comp hdφ).clm_apply
    (hv.comp (continuous_const.prodMk (continuous_const.sub continuous_id)))
  have hIs : HasCompactSupport I := (hs.fderiv ℝ).mono (fun y => mt (fun hy : fderiv ℝ φ y = 0 => by
    simp only [I, hy, map_zero, ContinuousLinearMap.zero_apply]))
  have hI : Integrable I := hIc.integrable_of_hasCompactSupport hIs
  have hlocal : LocallyIntegrable (v t) volume :=
    (hv.comp (continuous_const.prodMk continuous_id)).locallyIntegrable
  have hd : fderiv ℝ (boundedVelocityMollification φ v t) x = ∫ y, I y :=
    (hs.hasFDerivAt_convolution_left (μ := volume) (g := v t) L (hφ.of_le (by simp)) hlocal x).fderiv
  let J : (R2 →L[ℝ] R2) →L[ℝ] ℝ :=
    (EuclideanSpace.proj 0 : R2 →L[ℝ] ℝ).comp
      (ContinuousLinearMap.apply ℝ R2 (EuclideanSpace.single 0 1)) +
    (EuclideanSpace.proj 1 : R2 →L[ℝ] ℝ).comp
      (ContinuousLinearMap.apply ℝ R2 (EuclideanSpace.single 1 1))
  change J (fderiv ℝ (boundedVelocityMollification φ v t) x) = _
  rw [hd, ← J.integral_comp_comm hI]
  apply integral_congr_ae
  exact ae_of_all _ (fun y => by
    change (pd 0 φ y) * v t (x - y) 0 + (pd 1 φ y) * v t (x - y) 1 = _
    dsimp only
    rw [Fin.sum_univ_two])

theorem divergence_boundedVelocityMollification_zero
    {φ : R2 → ℝ} {v : ℝ → R2 → R2}
    (hs : HasCompactSupport φ) (hφ : ContDiff ℝ ∞ φ)
    (hv : Continuous (Function.uncurry v)) (hdiv : ∀ t, IsPlanarWeaklyDivergenceFree (v t))
    (t : ℝ) (x : R2) :
    pd 0 (boundedVelocityMollification φ v t) x 0 +
      pd 1 (boundedVelocityMollification φ v t) x 1 = 0 := by
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
  have hweak := hdiv t ψ hψ hsψ
  have hpoint (z : R2) : (∑ i : Fin 2, v t z i * pd i ψ z) =
      -(∑ i : Fin 2, pd i φ (x - z) * v t z i) := by
    simp only [Fin.sum_univ_two, hpd]
    ring
  simp_rw [hpoint] at hweak
  rw [integral_neg, neg_eq_zero] at hweak
  rw [divergence_boundedVelocityMollification_eq_integral hs hφ hv t x]
  calc
    _ = ∫ z, ∑ i : Fin 2, pd i φ (x - z) * v t z i := by
      simpa only [sub_sub_cancel] using integral_sub_left_eq_self (μ := volume)
        (fun z => ∑ i : Fin 2, pd i φ (x - z) * v t z i) x
    _ = 0 := hweak

end Euler2D

end
