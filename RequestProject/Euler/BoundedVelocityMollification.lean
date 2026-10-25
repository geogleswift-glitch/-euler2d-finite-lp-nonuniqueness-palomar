module

public import RequestProject.Euler.SmoothParticleFlow
public import RequestProject.Euler.Osgood
public import Mathlib.Analysis.Calculus.ContDiff.Convolution
public import Mathlib.Analysis.Calculus.BumpFunction.Normed

/-! Actual compact-kernel regularization of a bounded planar velocity.
The smoothing is performed in space, with no periodicity assumption. -/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal Convolution ContDiff

namespace Euler2D

def boundedVelocityMollification (φ : R2 → ℝ) (v : ℝ → R2 → R2)
    (t : ℝ) (x : R2) : R2 :=
  (φ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] v t) x

theorem integrable_boundedVelocityMollification_integrand
    {φ : R2 → ℝ} {v : ℝ → R2 → R2} {M : ℝ}
    (hφ : Integrable φ) (hv : Continuous (Function.uncurry v))
    (hM : ∀ t x, ‖v t x‖ ≤ M) (t : ℝ) (x : R2) :
    Integrable (fun y => φ y • v t (x - y)) := by
  have hm : AEStronglyMeasurable (fun y => φ y • v t (x - y)) :=
    hφ.aestronglyMeasurable.smul ((hv.comp
      (continuous_const.prodMk (continuous_const.sub continuous_id))).aestronglyMeasurable)
  apply (hφ.norm.mul_const M).mono' hm
  exact ae_of_all _ (fun y => by
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_left (hM t (x - y)) (norm_nonneg _))

theorem continuous_boundedVelocityMollification
    {φ : R2 → ℝ} {v : ℝ → R2 → R2} {M : ℝ}
    (hφ : Integrable φ) (hv : Continuous (Function.uncurry v))
    (hM : ∀ t x, ‖v t x‖ ≤ M) :
    Continuous (Function.uncurry (boundedVelocityMollification φ v)) := by
  change Continuous (fun p : ℝ × R2 => ∫ y, φ y • v p.1 (p.2 - y))
  apply continuous_of_dominated (F := fun (p : ℝ × R2) y => φ y • v p.1 (p.2 - y))
    (fun p => (integrable_boundedVelocityMollification_integrand hφ hv hM p.1 p.2).aestronglyMeasurable)
    (fun p => ae_of_all _ (fun y => ?_)) (hφ.norm.mul_const M)
    (ae_of_all _ (fun y => by
      have harg : Continuous (fun p : ℝ × R2 => (p.1, p.2 - y)) := by fun_prop
      simpa only [Pi.smul_def', Function.comp_def, Function.uncurry_apply_pair] using
        (continuous_const : Continuous (fun _ : ℝ × R2 => φ y)).smul (hv.comp harg)))
  rw [norm_smul]
  exact mul_le_mul_of_nonneg_left (hM p.1 (p.2 - y)) (norm_nonneg _)

theorem norm_boundedVelocityMollification_le
    {φ : R2 → ℝ} {v : ℝ → R2 → R2} {M : ℝ}
    (hφ : Integrable φ) (hφpos : ∀ y, 0 ≤ φ y) (hφone : (∫ y, φ y) = 1)
    (hM : ∀ t x, ‖v t x‖ ≤ M) (t : ℝ) (x : R2) :
    ‖boundedVelocityMollification φ v t x‖ ≤ M := by
  have hb (y : R2) : ‖φ y • v t (x - y)‖ ≤ φ y * M := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hφpos y)]
    exact mul_le_mul_of_nonneg_left (hM t _) (hφpos y)
  calc
    _ ≤ ∫ y, φ y * M := norm_integral_le_of_norm_le (hφ.mul_const M) (ae_of_all _ hb)
    _ = M := by rw [integral_mul_const, hφone, one_mul]

theorem contDiff_boundedVelocityMollification
    {φ : R2 → ℝ} {v : ℝ → R2 → R2}
    (hs : HasCompactSupport φ) (hφ : ContDiff ℝ ∞ φ)
    (hv : Continuous (Function.uncurry v)) (t : ℝ) :
    ContDiff ℝ ∞ (boundedVelocityMollification φ v t) :=
  hs.contDiff_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ) hφ
    ((hv.comp (continuous_const.prodMk continuous_id)).locallyIntegrable)

theorem exists_lipschitz_boundedVelocityMollification
    {φ : R2 → ℝ} {v : ℝ → R2 → R2} {M : ℝ}
    (hs : HasCompactSupport φ) (hφ : ContDiff ℝ ∞ φ)
    (hv : Continuous (Function.uncurry v)) (hM : ∀ t x, ‖v t x‖ ≤ M) :
    ∃ K : ℝ≥0, ∀ t, LipschitzWith K (boundedVelocityMollification φ v t) := by
  letI : NormedAddCommGroup R2 := inferInstance
  letI : NormedSpace ℝ R2 := inferInstance
  let L := (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] R2 →L[ℝ] R2)
  let L' : (R2 →L[ℝ] ℝ) →L[ℝ] R2 →L[ℝ] R2 →L[ℝ] R2 := L.precompL R2
  have hM0 : 0 ≤ M := (norm_nonneg (v 0 0)).trans (hM 0 0)
  have hi : Integrable (fun y => ‖fderiv ℝ φ y‖) :=
    ((hφ.continuous_fderiv (by simp)).integrable_of_hasCompactSupport (hs.fderiv ℝ)).norm
  let B : ℝ := M * ∫ y, ‖fderiv ℝ φ y‖
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  refine ⟨NNReal.mk B hB, fun t => ?_⟩
  have hlocal : LocallyIntegrable (v t) volume :=
    (hv.comp ((continuous_const : Continuous (fun _ : R2 => t)).prodMk continuous_id)).locallyIntegrable
  have hd (x : R2) := hs.hasFDerivAt_convolution_left (μ := volume) (g := v t)
    L (hφ.of_le (by simp)) hlocal x
  apply lipschitzWith_of_nnnorm_fderiv_le
    ((contDiff_boundedVelocityMollification hs hφ hv t).differentiable (by simp))
  intro x
  change ‖fderiv ℝ (φ ⋆[L, volume] v t) x‖ ≤ B
  rw [(hd x).fderiv]
  have hb (y : R2) : ‖L' (fderiv ℝ φ y) (v t (x - y))‖ ≤
      M * ‖fderiv ℝ φ y‖ := by
    apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg hM0 (norm_nonneg _))
    intro w
    simp only [L', ContinuousLinearMap.precompL_apply, L,
      ContinuousLinearMap.lsmul_apply, norm_smul]
    calc
      ‖fderiv ℝ φ y w‖ * ‖v t (x - y)‖ ≤
          (‖fderiv ℝ φ y‖ * ‖w‖) * ‖v t (x - y)‖ :=
        mul_le_mul_of_nonneg_right ((fderiv ℝ φ y).le_opNorm w) (norm_nonneg _)
      _ ≤ (‖fderiv ℝ φ y‖ * ‖w‖) * M :=
        mul_le_mul_of_nonneg_left (hM t _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
      _ = (M * ‖fderiv ℝ φ y‖) * ‖w‖ := by ring
  exact (norm_integral_le_of_norm_le (hi.const_mul M) (ae_of_all _ hb)).trans_eq
    (by rw [integral_const_mul])

end Euler2D
