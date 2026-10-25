module

public import RequestProject.Euler.TorusParticleCorrectionField
public import RequestProject.Euler.PlanarC1WeakDivergence
public import RequestProject.Euler.PlanarConvolutionWeakDivergence

/-! The correction of the same genuine torus Euler particle system is
incompressible on the whole plane. This property follows from its actual
integral derivative and the Green kernel, with no time differentiation. -/

@[expose] public section

set_option maxHeartbeats 2500000

noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal ContDiff

namespace Euler2D
namespace BoundedEulerParticleSystem

variable {f : Lp ℝ 2 μT} {T : ℝ} (S : BoundedEulerParticleSystem f T)

theorem pd_correctionLabelField (t : ℝ) (x : R2) (i j : Fin 2) :
    pd i (S.correctionLabelField t) x j =
      ∫ b, f b * pd i torusSmoothCorrectionKernel (x - S.forward t b + torusCenter) j ∂μT := by
  have hi := S.integrable_correctionLabelDerivative_integrand t x
  unfold pd
  rw [(S.hasFDerivAt_correctionLabelField t x).fderiv]
  unfold correctionLabelDerivative
  rw [ContinuousLinearMap.integral_apply hi]
  have he := (EuclideanSpace.proj j : R2 →L[ℝ] ℝ).integral_comp_comm
    (hi.apply_continuousLinearMap (EuclideanSpace.single i 1))
  simpa only [ContinuousLinearMap.smul_apply, PiLp.proj_apply,
    PiLp.smul_apply, smul_eq_mul] using he.symm

theorem divergence_correctionLabelField (t : ℝ) (x : R2) :
    pd 0 (S.correctionLabelField t) x 0 + pd 1 (S.correctionLabelField t) x 1 = 0 := by
  have hi := S.integrable_correctionLabelDerivative_integrand t x
  have hint (i j : Fin 2) : Integrable
      (fun b => f b * pd i torusSmoothCorrectionKernel (x - S.forward t b + torusCenter) j) μT := by
    simpa only [pd, ContinuousLinearMap.smul_apply, PiLp.proj_apply,
      PiLp.smul_apply, smul_eq_mul] using
      (EuclideanSpace.proj j : R2 →L[ℝ] ℝ).integrable_comp
        (hi.apply_continuousLinearMap (EuclideanSpace.single i 1))
  have hdiv (y : R2) : pd 0 torusSmoothCorrectionKernel y 0 + pd 1 torusSmoothCorrectionKernel y 1 = 0 :=
    perpGradient_divergence torusGreenCorrection_smooth y
  rw [S.pd_correctionLabelField, S.pd_correctionLabelField,
    ← integral_add (hint 0 0) (hint 1 1)]
  simp_rw [← mul_add, hdiv, mul_zero]
  simp

theorem contDiff_one_correctionLabelField (t : ℝ) : ContDiff ℝ 1 (S.correctionLabelField t) := by
  have hj : Continuous (fun x : R2 => (t, x)) := continuous_const.prodMk continuous_id
  refine contDiff_one_iff_hasFDerivAt.mpr
    ⟨(fun x : R2 => S.correctionLabelDerivative t x), ?_, fun x => S.hasFDerivAt_correctionLabelField t x⟩
  exact Continuous.comp (f := fun x : R2 => (t, x))
    (g := fun p : ℝ × R2 => S.correctionLabelDerivative p.1 p.2)
    S.continuous_correctionLabelDerivative hj

theorem isPlanarWeaklyDivergenceFree_correctionLabelField (t : ℝ) :
    IsPlanarWeaklyDivergenceFree (S.correctionLabelField t) :=
  isPlanarWeaklyDivergenceFree_of_C1_divergence_zero
    (S.contDiff_one_correctionLabelField t) (S.divergence_correctionLabelField t)

theorem isPlanarWeaklyDivergenceFree_centeredCorrectionLabelField (t : ℝ) :
    IsPlanarWeaklyDivergenceFree (fun x => S.correctionLabelField t (x + torusCenter)) := by
  intro ψ hψ hs
  simpa only [sub_neg_eq_add] using planarWeakDivergenceFree_translate_kernel
    (S.isPlanarWeaklyDivergenceFree_correctionLabelField t) hψ hs (-torusCenter)

end BoundedEulerParticleSystem
end Euler2D

end
