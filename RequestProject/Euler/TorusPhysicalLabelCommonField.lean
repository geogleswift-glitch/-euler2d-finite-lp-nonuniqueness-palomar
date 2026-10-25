module

public import RequestProject.Euler.TorusPhysicalLabelVelocityContinuity
public import RequestProject.Euler.CenteredComplexMaterialFlow
public import RequestProject.Euler.TorusParticleCorrectionIncompressibility
public import RequestProject.Euler.TorusHybridMaterialAgreementBounds

/-! A genuine shared inner-label field in physical coordinates. Its
global continuity, logarithmic modulus and incompressibility follow
from the same actual Euler transport, including for rough labels. -/

@[expose] public section

set_option maxHeartbeats 3500000

noncomputable section

open Set Filter Topology MeasureTheory Metric
open scoped NNReal ENNReal

namespace Euler2D
namespace BoundedEulerParticleSystem

variable {f : Lp ℝ 2 μT} {T : ℝ} (S : BoundedEulerParticleSystem f T)

def physicalLabelCommonField (w : R2 → ℝ) (t : ℝ) (x : R2) : R2 :=
  planarKernelVelocity kernelK (torusBox.indicator (S.transportedScalar w t)) x +
    S.correctionLabelField t x

theorem physicalComplexLabelVelocity_eq_raw_spatial (w : R2 → ℝ) (t : ℝ) (z : ℂ) :
    complexPhysicalPlane (velocityC (S.physicalComplexSource w t) z) =
      planarKernelVelocity kernelK (torusBox.indicator (S.transportedScalar w t)) (complexTorusPoint z) := by
  rw [complexTorus_velocityC_eq_spatial]
  congr 1
  funext x
  change torusBox.indicator (S.transportedScalar w t)
    (centeredComplexHomeomorph (centeredComplexHomeomorph.symm x)) = _
  rw [Homeomorph.apply_symm_apply]

theorem continuous_physicalLabelCommonField {w : R2 → ℝ} {M : ℝ}
    (hw : MemLp w 2 μT) (hM : ∀ x, ‖w x‖ ≤ M) :
    Continuous (fun p : ℝ × R2 => S.physicalLabelCommonField w p.1 p.2) := by
  have harg : Continuous (fun p : ℝ × R2 => (p.1, centeredComplexHomeomorph.symm p.2)) :=
    continuous_fst.prodMk (centeredComplexHomeomorph.symm.continuous.comp continuous_snd)
  have hc := complexPhysicalPlane.continuous.comp
    ((S.continuous_physicalComplexLabelVelocity hw hM).comp harg)
  have hraw : Continuous (fun p : ℝ × R2 =>
      planarKernelVelocity kernelK (torusBox.indicator (S.transportedScalar w p.1)) p.2) := by
    convert hc using 1
    funext p
    dsimp only [Function.comp_apply]
    rw [S.physicalComplexLabelVelocity_eq_raw_spatial,
      ← centeredComplexHomeomorph_apply, Homeomorph.apply_symm_apply]
  exact hraw.add S.continuous_correctionLabelField

theorem exists_physicalLabelCommonField_bounds {w : R2 → ℝ} {M : ℝ}
    (hw : MemLp w 2 μT) (hwper : IsTorusPeriodic w) (hM : ∀ x, ‖w x‖ ≤ M) :
    ∃ MB CB : ℝ≥0,
      Continuous (fun p : ℝ × R2 => S.physicalLabelCommonField w p.1 p.2) ∧
      (∀ t x, ‖S.physicalLabelCommonField w t x‖ ≤ MB) ∧
      (∀ t x y, ‖x - y‖ ≤ 1 / 2 →
        ‖S.physicalLabelCommonField w t x - S.physicalLabelCommonField w t y‖ ≤
          CB * logFlowModulus ‖x - y‖) ∧
      ∀ t, IsPlanarWeaklyDivergenceFree (S.physicalLabelCommonField w t) := by
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  have hwi : Integrable w μT := hw.integrable (by norm_num)
  let A := ∫ x in torusBox, |w x|
  have hA : 0 ≤ A := integral_nonneg (fun x => abs_nonneg _)
  let ω : ℝ → R2 → ℝ := fun t => torusBox.indicator (S.transportedScalar w t)
  have hωi (t : ℝ) : Integrable (ω t) :=
    (integrable_indicator_iff measurableSet_torusBox).mpr (S.integrable_transportedScalar_of_integrable hwi t)
  have hωM (t : ℝ) (x : R2) : ‖ω t x‖ ≤ M := by
    by_cases hx : x ∈ torusBox
    · rw [show ω t x = S.transportedScalar w t x from indicator_of_mem hx _]
      exact hM _
    · rw [show ω t x = 0 from indicator_of_notMem hx _, norm_zero]
      exact hM0
  have hωA (t : ℝ) : (∫ x, ‖ω t x‖) = A := by
    have he : (fun x => ‖ω t x‖) = torusBox.indicator (fun x => |S.transportedScalar w t x|) := by
      funext x
      by_cases hx : x ∈ torusBox <;> simp [ω, hx, Real.norm_eq_abs]
    rw [he, integral_indicator measurableSet_torusBox, S.integral_abs_transportedScalar hwi hwper t]
  have hplane (t : ℝ) (x : R2) : ‖planarKernelVelocity kernelK (ω t) x‖ ≤ M + A := by
    have hb := norm_planarBiotSavart_le_mass_amplitude (hωi t) (hωM t) x
    rw [hωA] at hb
    exact hb.trans (by nlinarith [sq_nonneg (Real.sqrt A - Real.sqrt M), Real.sq_sqrt hM0, Real.sq_sqrt hA])
  obtain ⟨Mc, hMc, hcorrM⟩ := S.exists_uniform_bound_correctionLabelField
  obtain ⟨L, hcorrL⟩ := S.exists_lipschitzWith_correctionLabelField
  let MB : ℝ≥0 := ⟨M + A + Mc, by positivity⟩
  let CB : ℝ≥0 := ⟨8 * (M + A) + L, by positivity⟩
  have hvc := S.continuous_physicalLabelCommonField hw hM
  refine ⟨MB, CB, hvc, ?_, ?_, ?_⟩
  · intro t x
    exact (norm_add_le _ _).trans (add_le_add (hplane t x) (hcorrM t x))
  · intro t x y hxy
    have hp := planarBiotSavart_logFlowModulus_le (hωi t) (hωM t) (hωA t).le hxy
    have hm : ‖x - y‖ ≤ logFlowModulus ‖x - y‖ := by
      have hn := mul_nonpos_of_nonneg_of_nonpos (norm_nonneg (x - y))
        (Real.log_nonpos (norm_nonneg _) (hxy.trans (by norm_num : (1 / 2 : ℝ) ≤ 1)))
      dsimp only [logFlowModulus]
      linarith
    have hc := (hcorrL t).dist_le_mul x y
    rw [dist_eq_norm, dist_eq_norm] at hc
    have hc' := hc.trans (mul_le_mul_of_nonneg_left hm L.2)
    change ‖(planarKernelVelocity kernelK (ω t) x + S.correctionLabelField t x) -
      (planarKernelVelocity kernelK (ω t) y + S.correctionLabelField t y)‖ ≤ _
    rw [add_sub_add_comm]
    have heq : 8 * (M + A) * logFlowModulus ‖x - y‖ +
        (L : ℝ) * logFlowModulus ‖x - y‖ = (CB : ℝ) * logFlowModulus ‖x - y‖ := by
      change 8 * (M + A) * logFlowModulus ‖x - y‖ +
        (L : ℝ) * logFlowModulus ‖x - y‖ =
          (8 * (M + A) + (L : ℝ)) * logFlowModulus ‖x - y‖
      ring
    exact (norm_add_le _ _).trans ((add_le_add hp hc').trans_eq heq)
  · intro t
    have hc : Continuous (S.correctionLabelField t) :=
      Continuous.comp (f := fun x : R2 => (t, x))
        (g := fun p : ℝ × R2 => S.correctionLabelField p.1 p.2)
        S.continuous_correctionLabelField (continuous_const.prodMk continuous_id)
    have hp : Continuous (planarKernelVelocity kernelK (ω t)) :=
      (uniformContinuous_planarBiotSavart (hωi t) (hωM t)).continuous
    exact (isPlanarWeaklyDivergenceFree_planarBiotSavart (hωi t) (hωM t)).add
      (S.isPlanarWeaklyDivergenceFree_correctionLabelField t) hp hc

end BoundedEulerParticleSystem
end Euler2D

end
