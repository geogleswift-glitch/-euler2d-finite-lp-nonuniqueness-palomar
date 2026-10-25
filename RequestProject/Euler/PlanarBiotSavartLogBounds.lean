module

public import RequestProject.Euler.ComplexPlanarBiotSavart
public import RequestProject.Euler.PlanarVelocityLogFlow

/-! Genuine global logarithmic continuity bounds for the original
Euclidean planar Biot--Savart velocity, in the exact particle modulus.
The complex and real formulas are identified by the actual isometry. -/

@[expose] public section

set_option maxHeartbeats 2000000

noncomputable section

open MeasureTheory Set Filter Topology Metric
open scoped NNReal

namespace Euler2D

theorem planarBiotSavart_logFlowModulus_le {w : R2 → ℝ} {M A : ℝ}
    (hw : Integrable w) (hM : ∀ y, ‖w y‖ ≤ M) (hA : ∫ y, ‖w y‖ ≤ A)
    {x y : R2} (hxy : ‖x - y‖ ≤ 1 / 2) :
    ‖planarKernelVelocity kernelK w x - planarKernelVelocity kernelK w y‖ ≤
      (8 * (M + A)) * logFlowModulus ‖x - y‖ := by
  let wc : ℂ → ℝ := fun z => w (complexPhysicalPlane z)
  have hwc : Integrable wc := complexPhysicalPlane.measurePreserving.integrable_comp_of_integrable hw
  have hMc (z : ℂ) : |wc z| ≤ M := by simpa only [Real.norm_eq_abs] using hM (complexPhysicalPlane z)
  have hAc : (∫ z, |wc z|) ≤ A := by
    have he := complexPhysicalPlane.measurePreserving.integral_comp
      complexPhysicalPlane.toHomeomorph.measurableEmbedding (fun a : R2 => ‖w a‖)
    have hb := he.trans_le hA
    simpa only [Real.norm_eq_abs] using hb
  have he (a : R2) : planarKernelVelocity kernelK w a =
      complexPhysicalPlane (velocityC wc (complexPhysicalPlane.symm a)) := by
    have h := complexPhysicalPlane_velocityC wc a
    simpa only [wc, LinearIsometryEquiv.apply_symm_apply] using h.symm
  rw [he x, he y, ← map_sub, LinearIsometryEquiv.norm_map]
  have hxyc : ‖complexPhysicalPlane.symm x - complexPhysicalPlane.symm y‖ ≤ 1 / 2 := by
    simpa only [← map_sub, LinearIsometryEquiv.norm_map] using hxy
  have hb := velocityC_logFlowModulus_le hwc hMc hAc hxyc
  simpa only [← map_sub, LinearIsometryEquiv.norm_map] using hb

theorem uniformContinuous_planarBiotSavart {w : R2 → ℝ} {M : ℝ}
    (hw : Integrable w) (hM : ∀ y, ‖w y‖ ≤ M) :
    UniformContinuous (planarKernelVelocity kernelK w) := by
  let C := 8 * (M + ∫ y, ‖w y‖)
  have hlim : Tendsto (fun r : ℝ => C * logFlowModulus r) (𝓝 0) (𝓝 0) := by
    simpa only [logFlowModulus, zero_mul, mul_zero, sub_zero] using
      (continuous_logFlowModulus.tendsto 0).const_mul C
  rw [Metric.uniformContinuous_iff]
  intro ε hε
  obtain ⟨δ, hδ, hδbound⟩ := Metric.eventually_nhds_iff.mp (hlim.eventually (eventually_lt_nhds hε))
  refine ⟨min δ (1 / 2), lt_min hδ (by norm_num), ?_⟩
  intro x y hxy
  have hd : ‖x - y‖ < min δ (1 / 2) := by simpa only [dist_eq_norm] using hxy
  have hb := hδbound (y := ‖x - y‖) (by
    rw [dist_zero_right, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
    exact hd.trans_le (min_le_left _ _))
  rw [dist_eq_norm]
  exact (planarBiotSavart_logFlowModulus_le hw hM le_rfl
    (hd.le.trans (min_le_right _ _))).trans_lt hb

end Euler2D

end
