module

public import RequestProject.Euler.TorusPhysicalSourceContinuity
public import RequestProject.Euler.TorusParticleCorrectionField

/-! Exact identification of the physical complex correction convolution
with the Green correction of the same actual Euler particle system. -/

@[expose] public section

set_option maxHeartbeats 1800000

noncomputable section

open Complex ComplexConjugate Set Filter Topology MeasureTheory Metric
open scoped NNReal ENNReal

namespace Euler2D

theorem actualTorusCorrectionVelocity_boxedComplexDensity (w : R2 → ℝ) (x : ℂ) :
    actualTorusCorrectionVelocity (boxedComplexDensity w) x =
      planeComplexEquiv (∫ y in torusBox, w y • torusSmoothCorrectionKernel
        (complexTorusPoint x - y + torusCenter)) := by
  have he (z : ℂ) : boxedComplexDensity w z • actualComplexRemainderKernel (x - z) =
      torusBox.indicator (fun y => w y • planeComplexEquiv
        (torusSmoothCorrectionKernel (complexTorusPoint x - y + torusCenter)))
          (complexTorusPoint z) := by
    have hc : complexTorusPoint (x - z) = complexTorusPoint x - complexTorusPoint z + torusCenter := by
      simp only [complexTorusPoint, map_sub]
      abel
    by_cases hz : complexTorusPoint z ∈ torusBox
    · simp only [boxedComplexDensity, indicator_of_mem hz,
        actualComplexRemainderKernel, hc, torusSmoothCorrectionKernel]
    · simp only [boxedComplexDensity, indicator_of_notMem hz, zero_smul]
  unfold actualTorusCorrectionVelocity
  rw [integral_congr_ae (ae_of_all _ he),
    measurePreserving_complexTorusPoint.integral_comp measurableEmbedding_complexTorusPoint,
    integral_indicator measurableSet_torusBox]
  have hh := complexPhysicalPlane.symm.toContinuousLinearEquiv.integral_comp_comm
    (fun y => w y • torusSmoothCorrectionKernel (complexTorusPoint x - y + torusCenter))
    (μ := μT)
  simpa only [μT, map_smul, LinearIsometryEquiv.coe_toContinuousLinearEquiv,
    complexPhysicalPlane_symm_eq_planeComplexEquiv] using hh

namespace BoundedEulerParticleSystem

variable {f : Lp ℝ 2 μT} {T : ℝ} (S : BoundedEulerParticleSystem f T)

theorem actualTorusCorrectionVelocity_physicalComplexSource {w : R2 → ℝ}
    (hwf : w =ᵐ[μT] (f : R2 → ℝ)) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) (x : ℂ) :
    actualTorusCorrectionVelocity (S.physicalComplexSource w t) x =
      planeComplexEquiv (S.correctionLabelField t (complexTorusPoint x)) := by
  rw [physicalComplexSource, actualTorusCorrectionVelocity_boxedComplexDensity,
    S.correctionLabelField_eq_transported_convolution ht]
  congr 1
  apply integral_congr_ae
  filter_upwards [S.particleCurlL2_ae_transportedScalar hwf t] with y hy
  rw [hy]

end BoundedEulerParticleSystem

end Euler2D

end
