module

public import RequestProject.Euler.LocalizedTorusVelocity

/-!
# Integrable physical torus velocities and their actual planar comparison

The local comparison retains genuine integrability at the kernel pole.
This is needed before splitting a Bochner integral into its planar and
smooth parts.
-/

@[expose] public section

noncomputable section

open MeasureTheory Complex Set Filter Topology

namespace Euler2D

theorem measurePreserving_complexTorusPoint :
    MeasurePreserving complexTorusPoint (volume : Measure ℂ) volume := by
  have h := (measurePreserving_add_right volume torusCenter).comp
    (MeasurePreserving.symm planeComplexEquiv measurePreserving_planeComplexEquiv)
  convert h using 1
  funext z
  simp only [complexTorusPoint, Function.comp_apply, complexPhysicalPlane_eq_planeComplexEquiv_symm]

lemma normalizedComplexCoordinate_one_complexTorusPoint (z : ℂ) :
    normalizedComplexCoordinate 1 (complexTorusPoint z) = z := by
  rw [normalizedComplexCoordinate_one, complexTorusPoint, add_sub_cancel_right,
    ← complexPhysicalPlane_symm_eq_planeComplexEquiv, LinearIsometryEquiv.symm_apply_apply]

lemma integrable_localizedComplexVorticity {ζ : ℂ → ℝ} (hζ : Integrable ζ) :
    Integrable (localizedComplexVorticity ζ) (volume : Measure R2) := by
  have hcoord : MeasurePreserving (fun y : R2 => planeComplexEquiv (y - torusCenter))
      volume volume :=
    measurePreserving_planeComplexEquiv.comp (measurePreserving_sub_right volume torusCenter)
  have hc := hcoord.integrable_comp_of_integrable hζ
  have he : localizedComplexVorticity ζ =
      fun y : R2 => ζ (planeComplexEquiv (y - torusCenter)) := by
    funext y
    rw [localizedComplexVorticity, normalizedComplexCoordinate_one]
  rw [he]
  exact hc

theorem integrable_localized_torusComplexVelocity {a M : ℝ} (ha : a < 1)
    {ζ : ℂ → ℝ} (hζ : Integrable ζ) (hM : ∀ y, ‖ζ y‖ ≤ M)
    (hsupp : ∀ z, a < ‖z‖ → ζ z = 0) (x : ℂ) :
    Integrable (fun y => ζ y • planeComplexEquiv
      (torusBiotSavartKernel (complexTorusPoint (x - y)))) := by
  have hw : AEStronglyMeasurable (localizedComplexVorticity ζ) μT :=
    (integrable_localizedComplexVorticity hζ).integrableOn.aestronglyMeasurable
  have hbound : ∀ᵐ y ∂μT, ‖localizedComplexVorticity ζ y‖ ≤ M :=
    Eventually.of_forall fun y => hM _
  have hi := integrable_torusKernelVelocity_integrand hw hbound (complexTorusPoint x)
  have hc := complexPhysicalPlane.symm.toContinuousLinearEquiv.toContinuousLinearMap.integrable_comp hi
  have hc' : IntegrableOn (fun y : R2 => localizedComplexVorticity ζ y • planeComplexEquiv
      (torusBiotSavartKernel (complexTorusPoint x - y + torusCenter))) torusBox := by
    apply hc.congr
    filter_upwards [] with y
    change complexPhysicalPlane.symm (localizedComplexVorticity ζ y •
      torusBiotSavartKernel (complexTorusPoint x - y + torusCenter)) = _
    rw [map_smul, complexPhysicalPlane_symm_eq_planeComplexEquiv]
  have hwhole : Integrable (fun y : R2 => localizedComplexVorticity ζ y • planeComplexEquiv
      (torusBiotSavartKernel (complexTorusPoint x - y + torusCenter))) := by
    apply hc'.integrable_of_forall_notMem_eq_zero
    intro y hy
    rw [localizedComplexVorticity_zero_off_box ha hsupp hy, zero_smul]
  have hp := measurePreserving_complexTorusPoint.integrable_comp_of_integrable hwhole
  apply hp.congr
  filter_upwards [] with y
  dsimp only [Function.comp_apply, localizedComplexVorticity]
  rw [normalizedComplexCoordinate_one_complexTorusPoint,
    ← complexTorusPoint_sub_normalizedCoordinate x (complexTorusPoint y),
    normalizedComplexCoordinate_one_complexTorusPoint]

lemma integrable_actualComplexRemainderVelocity {ζ : ℂ → ℝ} (hζ : Integrable ζ) (x : ℂ) :
    Integrable (fun y => ζ y • actualComplexRemainderKernel (x - y)) := by
  have hc := complexPerpGradientOperator.integrable_comp
    (integrable_actualComplexGreenCorrection_derivative hζ x)
  apply hc.congr
  filter_upwards [] with y
  rw [map_smul, actualComplexRemainderKernel_eq_operator]

lemma complexTorusKernel_eq_planar_add_remainder {z : ℂ} (hz : ‖z‖ ≤ 1 / 2) :
    planeComplexEquiv (torusBiotSavartKernel (complexTorusPoint z)) =
      I * z / (2 * Real.pi * ‖z‖ ^ 2) + actualComplexRemainderKernel z := by
  have he := congrArg complexPhysicalPlane.symm
    (torusBiotSavartKernel_complexTorusPoint_sub_kernelK hz)
  simp only [map_sub, complexPhysicalPlane_symm_eq_planeComplexEquiv,
    planeComplexEquiv_kernelK_complexPhysicalPlane] at he
  change _ - _ = actualComplexRemainderKernel z at he
  exact sub_eq_iff_eq_add'.mp he

end Euler2D

end
