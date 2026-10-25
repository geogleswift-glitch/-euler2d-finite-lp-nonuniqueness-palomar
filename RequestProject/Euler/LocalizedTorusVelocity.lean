module

public import RequestProject.Euler.ActualTorusKernelCancellation
public import RequestProject.Euler.TorusKernelConvolution
public import RequestProject.Euler.MultipoleFields

/-!
# The actual torus velocity in physical complex coordinates

Localized physical densities are evaluated by the original torus kernel
and area measure. The coordinate identity uses a genuine measure
preserving change of variables, so planar moment estimates can be applied
to those actual velocities.
-/

@[expose] public section

noncomputable section

open MeasureTheory Complex Set Filter Topology

namespace Euler2D

def localizedComplexVorticity (ζ : ℂ → ℝ) (y : R2) : ℝ :=
  ζ (normalizedComplexCoordinate 1 y)

lemma normalizedComplexCoordinate_one (y : R2) :
    normalizedComplexCoordinate 1 y = planeComplexEquiv (y - torusCenter) := by
  simp only [normalizedComplexCoordinate, inv_one, one_smul]

lemma complexTorusPoint_sub_normalizedCoordinate (x : ℂ) (y : R2) :
    complexTorusPoint (x - normalizedComplexCoordinate 1 y) =
      complexTorusPoint x - y + torusCenter := by
  have he : complexPhysicalPlane (planeComplexEquiv (y - torusCenter)) =
      y - torusCenter := by
    rw [← complexPhysicalPlane_symm_eq_planeComplexEquiv,
      LinearIsometryEquiv.apply_symm_apply]
  rw [normalizedComplexCoordinate_one, complexTorusPoint, map_sub, he, complexTorusPoint]
  abel

lemma localizedComplexVorticity_zero_off_box {a : ℝ} (ha : a < 1)
    {ζ : ℂ → ℝ} (hsupp : ∀ z, a < ‖z‖ → ζ z = 0)
    {y : R2} (hy : y ∉ torusBox) : localizedComplexVorticity ζ y = 0 := by
  apply hsupp
  by_contra hn
  have hn' : ‖y - torusCenter‖ ≤ a := by
    simpa only [normalizedComplexCoordinate_one, norm_planeComplexEquiv] using not_lt.mp hn
  exact hy (norm_sub_center_lt_one_mem_box (hn'.trans_lt ha))

theorem planeComplexEquiv_torusKernelVelocity (w : R2 → ℝ) (x : R2) :
    planeComplexEquiv (torusKernelVelocity w x) =
      ∫ y in torusBox, w y • planeComplexEquiv
        (torusBiotSavartKernel (x - y + torusCenter)) := by
  calc
    _ = complexPhysicalPlane.symm (∫ y in torusBox,
        w y • torusBiotSavartKernel (x - y + torusCenter)) :=
      (complexPhysicalPlane_symm_eq_planeComplexEquiv _).symm
    _ = ∫ y in torusBox, complexPhysicalPlane.symm
        (w y • torusBiotSavartKernel (x - y + torusCenter)) :=
      (complexPhysicalPlane.symm.toLinearIsometry.integral_comp_comm _).symm
    _ = _ := by
      apply integral_congr_ae
      exact Eventually.of_forall fun y => by
        dsimp only
        rw [map_smul, complexPhysicalPlane_symm_eq_planeComplexEquiv]

theorem torusKernelVelocity_localized_complex {a : ℝ} (ha : a < 1)
    {ζ : ℂ → ℝ} (hsupp : ∀ z, a < ‖z‖ → ζ z = 0) (x : ℂ) :
    planeComplexEquiv (torusKernelVelocity (localizedComplexVorticity ζ) (complexTorusPoint x)) =
      ∫ y, ζ y • planeComplexEquiv
        (torusBiotSavartKernel (complexTorusPoint (x - y))) := by
  rw [planeComplexEquiv_torusKernelVelocity]
  have hwhole : (∫ y in torusBox, localizedComplexVorticity ζ y • planeComplexEquiv
      (torusBiotSavartKernel (complexTorusPoint x - y + torusCenter))) =
      ∫ y : R2, localizedComplexVorticity ζ y • planeComplexEquiv
        (torusBiotSavartKernel (complexTorusPoint x - y + torusCenter)) := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro y hy
    rw [localizedComplexVorticity_zero_off_box ha hsupp hy, zero_smul]
  rw [hwhole]
  have he : (fun y : R2 => localizedComplexVorticity ζ y • planeComplexEquiv
      (torusBiotSavartKernel (complexTorusPoint x - y + torusCenter))) =
      fun y : R2 => (fun z : ℂ => ζ z • planeComplexEquiv
        (torusBiotSavartKernel (complexTorusPoint (x - z))))
          (normalizedComplexCoordinate 1 y) := by
    funext y
    dsimp only [localizedComplexVorticity]
    rw [complexTorusPoint_sub_normalizedCoordinate]
  rw [he]
  simpa only [one_pow, one_smul] using
    integral_normalizedComplexCoordinate (by norm_num : 0 < (1 : ℝ))
      (fun z : ℂ => ζ z • planeComplexEquiv
        (torusBiotSavartKernel (complexTorusPoint (x - z))))

end Euler2D

end
