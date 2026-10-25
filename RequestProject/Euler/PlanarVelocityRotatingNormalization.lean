module

public import RequestProject.Euler.PlanarVelocityPhysicalScaling
public import RequestProject.Euler.ComplexPlanarBiotSavart
public import RequestProject.Euler.RotatingNormalizedFiniteParticleTransport

/-! Exact rotation, amplitude and length changes of the original
singular Biot--Savart integral, for arbitrary real sources. These
identities retain its value at the singular point. -/

@[expose] public section

set_option maxHeartbeats 5000000
set_option maxRecDepth 5500

noncomputable section

open Complex Set Filter Topology MeasureTheory
open scoped NNReal ENNReal

namespace Euler2D

theorem velocityC_rotation_pullback (w : ℂ → ℝ) (a : Circle) (x : ℂ) :
    velocityC w ((a : ℂ) * x) =
      (a : ℂ) * velocityC (fun y => w ((a : ℂ) * y)) x := by
  let G : ℂ → ℂ := fun y => (w y : ℂ) *
    (I * ((a : ℂ) * x - y) / (2 * Real.pi * ‖(a : ℂ) * x - y‖ ^ 2))
  have hchange := (rotation a).measurePreserving.integral_comp
    (rotation a).toHomeomorph.measurableEmbedding G
  have hpoint (y : ℂ) : G (rotation a y) = (a : ℂ) *
      ((w ((a : ℂ) * y) : ℂ) * (I * (x - y) / (2 * Real.pi * ‖x - y‖ ^ 2))) := by
    dsimp only [G]
    rw [rotation_apply, show (a : ℂ) * x - (a : ℂ) * y = (a : ℂ) * (x - y) by ring,
      norm_mul, a.norm_coe, one_mul]
    ring
  calc
    _ = ∫ y, G (rotation a y) := hchange.symm
    _ = ∫ y, (a : ℂ) *
        ((w ((a : ℂ) * y) : ℂ) * (I * (x - y) / (2 * Real.pi * ‖x - y‖ ^ 2))) := by
      exact integral_congr_ae (ae_of_all _ hpoint)
    _ = _ := integral_const_mul _ _

theorem velocityC_normalized_rotation (A : ℝ) (hA : A ≠ 0) {r : ℝ} (hr : 0 < r)
    (a : Circle) (w : ℂ → ℝ) (z : ℂ) :
    (a : ℂ)⁻¹ * ((A * r)⁻¹ • velocityC w (r • ((a : ℂ) * z))) =
      velocityC (fun y => A⁻¹ * w (r • ((a : ℂ) * y))) z := by
  let wn : ℂ → ℝ := fun y => A⁻¹ * w (r • y)
  have hscale : scaledComplexDensity A r wn = w := by
    funext y
    dsimp only [scaledComplexDensity, wn]
    rw [smul_inv_smul₀ hr.ne', ← mul_assoc, mul_inv_cancel₀ hA, one_mul]
  have hv := velocityC_scaledComplexDensity A hr wn ((a : ℂ) * z)
  rw [hscale, velocityC_rotation_pullback wn a z] at hv
  have ha : (a : ℂ) ≠ 0 := by
    intro hz
    have hn := a.norm_coe
    rw [hz, norm_zero] at hn
    norm_num at hn
  rw [hv, inv_smul_smul₀ (mul_ne_zero hA hr.ne'), inv_mul_cancel_left₀ ha]

theorem planarKernelVelocity_rotating_normalization
    (u : R2 → ℝ) (A : ℝ) (hA : A ≠ 0) {r : ℝ} (hr : 0 < r) (θ : ℝ) (z : R2) :
    planarRigidRotation (-θ)
        ((A * r)⁻¹ • planarKernelVelocity kernelK u (r • planarRigidRotation θ z)) =
      planarKernelVelocity kernelK (fun y => A⁻¹ * u (r • planarRigidRotation θ y)) z := by
  let a : Circle := Circle.exp θ
  let w : ℂ → ℝ := fun y => u (complexPhysicalPlane y)
  have ha : (a : ℂ) = Complex.exp ((θ : ℂ) * I) := Circle.coe_exp θ
  have haInv : Complex.exp (((-θ : ℝ) : ℂ) * I) = (a : ℂ)⁻¹ := by
    rw [ha]
    simpa only [Complex.ofReal_neg, neg_mul] using Complex.exp_neg ((θ : ℂ) * I)
  have hphysical (v : R2) : complexPhysicalPlane (velocityC w (complexPhysicalPlane.symm v)) =
      planarKernelVelocity kernelK u v := by
    simpa only [w, LinearIsometryEquiv.apply_symm_apply] using complexPhysicalPlane_velocityC w v
  have hpoint : complexPhysicalPlane.symm (r • planarRigidRotation θ z) =
      r • ((a : ℂ) * complexPhysicalPlane.symm z) := by
    rw [map_smul, planarRigidRotation_apply, LinearIsometryEquiv.symm_apply_apply, ha]
  have hv := congrArg complexPhysicalPlane
    (velocityC_normalized_rotation A hA hr a w (complexPhysicalPlane.symm z))
  calc
    _ = complexPhysicalPlane ((a : ℂ)⁻¹ *
        ((A * r)⁻¹ • velocityC w (r • ((a : ℂ) * complexPhysicalPlane.symm z)))) := by
      rw [← hphysical (r • planarRigidRotation θ z), planarRigidRotation_apply,
        map_smul, LinearIsometryEquiv.symm_apply_apply, haInv, hpoint]
    _ = complexPhysicalPlane (velocityC
        (fun y => A⁻¹ * w (r • ((a : ℂ) * y))) (complexPhysicalPlane.symm z)) := hv
    _ = _ := by
      rw [complexPhysicalPlane_velocityC]
      congr 1
      funext y
      dsimp only [w]
      rw [map_smul, planarRigidRotation_apply, ← ha]

end Euler2D

end
