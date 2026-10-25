module

public import RequestProject.Euler.PlanarBiotSavartWeakDivergence
public import RequestProject.Euler.ActualTorusCancellation
public import RequestProject.Euler.Exterior

/-! Exact identification of the original complex Biot--Savart
formula with the genuine Euclidean planar kernel. The original
bounded integrable patch velocity is actually incompressible. -/

@[expose] public section

set_option maxHeartbeats 2000000

noncomputable section

open MeasureTheory Set Filter Topology Complex
open scoped NNReal ContDiff

namespace Euler2D

theorem complexPhysicalPlane_planar_kernel (z : ℂ) :
    complexPhysicalPlane (I * z / (2 * Real.pi * ‖z‖ ^ 2)) = kernelK (complexPhysicalPlane z) := by
  have he : I * z / (2 * Real.pi * ‖z‖ ^ 2) =
      (2 * Real.pi * ‖z‖ ^ 2)⁻¹ • (I * z) := by
    simp only [Complex.real_smul, Complex.ofReal_inv, Complex.ofReal_mul,
      Complex.ofReal_ofNat, Complex.ofReal_pow, div_eq_mul_inv]
    ring
  rw [he, map_smul, complexPhysicalPlane_mul_I, kernelK, LinearIsometryEquiv.norm_map]

theorem complexPhysicalPlane_velocityC (w : ℂ → ℝ) (x : R2) :
    complexPhysicalPlane (velocityC w (complexPhysicalPlane.symm x)) =
      planarKernelVelocity kernelK (fun y => w (complexPhysicalPlane.symm y)) x := by
  unfold velocityC planarKernelVelocity
  calc
    _ = ∫ z, complexPhysicalPlane ((w z : ℂ) *
        (I * (complexPhysicalPlane.symm x - z) / (2 * Real.pi * ‖complexPhysicalPlane.symm x - z‖ ^ 2))) :=
      (complexPhysicalPlane.toLinearIsometry.integral_comp_comm _).symm
    _ = ∫ z, w z • kernelK (x - complexPhysicalPlane z) := by
      apply integral_congr_ae
      exact ae_of_all _ (fun z => by
        dsimp only
        rw [← Complex.real_smul, map_smul, complexPhysicalPlane_planar_kernel, map_sub,
          LinearIsometryEquiv.apply_symm_apply])
    _ = _ := by
      have hc := complexPhysicalPlane.measurePreserving.integral_comp
        complexPhysicalPlane.toHomeomorph.measurableEmbedding
        (fun y : R2 => w (complexPhysicalPlane.symm y) • kernelK (x - y))
      simpa only [LinearIsometryEquiv.symm_apply_apply] using hc

theorem isPlanarWeaklyDivergenceFree_velocityC {w : ℂ → ℝ} {M : ℝ}
    (hw : Integrable w) (hM : ∀ z, ‖w z‖ ≤ M) :
    IsPlanarWeaklyDivergenceFree (fun x : R2 =>
      complexPhysicalPlane (velocityC w (complexPhysicalPlane.symm x))) := by
  have hwr : Integrable (fun y => w (complexPhysicalPlane.symm y)) :=
    complexPhysicalPlane.symm.measurePreserving.integrable_comp_of_integrable hw
  have he : (fun x : R2 => complexPhysicalPlane (velocityC w (complexPhysicalPlane.symm x))) =
      planarKernelVelocity kernelK (fun y => w (complexPhysicalPlane.symm y)) :=
    funext (complexPhysicalPlane_velocityC w)
  rw [he]
  exact isPlanarWeaklyDivergenceFree_planarBiotSavart hwr (fun y => hM (complexPhysicalPlane.symm y))

end Euler2D

end
