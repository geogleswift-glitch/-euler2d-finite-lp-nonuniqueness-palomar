module

public import RequestProject.Euler.PlanarKernelL1
public import RequestProject.Euler.TorusKernelSource

/-!
# The actual periodic local singular kernel

Translation into the coordinate disk and genuine lattice periodization
retain the planar distribution identities. The local kernel is integrable,
periodic, divergence free and has curl equal to a point mass plus the
specified smooth periodic error.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology Real
open scoped ContDiff

namespace Euler2D

def periodicLocalKernel : R2 → R2 :=
  torusPeriodize (fun x => localPlanarKernel (x - torusCenter))

lemma isTorusPeriodic_periodicLocalKernel : IsTorusPeriodic periodicLocalKernel :=
  isTorusPeriodic_torusPeriodize _

lemma periodicLocalKernel_eq_on_box {x : R2} (hx : x ∈ torusBox) :
    periodicLocalKernel x = localPlanarKernel (x - torusCenter) :=
  torusPeriodize_eq_on_box (fun _ hy => localPlanarKernel_eq_zero_of_one_le_norm hy) hx

lemma integrable_periodicLocalKernel : Integrable periodicLocalKernel μT := by
  have hr := (measurePreserving_sub_right volume torusCenter).integrable_comp_of_integrable
    integrable_localPlanarKernel
  apply hr.integrableOn.congr
  filter_upwards [ae_restrict_mem measurableSet_torusBox] with x hx
  exact (periodicLocalKernel_eq_on_box hx).symm

lemma pd_comp_add_const {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : R2 → F) (a x : R2) (i : Fin 2) :
    pd i (fun y => f (y + a)) x = pd i f (x + a) := by
  unfold pd
  rw [fderiv_comp_add_right]

lemma pd_comp_sub_const {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : R2 → F) (a x : R2) (i : Fin 2) :
    pd i (fun y => f (y - a)) x = pd i f (x - a) := by
  unfold pd
  rw [fderiv_comp_sub]

private lemma kernel_zero_off_box {x : R2} (hx : x ∉ torusBox) :
    localPlanarKernel (x - torusCenter) = 0 :=
  localPlanarKernel_eq_zero_of_one_le_norm
    (le_of_not_gt (fun hn => hx (norm_sub_center_lt_one_mem_box hn)))

theorem periodicLocalKernel_weak_curl {ψ : R2 → ℝ} (hψ : ContDiff ℝ 1 ψ) :
    (∫ x in torusBox, periodicLocalKernel x 0 * pd 1 ψ x - periodicLocalKernel x 1 * pd 0 ψ x) =
      ψ torusCenter + ∫ x in torusBox, periodicCenteredSource localPlanarKernelError x * ψ x := by
  let φ := fun x => ψ (x + torusCenter)
  have hφ : ContDiff ℝ 1 φ := hψ.comp (contDiff_id.add contDiff_const)
  have hraw : (∫ x in torusBox,
      periodicLocalKernel x 0 * pd 1 ψ x - periodicLocalKernel x 1 * pd 0 ψ x) =
      ∫ x : R2, localPlanarKernel x 0 * pd 1 φ x - localPlanarKernel x 1 * pd 0 φ x := by
    calc
      _ = ∫ x in torusBox, localPlanarKernel (x - torusCenter) 0 * pd 1 ψ x -
          localPlanarKernel (x - torusCenter) 1 * pd 0 ψ x := by
        apply setIntegral_congr_fun measurableSet_torusBox
        intro x hx
        dsimp only
        rw [periodicLocalKernel_eq_on_box hx]
      _ = ∫ x : R2, localPlanarKernel (x - torusCenter) 0 * pd 1 ψ x -
          localPlanarKernel (x - torusCenter) 1 * pd 0 ψ x := by
        apply setIntegral_eq_integral_of_forall_compl_eq_zero
        intro x hx
        simp only [kernel_zero_off_box hx, PiLp.zero_apply, zero_mul, sub_zero]
      _ = _ := by
        rw [← integral_add_right_eq_self _ torusCenter]
        congr 1
        funext x
        dsimp only [φ]
        rw [add_sub_cancel_right, pd_comp_add_const, pd_comp_add_const]
  have herr : (∫ x : R2, localPlanarKernelError x * φ x) =
      ∫ x in torusBox, periodicCenteredSource localPlanarKernelError x * ψ x := by
    symm
    calc
      _ = ∫ x in torusBox, localPlanarKernelError (x - torusCenter) * ψ x := by
        apply setIntegral_congr_fun measurableSet_torusBox
        intro x hx
        dsimp only
        rw [periodicCenteredSource_eq_on_box
          (fun _ hy => localPlanarKernelError_eq_zero_of_one_le_norm hy) hx]
      _ = ∫ x : R2, localPlanarKernelError (x - torusCenter) * ψ x := by
        apply setIntegral_eq_integral_of_forall_compl_eq_zero
        intro x hx
        rw [localPlanarKernelError_eq_zero_of_one_le_norm
          (le_of_not_gt (fun hn => hx (norm_sub_center_lt_one_mem_box hn))), zero_mul]
      _ = _ := by
        rw [← integral_add_right_eq_self _ torusCenter]
        congr 1
        funext x
        simp only [add_sub_cancel_right, φ]
  rw [hraw, localPlanarKernel_weak_curl_global hφ, herr]
  simp only [φ, zero_add]

theorem periodicLocalKernel_weak_divergence {ψ : R2 → ℝ} (hψ : ContDiff ℝ 1 ψ) :
    (∫ x in torusBox, ∑ i : Fin 2, periodicLocalKernel x i * pd i ψ x) = 0 := by
  let φ := fun x => ψ (x + torusCenter)
  have hφ : ContDiff ℝ 1 φ := hψ.comp (contDiff_id.add contDiff_const)
  calc
    _ = ∫ x in torusBox, ∑ i : Fin 2, localPlanarKernel (x - torusCenter) i * pd i ψ x := by
      apply setIntegral_congr_fun measurableSet_torusBox
      intro x hx
      dsimp only
      rw [periodicLocalKernel_eq_on_box hx]
    _ = ∫ x : R2, ∑ i : Fin 2, localPlanarKernel (x - torusCenter) i * pd i ψ x := by
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro x hx
      simp only [kernel_zero_off_box hx, PiLp.zero_apply, zero_mul, Finset.sum_const_zero]
    _ = ∫ x : R2, ∑ i : Fin 2, localPlanarKernel x i * pd i φ x := by
      rw [← integral_add_right_eq_self _ torusCenter]
      congr 1
      funext x
      dsimp only [φ]
      simp only [add_sub_cancel_right, pd_comp_add_const]
    _ = 0 := localPlanarKernel_weak_divergence_global hφ

theorem divFree_periodicLocalKernel : DivFree periodicLocalKernel := by
  intro ψ hψ
  exact periodicLocalKernel_weak_divergence (hψ.1.of_le (by simp))

end Euler2D

end
