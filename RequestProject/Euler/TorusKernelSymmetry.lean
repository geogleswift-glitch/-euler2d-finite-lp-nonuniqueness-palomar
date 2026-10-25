module

public import RequestProject.Euler.TorusGreenSymmetry
public import RequestProject.Euler.TorusKernelMollification
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# Quarter-turn covariance of the actual torus velocity kernel

The singular part is reindexed by the actual integer-lattice rotation;
the correction uses the proved scalar Green symmetry and the chain rule.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology Real
open scoped ContDiff ENNReal

namespace Euler2D

def perpJLinearIsometryEquiv : R2 ≃ₗᵢ[ℝ] R2 where
  toLinearEquiv :=
    { toLinearMap := perpJL.toLinearMap
      invFun := fun x => -perpJ x
      left_inv := by intro x; ext i; fin_cases i <;> simp [perpJ]
      right_inv := by intro x; ext i; fin_cases i <;> simp [perpJ] }
  norm_map' := norm_perpJ

@[simp] lemma perpJLinearIsometryEquiv_apply (x : R2) :
    perpJLinearIsometryEquiv x = perpJ x := rfl

theorem measurePreserving_perpJ : MeasurePreserving perpJ volume volume :=
  perpJLinearIsometryEquiv.measurePreserving

theorem measurePreserving_torusQuarterTurn : MeasurePreserving torusQuarterTurn volume volume :=
  (measurePreserving_add_left volume torusCenter).comp
    (measurePreserving_perpJ.comp (measurePreserving_sub_right volume torusCenter))

lemma norm_torusQuarterTurn_sub_center (x : R2) :
    ‖torusQuarterTurn x - torusCenter‖ = ‖x - torusCenter‖ := by
  simp only [torusQuarterTurn, add_sub_cancel_left, norm_perpJ]

lemma torusQuarterTurn_four (x : R2) :
    torusQuarterTurn (torusQuarterTurn (torusQuarterTurn (torusQuarterTurn x))) = x := by
  ext i
  fin_cases i <;> simp [torusQuarterTurn, perpJ] <;> ring

lemma torusQuarterTurn_add (x v : R2) :
    torusQuarterTurn (x + v) = torusQuarterTurn x + perpJ v := by
  ext i
  fin_cases i <;> simp [torusQuarterTurn, perpJ] <;> ring

lemma torusQuarterTurn_kernel_argument (x y : R2) :
    torusQuarterTurn x - torusQuarterTurn y + torusCenter =
      torusQuarterTurn (x - y + torusCenter) := by
  ext i
  fin_cases i <;> simp [torusQuarterTurn, perpJ] <;> ring

lemma kernelK_perpJ (x : R2) : kernelK (perpJ x) = perpJ (kernelK x) := by
  simp only [kernelK, norm_perpJ, perpJ_smul]

lemma localPlanarKernel_perpJ (x : R2) :
    localPlanarKernel (perpJ x) = perpJ (localPlanarKernel x) := by
  simp only [localPlanarKernel, cutoffKernelK, radialKernelCutoff,
    norm_perpJ, kernelK_perpJ, perpJ_smul]

theorem periodicLocalKernel_quarterTurn (x : R2) :
    periodicLocalKernel (torusQuarterTurn x) = perpJ (periodicLocalKernel x) := by
  change (∑' k, localPlanarKernel
    (torusQuarterTurn x + torusLatticeShift k - torusCenter)) =
      perpJ (∑' k, localPlanarKernel (x + torusLatticeShift k - torusCenter))
  have hmap : perpJ (∑' k, localPlanarKernel (x + torusLatticeShift k - torusCenter)) =
      ∑' k, perpJ (localPlanarKernel (x + torusLatticeShift k - torusCenter)) :=
    perpJLinearIsometryEquiv.toContinuousLinearEquiv.map_tsum
  rw [hmap, ← torusLatticeQuarterTurn.tsum_eq]
  apply tsum_congr
  intro k
  rw [torusLatticeShift_quarterTurn]
  have he : torusQuarterTurn x + perpJ (torusLatticeShift k) - torusCenter =
      perpJ (x + torusLatticeShift k - torusCenter) := by
    ext i
    fin_cases i <;> simp [torusQuarterTurn, perpJ, sub_eq_add_neg,
      add_assoc, add_left_comm, add_comm]
  rw [he, localPlanarKernel_perpJ]

theorem perpGradient_torusGreenCorrection_quarterTurn (x : R2) :
    perpGradient torusGreenCorrection (torusQuarterTurn x) =
      perpJ (perpGradient torusGreenCorrection x) := by
  have hdiff := torusGreenCorrection_smooth.differentiable (by simp)
  have he : torusGreenCorrection ∘ torusQuarterTurn = torusGreenCorrection :=
    funext torusGreenCorrection_quarterTurn
  have h0 := pd_zero_comp_torusQuarterTurn hdiff x
  have h1 := pd_one_comp_torusQuarterTurn hdiff x
  rw [he] at h0 h1
  ext i
  fin_cases i
  · change -pd 1 torusGreenCorrection (torusQuarterTurn x) = -pd 0 torusGreenCorrection x
    rw [← h0]
  · change pd 0 torusGreenCorrection (torusQuarterTurn x) = -pd 1 torusGreenCorrection x
    linarith

theorem torusBiotSavartKernel_quarterTurn (x : R2) :
    torusBiotSavartKernel (torusQuarterTurn x) = perpJ (torusBiotSavartKernel x) := by
  change periodicLocalKernel (torusQuarterTurn x) +
      perpGradient torusGreenCorrection (torusQuarterTurn x) =
    perpJL (periodicLocalKernel x + perpGradient torusGreenCorrection x)
  rw [periodicLocalKernel_quarterTurn, perpGradient_torusGreenCorrection_quarterTurn, map_add]
  rfl

end Euler2D

end
