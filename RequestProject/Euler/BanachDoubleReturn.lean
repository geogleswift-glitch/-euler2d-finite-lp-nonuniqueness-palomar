module

public import Mathlib

/-! The actual doubled local return map has derivative equal to the
square of the original derivative and preserves the proved local regularity. -/

@[expose] public section

noncomputable section

open Set Filter Topology
open scoped ContDiff

namespace Euler2D

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def banachDoubleReturn (F : E → E) : E → E := fun v => F (F v)

theorem banachDoubleReturn_zero {F : E → E} (hF : F 0 = 0) : banachDoubleReturn F 0 = 0 := by
  unfold banachDoubleReturn
  rw [hF, hF]

theorem contDiffAt_banachDoubleReturn {F : E → E} {n : ℕ∞}
    (hF : F 0 = 0) (hf : ContDiffAt ℝ n F 0) : ContDiffAt ℝ n (banachDoubleReturn F) 0 := by
  have hf' : ContDiffAt ℝ n F (F 0) := by rw [hF]; exact hf
  exact hf'.comp 0 hf

theorem hasFDerivAt_banachDoubleReturn {F : E → E}
    (hF : F 0 = 0) (hf : DifferentiableAt ℝ F 0) :
    HasFDerivAt (banachDoubleReturn F) ((fderiv ℝ F 0) ^ 2) 0 := by
  have hf' : HasFDerivAt F (fderiv ℝ F 0) (F 0) := by rw [hF]; exact hf.hasFDerivAt
  rw [pow_two]
  exact hf'.comp 0 hf.hasFDerivAt

theorem fderiv_banachDoubleReturn {F : E → E}
    (hF : F 0 = 0) (hf : DifferentiableAt ℝ F 0) :
    fderiv ℝ (banachDoubleReturn F) 0 = (fderiv ℝ F 0) ^ 2 :=
  (hasFDerivAt_banachDoubleReturn hF hf).fderiv

theorem continuousLinearMap_square_eigenvector (L : E →L[ℝ] E) (v : E) (a : ℝ)
    (hv : L v = a • v) : (L ^ 2) v = a ^ 2 • v := by
  rw [pow_two, ContinuousLinearMap.mul_apply, hv]
  have hs : L (a • v) = a • L v := L.toLinearMap.map_smul' a v
  rw [hs, hv, smul_smul, pow_two]

end Euler2D

end
