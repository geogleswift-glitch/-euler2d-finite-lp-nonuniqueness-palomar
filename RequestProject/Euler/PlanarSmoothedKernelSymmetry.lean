module

public import RequestProject.Euler.PlanarSmoothKernel
public import RequestProject.Euler.TorusKernelSymmetry

/-! Quarter-turn covariance of the actual smoothings of the original
planar Biot--Savart kernel. The scalar mollifier is chosen with the
same symmetry, and the integral is changed by the true planar rotation. -/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology

namespace Euler2D

theorem planarKernelVelocity_perpJ {K : R2 → R2} {w : R2 → ℝ}
    (hK : ∀ x, K (perpJ x) = perpJ (K x))
    (hw : ∀ x, w (perpJ x) = w x) (x : R2) :
    planarKernelVelocity K w (perpJ x) = perpJ (planarKernelVelocity K w x) := by
  unfold planarKernelVelocity
  calc
    _ = ∫ z, w (perpJ z) • K (perpJ x - perpJ z) :=
      (measurePreserving_perpJ.integral_comp
        perpJLinearIsometryEquiv.toHomeomorph.measurableEmbedding _).symm
    _ = ∫ z, perpJ (w z • K (x - z)) := by
      apply integral_congr_ae
      exact ae_of_all _ (fun z => by
        dsimp only
        have he : perpJ x - perpJ z = perpJ (x - z) := (perpJL.map_sub x z).symm
        rw [hw z, he, hK, perpJ_smul])
    _ = _ := perpJLinearIsometryEquiv.toLinearIsometry.integral_comp_comm _

theorem planarSmoothedBiotSavartKernel_perpJ (n : ℕ) (x : R2) :
    planarSmoothedBiotSavartKernel n (perpJ x) =
      perpJ (planarSmoothedBiotSavartKernel n x) :=
  planarKernelVelocity_perpJ kernelK_perpJ
    (planarVelocityMollifier_perpJ (planarVelocityApproxScale_pos n)) x

end Euler2D

end
