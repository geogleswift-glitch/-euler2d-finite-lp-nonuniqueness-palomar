module

public import RequestProject.Euler.PlanarFlowPairCompactness
public import RequestProject.Euler.PlanarL1TransportContinuity
public import RequestProject.Euler.PlanarBiotSavartL1Stability

/-! The actual density and singular velocity carried by a continuous
planar area-preserving inverse pair. Strong density continuity gives
genuine joint time-space continuity of the original velocity. -/

@[expose] public section

set_option maxHeartbeats 2500000

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace Euler2D

structure PlanarTransportFlowLimit (w : R2 → ℝ) (T : ℝ) where
  maps : C(Icc (0 : ℝ) T × R2, R2 × R2)
  left_inv : ∀ t a, planarPairBackwardAt maps t (planarPairForwardAt maps t a) = a
  right_inv : ∀ t a, planarPairForwardAt maps t (planarPairBackwardAt maps t a) = a
  forward_area : ∀ t, MeasurePreserving (planarPairForwardAt maps t) volume volume
  backward_area : ∀ t, MeasurePreserving (planarPairBackwardAt maps t) volume volume
  initial : ∀ t : Icc (0 : ℝ) T, (t : ℝ) = 0 → ∀ a, planarPairForwardAt maps t a = a

namespace PlanarTransportFlowLimit

variable {w : R2 → ℝ} {T : ℝ} (S : PlanarTransportFlowLimit w T)

def homeomorph (t : Icc (0 : ℝ) T) : R2 ≃ₜ R2 where
  toFun := planarPairForwardAt S.maps t
  invFun := planarPairBackwardAt S.maps t
  left_inv := S.left_inv t
  right_inv := S.right_inv t
  continuous_toFun := (planarPairForwardAt S.maps t).continuous
  continuous_invFun := (planarPairBackwardAt S.maps t).continuous

def density (t : Icc (0 : ℝ) T) (x : R2) : ℝ := w (planarPairBackwardAt S.maps t x)

def velocity (t : Icc (0 : ℝ) T) : R2 → R2 := planarKernelVelocity kernelK (S.density t)

theorem integrable_density (hw : Integrable w) (t : Icc (0 : ℝ) T) :
    Integrable (S.density t) :=
  (S.backward_area t).integrable_comp_of_integrable hw

theorem norm_density_le {B : ℝ} (hB : ∀ x, ‖w x‖ ≤ B) (t : Icc (0 : ℝ) T) (x : R2) :
    ‖S.density t x‖ ≤ B := hB _

theorem integral_norm_density (t : Icc (0 : ℝ) T) :
    (∫ x, ‖S.density t x‖) = ∫ x, ‖w x‖ :=
  (S.backward_area t).integral_comp (S.homeomorph t).symm.measurableEmbedding
    (fun x : R2 => ‖w x‖)

theorem eLpNorm_density (hw : Integrable w) (p : ℝ≥0∞) (t : Icc (0 : ℝ) T) :
    eLpNorm (S.density t) p volume = eLpNorm w p volume :=
  eLpNorm_comp_measurePreserving hw.aestronglyMeasurable (S.backward_area t)

theorem density_initial (t : Icc (0 : ℝ) T) (ht : (t : ℝ) = 0) (x : R2) :
    S.density t x = w x := by
  have hi := S.left_inv t x
  rw [S.initial t ht x] at hi
  exact congrArg w hi

theorem density_L1_time (hw : Integrable w) (t : Icc (0 : ℝ) T) :
    Tendsto (fun s => ∫ x, ‖S.density s x - S.density t x‖) (𝓝 t) (𝓝 (0 : ℝ)) :=
  tendsto_integral_norm_planarTransport_time hw
    (continuous_planarPairBackwardAt_time S.maps) S.backward_area t

theorem continuous_velocity {B : ℝ} (hw : Integrable w) (hB : ∀ x, ‖w x‖ ≤ B) :
    Continuous (Function.uncurry S.velocity) := by
  apply continuous_iff_continuousAt.mpr
  intro p
  have hL : Tendsto (fun q : Icc (0 : ℝ) T × R2 =>
      ∫ x, ‖S.density q.1 x - S.density p.1 x‖) (𝓝 p) (𝓝 (0 : ℝ)) :=
    (S.density_L1_time hw p.1).comp continuous_fst.continuousAt
  exact tendsto_planarBiotSavart_apply_of_L1
    (fun q => S.integrable_density hw q.1) (S.integrable_density hw p.1)
    (fun q => S.norm_density_le hB q.1) (S.norm_density_le hB p.1)
    hL continuous_snd.continuousAt

end PlanarTransportFlowLimit

end Euler2D

end
