module

public import RequestProject.Euler.PositivePlanarFlowLimit

/-! Actual transport and original singular velocity on every
nonnegative time, for a genuine continuous planar area flow. -/

@[expose] public section

set_option maxHeartbeats 2500000

noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

namespace Euler2D

theorem continuous_positivePairBackwardAt_map (t : ℝ≥0) :
    Continuous (fun H : C(ℝ≥0 × R2, R2 × R2) => positivePairBackwardAt H t) :=
  (ContinuousMap.continuous_postcomp (⟨Prod.snd, continuous_snd⟩ : C(R2 × R2, R2))).comp
    (ContinuousMap.continuous_precomp
      (⟨fun a => (t, a), continuous_const.prodMk continuous_id⟩ : C(R2, ℝ≥0 × R2)))

theorem continuous_positivePairBackwardAt_time (H : C(ℝ≥0 × R2, R2 × R2)) :
    Continuous (positivePairBackwardAt H) :=
  ContinuousMap.continuous_of_continuous_uncurry _ H.continuous.snd

structure PositivePlanarTransportFlow (w : R2 → ℝ) where
  maps : C(ℝ≥0 × R2, R2 × R2)
  left_inv : ∀ t a, positivePairBackwardAt maps t (positivePairForwardAt maps t a) = a
  right_inv : ∀ t a, positivePairForwardAt maps t (positivePairBackwardAt maps t a) = a
  forward_area : ∀ t, MeasurePreserving (positivePairForwardAt maps t) volume volume
  backward_area : ∀ t, MeasurePreserving (positivePairBackwardAt maps t) volume volume
  initial : ∀ a, positivePairForwardAt maps 0 a = a

namespace PositivePlanarTransportFlow

variable {w : R2 → ℝ} (S : PositivePlanarTransportFlow w)

def homeomorph (t : ℝ≥0) : R2 ≃ₜ R2 where
  toFun := positivePairForwardAt S.maps t
  invFun := positivePairBackwardAt S.maps t
  left_inv := S.left_inv t
  right_inv := S.right_inv t
  continuous_toFun := (positivePairForwardAt S.maps t).continuous
  continuous_invFun := (positivePairBackwardAt S.maps t).continuous

def density (t : ℝ≥0) (x : R2) : ℝ := w (positivePairBackwardAt S.maps t x)

def velocity (t : ℝ≥0) : R2 → R2 := planarKernelVelocity kernelK (S.density t)

theorem integrable_density (hw : Integrable w) (t : ℝ≥0) : Integrable (S.density t) :=
  (S.backward_area t).integrable_comp_of_integrable hw

theorem norm_density_le {B : ℝ} (hB : ∀ x, ‖w x‖ ≤ B) (t : ℝ≥0) (x : R2) :
    ‖S.density t x‖ ≤ B := hB _

theorem integral_norm_density (t : ℝ≥0) : (∫ x, ‖S.density t x‖) = ∫ x, ‖w x‖ :=
  (S.backward_area t).integral_comp (S.homeomorph t).symm.measurableEmbedding (fun x : R2 => ‖w x‖)

theorem eLpNorm_density (hw : Integrable w) (p : ℝ≥0∞) (t : ℝ≥0) :
    eLpNorm (S.density t) p volume = eLpNorm w p volume :=
  eLpNorm_comp_measurePreserving hw.aestronglyMeasurable (S.backward_area t)

theorem density_initial (x : R2) : S.density 0 x = w x := by
  have hi := S.left_inv 0 x
  rw [S.initial x] at hi
  exact congrArg w hi

theorem density_L1_time (hw : Integrable w) (t : ℝ≥0) :
    Tendsto (fun s => ∫ x, ‖S.density s x - S.density t x‖) (𝓝 t) (𝓝 (0 : ℝ)) :=
  tendsto_integral_norm_planarTransport_time hw
    (continuous_positivePairBackwardAt_time S.maps) S.backward_area t

theorem continuous_velocity {B : ℝ} (hw : Integrable w) (hB : ∀ x, ‖w x‖ ≤ B) :
    Continuous (Function.uncurry S.velocity) := by
  apply continuous_iff_continuousAt.mpr
  intro p
  have hL : Tendsto (fun q : ℝ≥0 × R2 => ∫ x, ‖S.density q.1 x - S.density p.1 x‖)
      (𝓝 p) (𝓝 (0 : ℝ)) := (S.density_L1_time hw p.1).comp continuous_fst.continuousAt
  exact tendsto_planarBiotSavart_apply_of_L1
    (fun q => S.integrable_density hw q.1) (S.integrable_density hw p.1)
    (fun q => S.norm_density_le hB q.1) (S.norm_density_le hB p.1) hL continuous_snd.continuousAt

end PositivePlanarTransportFlow

end Euler2D

end
