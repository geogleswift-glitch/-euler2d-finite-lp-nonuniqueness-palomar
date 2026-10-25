module

public import RequestProject.Euler.TorusQuarterTurnTransport
public import RequestProject.Euler.FourfoldTorusKernelMollification

/-! The explicitly averaged actual regularization has vector quarter-turn covariance. -/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ContDiff ENNReal

namespace Euler2D

theorem fourfoldRegularizedTorusKernel_quarterTurn {ε : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1) (x : R2) :
    fourfoldRegularizedTorusKernel ε hε (torusQuarterTurn x) =
      perpJ (fourfoldRegularizedTorusKernel ε hε x) := by
  have htest := fourfoldTorusKernelMollifier_test hε hε1
  obtain ⟨C, hC⟩ := bound_on_box htest.1.continuous
  apply torusKernelVelocity_quarterTurn_of_invariant htest.1.continuous.aestronglyMeasurable
    (M := C) ?_ htest.2 (fourfoldTorusKernelMollifier_quarterTurn ε hε) x
  filter_upwards [ae_restrict_mem measurableSet_torusBox] with y hy
  simpa only [Real.norm_eq_abs] using hC y hy

end Euler2D

end
