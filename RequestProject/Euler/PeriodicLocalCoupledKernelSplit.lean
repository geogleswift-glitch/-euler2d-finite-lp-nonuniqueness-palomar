module

public import RequestProject.Euler.TorusCoupledKernelSplit

/-! The singular periodic local part is retained separately for
comparison under the same genuine smooth correction field. -/

@[expose] public section

set_option maxHeartbeats 2000000

noncomputable section

open MeasureTheory Set Filter Topology Metric Real

namespace Euler2D

theorem periodic_local_kernel_diff_split_bounded {C h : ℝ} (hC : 0 ≤ C)
    (hderiv : ∀ z : R2, z ≠ 0 → ‖fderiv ℝ localPlanarKernel z‖ ≤ C * (‖z‖ ^ 2)⁻¹)
    (hh : 0 < h) (hh1 : h ≤ 1 / 4) {a b : R2} (hab : ‖a - b‖ ≤ h) :
    ‖periodicLocalKernel a - periodicLocalKernel b‖ ≤
      (periodicCenteredSource (coupledNearProfile (2 * h)) a +
        periodicCenteredSource (coupledNearProfile (3 * h)) b) / (2 * Real.pi) +
      (4 * C * h) * periodicCenteredSource (coupledAnnularProfile h) a + 4 * C * h := by
  have hsmall : ‖b - a‖ ≤ 1 / 2 := by rw [norm_sub_rev]; linarith
  let u := torusWrap a - torusCenter
  let v := torusWrap a + (b - a) - torusCenter
  have huv : ‖u - v‖ ≤ h := by
    have he : u - v = a - b := by dsimp only [u, v]; abel
    rw [he]; exact hab
  have hlocal := local_kernel_diff_split_bounded hC hderiv hh huv
  have hpa : periodicLocalKernel a = localPlanarKernel u := by
    rw [← isTorusPeriodic_periodicLocalKernel.eq_torusWrap a]
    exact periodicLocalKernel_eq_on_box (torusRep_mem _)
  have hpb : periodicLocalKernel b = localPlanarKernel v := periodicLocalKernel_common_chart a b hsmall
  have hn1 : periodicCenteredSource (coupledNearProfile (2 * h)) a = coupledNearProfile (2 * h) u :=
    periodicCenteredSource_eq_wrapped (coupledNearProfile_zero_of_one_le (by linarith)) a
  have hn2 : periodicCenteredSource (coupledNearProfile (3 * h)) b = coupledNearProfile (3 * h) v :=
    periodicCenteredSource_common_chart (coupledNearProfile_zero_of_one_le (by linarith)) a b hsmall
  have ha1 : periodicCenteredSource (coupledAnnularProfile h) a = coupledAnnularProfile h u :=
    periodicCenteredSource_eq_wrapped (coupledAnnularProfile_zero_of_one_le h) a
  rw [hpa, hpb, hn1, hn2, ha1]
  exact hlocal

end Euler2D

end
