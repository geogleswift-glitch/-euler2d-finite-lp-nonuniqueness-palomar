module

public import RequestProject.Euler.AnnularDepartureTest
public import RequestProject.Euler.DepartureTest

/-!
# The physical fourth moment forces positive velocity departure

This connects the constructed periodic annular test, exact physical
moment pairing and original distributional curl to the L² departure
used in the limit proposition.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ContDiff symmDiff

namespace Euler2D

theorem velocity_departure_of_annular_geometry
    {η R A δJ : ℝ} (hη : 0 < η) (hηmax : η < 1 / 5)
    (hR : 0 < R) (hR1 : R ≤ 1) (hA : 0 < A) (hδJ : 0 < δJ)
    {u v : L2T} {w z : Lp ℝ 2 μT} (hc : IsCurl u w) (hd : IsCurl v z)
    {D E : Set ℂ} {desc : R2 → ℝ} (hD : MeasurableSet D)
    (hinner : ∀ y ∈ D ∆ Metric.ball 0 cellA, |‖y‖ ^ 2 - 3 / 5| ≤ η)
    (houter : ∀ y ∈ E ∆ Metric.ball 0 1, 2 * η ≤ |‖y‖ ^ 2 - 3 / 5|)
    (hdesc : ∀ x ∈ torusBox, desc x ≠ 0 → 2 * η ≤ |normalizedRadiusSq R x - 3 / 5|)
    (hdifference : (w - z : Lp ℝ 2 μT) =ᵐ[μT] physicalAnnularDifference A R D E desc)
    (hmoment : δJ ≤ ‖momentJ D 4‖) :
    0 < complexCurlTestBound (contDiff_annularDepartureTest hη hηmax hR hR1) ∧
      (5 / 2 * A * R ^ 2 * δJ) /
        complexCurlTestBound (contDiff_annularDepartureTest hη hηmax hR hR1) ≤ ‖u - v‖ := by
  have hpair : ‖∫ x in torusBox, ((w - z) x : ℂ) * annularDepartureTest η hη R x‖ =
      (5 / 2 * A * R ^ 2) * ‖momentJ D 4‖ := by
    rw [← norm_integral_annularDepartureTest_physical_difference hη hηmax hR hR1 hA.le
      hD hinner houter hdesc]
    congr 1
    apply integral_congr_ae
    filter_upwards [hdifference] with x hx
    rw [hx, mul_comm]
  apply velocity_departure_of_complex_curl_test hc hd
    (contDiff_annularDepartureTest hη hηmax hR hR1)
    (isTorusPeriodic_annularDepartureTest η hη R) (by positivity)
  rw [hpair]
  exact mul_le_mul_of_nonneg_left hmoment (by positivity)

end Euler2D

end
